/-
# Dregg2.Circuit.Spec.authorityrevocation — INDEPENDENT full-state spec + executor⟺spec for the
  dregg2 effect FAMILY `authority-revocation` (`revoke` · `dropRefA` · `revokeDelegationA`).

This is a LEAF module copying the REFERENCE pattern in `Dregg2/Circuit/Transfer.lean`
(`TransferSpec` + `recKExec_iff_spec` + `recTransfer_correct`), specialised to the three
authority-revocation arms of the FULL op-set executor `execFullA` (`TurnExecutorFull.lean:3479`):

    execFullA s (.revoke           holder t) = some (recCRevoke s holder t)
    execFullA s (.dropRefA         holder t) = some (recCRevoke s holder t)
    execFullA s (.revokeDelegationA holder t) = some (recCRevoke s holder t)

All three route to the SAME chained kernel mutator `recCRevoke` (`TurnExecutorFull.lean:248`):

    recCRevoke s holder t
      = { kernel := recKRevokeTarget s.kernel holder t, log := authReceipt holder :: s.log }

with `recKRevokeTarget` (`AuthTurn.lean:108`) the cap-graph `removeEdge`:

    recKRevokeTarget k holder t
      = { k with caps := fun l => if l = holder
                                  then (k.caps l).filter (fun cap => ¬ confersEdgeTo t cap)
                                  else k.caps l }

## NO FAIL-CLOSED GUARD.

Revocation is UNCONDITIONAL — the arm is a bare `some (…)`, not a guarded `if … then some … else
none`. So unlike `Transfer` (whose `admitGuard` is a six-conjunct `if`), the admissibility guard of
this family is **`True`**: the executor commits on EVERY input. The spec records `True` as the guard
slot (keeping the reference shape) and the obligation reduces to the EXACT post-state.

## The FRAME (the whole point — every ghost enumerated).

`recCRevoke` touches exactly TWO components of the `RecChainedState`:
  * `kernel.caps`  — rewritten to the `removeEdge` filter (`holder` loses every cap conferring an
                     edge to `t`; every OTHER holder's cap-list literally unchanged).
  * `log`          — prepended with `authReceipt holder` (the chain advances by exactly one row).

EVERYTHING else is unchanged. The spec FRAME therefore literally pins, on `s'.kernel`, all SIXTEEN
non-`caps` `RecordKernelState` fields — `accounts` `cell` `escrows` `nullifiers` `revoked`
`commitments` `bal` `queues` `swiss` `slotCaveats` `factories` `lifecycle` `deathCert` `delegate`
`delegations` `sealedBoxes` — written WITHOUT reference to any executor helper. Missing ANY field
reintroduces a ghost (a field the executor could silently mutate undetected), so all sixteen are
enumerated. The `caps` post-state is pinned to an INDEPENDENT declarative `removeEdgeCaps` (defined
here, NOT `recKRevokeTarget`), validated against the executor's helper by `recKRevokeTarget_correct`.

## The deliverables (mirroring Transfer).

  1. `RevokeSpec st t st'` : `Prop` — the INDEPENDENT declarative full-state spec (guard `True` ∧ the
     exact `caps`+`log` post ∧ the 16-field kernel FRAME). One spec drives all three variants
     because their executor arms are definitionally equal.
  2. `execFullA_revoke_iff_spec` / `execFullA_dropRef_iff_spec` /
     `execFullA_revokeDelegation_iff_spec` — `execFullA st (.<variant> …) = some st' ↔ RevokeSpec …`
     (BOTH directions). The `→` validates the executor against the independent spec; a silently-
     mutated field would make it FAIL.
  3. `recKRevokeTarget_correct` — the post-`caps` helper validated DECLARATIVELY (holder filtered,
     others untouched), the analogue of `recTransfer_correct`.
  4. `removeEdgeCaps_correct` — the declarative `removeEdge` meets the executor's `recKRevokeTarget`.

## Non-vacuity (the spec is a genuine `removeEdge`, not a rubber stamp).

  * `revoke_drops_holder_edges` — after a revoke, `holder` confers NO edge to `t` (the edge is gone).
  * `revoke_preserves_other_holders` — any holder `≠ holder` keeps its cap-list verbatim.
  * `revoke_preserves_balances` — `recTotal` (and `accounts`/`cell`) unchanged — the dual frame.
-/
import Dregg2.Exec.TurnExecutorFull

namespace Dregg2.Circuit.Spec.AuthorityRevocation

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Authority (Caps Cap Auth)

/-! ## §1 — The INDEPENDENT declarative post-state of the `caps` table.

`removeEdgeCaps caps holder t` is the cap-graph `removeEdge` written WITHOUT reference to the
executor's `recKRevokeTarget`: at `holder`, keep only caps that do NOT confer an edge to `t`; every
other holder's cap-list is verbatim. This is the apex reference for the `caps` post-state; the
executor's helper is then proved equal to it (`removeEdgeCaps_correct`). -/

/-- **`removeEdgeCaps`** — the declarative cap-graph after `holder` revokes its edge(s) to `t`:
`holder`'s cap-list loses every cap conferring an edge to `t`; all other holders unchanged. -/
def removeEdgeCaps (caps : Caps) (holder t : CellId) : Caps :=
  fun l => if l = holder then (caps l).filter (fun cap => ¬ confersEdgeTo t cap) else caps l

/-- **`removeEdgeCaps_correct`** — the declarative `removeEdge` is EXACTLY the executor's
`recKRevokeTarget` post-`caps`. So pinning the spec's `caps` clause to `removeEdgeCaps`
encodes the executor's revocation, while being written independently of it. -/
theorem removeEdgeCaps_correct (k : RecordKernelState) (holder t : CellId) :
    (recKRevokeTarget k holder t).caps = removeEdgeCaps k.caps holder t := by
  rfl

/-- **`recKRevokeTarget_correct`** — the cap-update helper validated DECLARATIVELY (not trusted):
the revoked `holder` confers no edge to `t` after the filter, and every OTHER holder's cap-list is
untouched. The analogue of `recTransfer_correct`. -/
theorem recKRevokeTarget_correct (caps : Caps) (holder t : CellId) :
    (∀ cap ∈ removeEdgeCaps caps holder t holder, ¬ confersEdgeTo t cap = true)
    ∧ (∀ l, l ≠ holder → removeEdgeCaps caps holder t l = caps l) := by
  refine ⟨?_, ?_⟩
  · intro cap hcap
    have hcap' : cap ∈ (caps holder).filter (fun cap => ¬ confersEdgeTo t cap) := by
      simpa only [removeEdgeCaps, if_pos (rfl : holder = holder), if_true] using hcap
    have := (List.mem_filter.mp hcap').2
    simpa only [decide_eq_true_eq] using this
  · intro l hl
    simp only [removeEdgeCaps, if_neg hl]

/-! ## §2 — FULL-STATE SEMANTIC SPEC (the INDEPENDENT reference) + executor⟺spec.

`RevokeSpec st t st'` is the COMPLETE declarative post-state of a committed authority-revocation,
written INDEPENDENTLY of the executor (no `recCRevoke`/`recKRevokeTarget` term in any frame clause):

  * guard `True` — revocation is UNCONDITIONAL (the executor arm is a bare `some`, no fail-closed
    `if`). Recorded to keep the reference `admitGuard ∧ …` shape; here it is trivially satisfied.
  * `kernel.caps` = `removeEdgeCaps` — the declarative `removeEdge` (validated by §1).
  * `log` = `authReceipt holder :: st.log` — the receipt chain advances by exactly one row.
  * the SIXTEEN non-`caps` `RecordKernelState` fields, all LITERALLY unchanged (the FRAME). -/

/-- **The full-state declarative spec of a committed authority-revocation** — the INDEPENDENT
reference semantics over `RecChainedState`. Holds `True` (unconditional); the post-`caps` is the
declarative `removeEdge`; the log advances by `authReceipt holder`; and every one of the 16
non-`caps` kernel fields is unchanged. No frame clause mentions the executor. -/
def RevokeSpec (st : RecChainedState) (holder t : CellId) (st' : RecChainedState) : Prop :=
  True
  ∧ st'.kernel.caps = removeEdgeCaps st.kernel.caps holder t
  ∧ st'.log = authReceipt holder :: st.log
  ∧ st'.kernel.accounts = st.kernel.accounts
  ∧ st'.kernel.cell = st.kernel.cell
  ∧ st'.kernel.nullifiers = st.kernel.nullifiers
  ∧ st'.kernel.revoked = st.kernel.revoked
  ∧ st'.kernel.commitments = st.kernel.commitments
  ∧ st'.kernel.bal = st.kernel.bal
  ∧ st'.kernel.slotCaveats = st.kernel.slotCaveats
  ∧ st'.kernel.factories = st.kernel.factories
  ∧ st'.kernel.lifecycle = st.kernel.lifecycle
  ∧ st'.kernel.deathCert = st.kernel.deathCert
  ∧ st'.kernel.delegate = st.kernel.delegate
  ∧ st'.kernel.delegations = st.kernel.delegations
  ∧ st'.kernel.delegationEpoch = st.kernel.delegationEpoch
  ∧ st'.kernel.delegationEpochAt = st.kernel.delegationEpochAt
  ∧ st'.kernel.heaps = st.kernel.heaps
  ∧ st'.kernel.nullifierRoot = st.kernel.nullifierRoot
  ∧ st'.kernel.revokedRoot = st.kernel.revokedRoot
  ∧ st'.kernel.commitmentsRoot = st.kernel.commitmentsRoot

/-! ## §3 — The executor ⟺ spec equivalence, shared core then per-variant. -/

/-- **The shared core: `recCRevoke` ⟺ `RevokeSpec` (FULL state, both directions).** The chained
revoke mutator commits into `st'` IFF `st'` is EXACTLY the spec'd full post-state. The `→` direction
VALIDATES `recCRevoke` against the independent spec — all 18 RecChainedState components (16 framed
kernel fields + the `caps` post + the `log` post) are checked, so had the mutator silently touched
`bal`/`nullifiers`/`revoked`/… the frame clauses would make this proof FAIL; the `←` reconstructs
the committed state from the spec. -/
theorem recCRevoke_iff_spec (st : RecChainedState) (holder t : CellId) (st' : RecChainedState) :
    recCRevoke st holder t = st' ↔ RevokeSpec st holder t st' := by
  unfold RevokeSpec
  constructor
  · intro h; subst h
    refine ⟨trivial, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl, rfl, rfl⟩
    exact removeEdgeCaps_correct st.kernel holder t
  · rintro ⟨_, hcaps, hlog, hacc, hcell, hnull, hrev, hcom, hbal, hsc, hfac, hlif,
           hdc, hdel, hdels, hde, hdea, hhp, hnr, hrr, hcr⟩
    -- `st'` is the spec'd full post-state: rebuild the committed `RecChainedState` field-by-field.
    -- The `caps` post (`removeEdgeCaps`) is the executor's `recKRevokeTarget` post (§1), so
    -- `recCRevoke st holder t` has EXACTLY `st'`'s fields. Destructure `st'` so each spec field hyp
    -- has a fresh field VAR to `subst`.
    obtain ⟨k', log'⟩ := st'
    obtain ⟨acc', cell', caps', null', rev', com', bal', sc', fac', lif', dc', del',
            dels', de', dea', hp', nr', rr', cr'⟩ := k'
    rw [← removeEdgeCaps_correct st.kernel holder t] at hcaps
    subst hacc hcell hcaps hnull hrev hcom hbal hsc hfac hlif hdc hdel hdels hlog
      hde hdea hhp hnr hrr hcr
    rfl

/-- **`execFullA_revoke_iff_spec` — EXECUTOR ⟺ SPEC for the `revoke` arm (FULL state, both
directions).** `execFullA st (.revoke holder t) = some st'` IFF `st'` is exactly the spec'd full
post-state. The `→` validates the `revoke` executor arm against the independent spec. -/
theorem execFullA_revoke_iff_spec (st : RecChainedState) (holder t : CellId)
    (st' : RecChainedState) :
    execFullA st (.revoke holder t) = some st' ↔ RevokeSpec st holder t st' := by
  rw [show execFullA st (.revoke holder t) = some (recCRevoke st holder t) from rfl,
      Option.some.injEq]
  exact recCRevoke_iff_spec st holder t st'

/-! ## §2.EPOCH — the STRENGTHENED full-state spec for `revokeDelegationA` (the faithful epoch step).

`.revokeDelegationA holder t` does NOT route to the bare `recCRevoke` (cap-edge removal only). It routes
to `recCRevokeDelegationFull` (`TurnExecutorFull.lean`), the committed form of `recKRevokeDelegationFull`
(`AuthTurn.lean`) — the FAITHFUL `apply_revoke_delegation`: the shared cap-edge `removeEdge` (leg 1)
COMPOSED with the epoch bump + child-snapshot clear (legs 2+3). So the spec it meets is STRICTLY STRONGER
than `RevokeSpec`: the same `caps` removeEdge + log advance + thirteen-field frame, but instead of FRAMING
`delegationEpoch`/`delegations`/`delegationEpochAt` UNCHANGED, it ASSERTS the epoch step — the parent's
epoch bumped `+1`, the child's snapshot cleared (`[]`) and its stamp reset to `0`. The light-client
freshness consequence (`delegationStale child = true`) is the keystone `recKRevokeDelegationFull_makes_child_stale`. -/

/-- **`RevokeDelegationFullSpec st parent child st'`** — the STRENGTHENED full-state spec of the FAITHFUL
delegation revoke. Identical to `RevokeSpec` on the shared cap-edge `removeEdge`, the receipt-log advance,
and the THIRTEEN balance/account/note/lifecycle frame fields — but the three delegation registries are no
longer FRAMED unchanged; they carry the dregg1 epoch step: the PARENT's `delegationEpoch` bumped `+1`, the
CHILD's `delegations` snapshot cleared, its `delegationEpochAt` stamp reset to `0`. A forge that removes
the cap edge WITHOUT performing the epoch step FAILS these clauses. -/
def RevokeDelegationFullSpec (st : RecChainedState) (parent child : CellId)
    (st' : RecChainedState) : Prop :=
  True
  ∧ st'.kernel.caps = removeEdgeCaps st.kernel.caps parent child
  ∧ st'.log = authReceipt parent :: st.log
  ∧ st'.kernel.accounts = st.kernel.accounts
  ∧ st'.kernel.cell = st.kernel.cell
  ∧ st'.kernel.nullifiers = st.kernel.nullifiers
  ∧ st'.kernel.revoked = st.kernel.revoked
  ∧ st'.kernel.commitments = st.kernel.commitments
  ∧ st'.kernel.bal = st.kernel.bal
  ∧ st'.kernel.slotCaveats = st.kernel.slotCaveats
  ∧ st'.kernel.factories = st.kernel.factories
  ∧ st'.kernel.lifecycle = st.kernel.lifecycle
  ∧ st'.kernel.deathCert = st.kernel.deathCert
  ∧ st'.kernel.delegate = st.kernel.delegate
  ∧ st'.kernel.heaps = st.kernel.heaps
  ∧ st'.kernel.nullifierRoot = st.kernel.nullifierRoot
  ∧ st'.kernel.revokedRoot = st.kernel.revokedRoot
  ∧ st'.kernel.commitmentsRoot = st.kernel.commitmentsRoot
  -- THE EPOCH STEP (legs 2+3), no longer framed-unchanged:
  ∧ st'.kernel.delegationEpoch
      = (fun c => if c = parent then st.kernel.delegationEpoch c + 1 else st.kernel.delegationEpoch c)
  ∧ st'.kernel.delegations
      = (fun c => if c = child then [] else st.kernel.delegations c)
  ∧ st'.kernel.delegationEpochAt
      = (fun c => if c = child then 0 else st.kernel.delegationEpochAt c)

/-- **The strengthened core: `recCRevokeDelegationFull` ⟺ `RevokeDelegationFullSpec` (FULL state, both
directions).** The faithful chained delegation-revoke commits into `st'` IFF `st'` is EXACTLY the
strengthened spec'd post-state. The `→` validates the FULL step against the independent spec — the
thirteen frame fields PLUS the three epoch-step clauses are all checked, so a mutator that dropped the
edge but skipped the epoch bump / snapshot clear would make this FAIL. -/
theorem recCRevokeDelegationFull_iff_spec (st : RecChainedState) (parent child : CellId)
    (st' : RecChainedState) :
    recCRevokeDelegationFull st parent child = st' ↔ RevokeDelegationFullSpec st parent child st' := by
  unfold RevokeDelegationFullSpec recCRevokeDelegationFull recKRevokeDelegationFull
    recKRevokeDelegationEpoch
  constructor
  · intro h; subst h
    refine ⟨trivial, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
            rfl, rfl, rfl, rfl, rfl, rfl⟩
    -- the `caps` post is the shared `recKRevokeTarget` post = `removeEdgeCaps` (the epoch legs touch
    -- no `caps`, so `recKRevokeDelegationFull_caps` carries the §1 equality verbatim).
    exact removeEdgeCaps_correct st.kernel parent child
  · rintro ⟨_, hcaps, hlog, hacc, hcell, hnull, hrev, hcom, hbal, hsc, hfac, hlif,
           hdc, hdel, hhp, hnr, hrr, hde, hdels, hdea, hcr⟩
    obtain ⟨k', log'⟩ := st'
    obtain ⟨acc', cell', caps', null', rev', com', bal', sc', fac', lif', dc', del',
            dels', de', dea', hp', nr', rr', cr'⟩ := k'
    rw [← removeEdgeCaps_correct st.kernel parent child] at hcaps
    subst hacc hcell hcaps hnull hrev hcom hbal hsc hfac hlif hdc hdel hhp hnr hrr hde hdels hdea hcr
      hlog
    rfl

/-- **`execFullA_revokeDelegation_iff_spec` — EXECUTOR ⟺ STRENGTHENED SPEC for the `revokeDelegationA`
arm (FULL state, both directions).** `execFullA st (.revokeDelegationA parent child) = some st'` IFF
`st'` is exactly the FAITHFUL epoch-step post-state. The arm routes to `recCRevokeDelegationFull` (NOT
the bare `recCRevoke`), so the iff is the STRONGER `RevokeDelegationFullSpec` — it asserts the parent
epoch bump + child snapshot clear, not merely the cap-edge removal. -/
theorem execFullA_revokeDelegation_iff_spec (st : RecChainedState) (parent child : CellId)
    (st' : RecChainedState) :
    execFullA st (.revokeDelegationA parent child) = some st'
      ↔ RevokeDelegationFullSpec st parent child st' := by
  rw [show execFullA st (.revokeDelegationA parent child)
        = some (recCRevokeDelegationFull st parent child) from rfl,
      Option.some.injEq]
  exact recCRevokeDelegationFull_iff_spec st parent child st'

/-! ## §2.EPOCH-NV — the strengthened spec is NON-VACUOUS: the child genuinely STALES.

The whole point of the strengthening: a forge that drops the edge but does NOT bump the epoch is REJECTED.
We exhibit the freshness consequence DIRECTLY off the spec — after the faithful revoke, IF the child's
parent pointer still points at `parent`, its snapshot is STALE. -/

/-- **`revokeDelegationFull_stales_child` — THE FRESHNESS TOOTH, read off the spec.** From the
strengthened spec, the child's stamp is reset to `0` while the parent's epoch is bumped to
`delegationEpoch parent + 1 > 0`; so if the child still points at `parent`, `delegationStale child = true`
in the post-state. A light client REJECTS the revoked delegation — it cannot be replayed. The forge that
skips the epoch bump cannot satisfy the spec (its `delegationEpoch parent` would be unchanged, failing the
epoch-step clause), so it is unreachable. -/
theorem revokeDelegationFull_stales_child (st : RecChainedState) (parent child : CellId)
    (st' : RecChainedState) (h : RevokeDelegationFullSpec st parent child st')
    (hpoint : st'.kernel.delegate child = some parent) :
    delegationStale st'.kernel child = true := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hde, _, hdea⟩ := h
  have hstamp : st'.kernel.delegationEpochAt child = 0 := by
    have := congrFun hdea child; simpa using this
  have hpar : st'.kernel.delegationEpoch parent = st.kernel.delegationEpoch parent + 1 := by
    have := congrFun hde parent; simpa using this
  unfold delegationStale
  rw [hpoint]
  simp only [hstamp, hpar]
  exact decide_eq_true (by omega)

/-! ## §4 — Non-vacuity: the spec is a GENUINE `removeEdge`, not a rubber stamp.

A spec that left `caps` untouched would be worthless. Here we EXHIBIT that the spec's `caps` clause
tears the edge down (`holder` confers no edge to `t` afterward), preserves every other
holder, and — the dual frame — leaves all balances untouched. -/

/-- **`revoke_drops_holder_edges`.** After a committed revoke, the `holder` confers NO edge
to `t`: every cap it still holds fails `confersEdgeTo t`. The edge is gone. -/
theorem revoke_drops_holder_edges (st : RecChainedState) (holder t : CellId)
    (st' : RecChainedState) (h : RevokeSpec st holder t st') :
    ∀ cap ∈ st'.kernel.caps holder, ¬ confersEdgeTo t cap = true := by
  obtain ⟨_, hcaps, _⟩ := h
  rw [hcaps]
  exact (recKRevokeTarget_correct st.kernel.caps holder t).1

/-- **`revoke_preserves_other_holders`.** Any holder `l ≠ holder` keeps its cap-list
verbatim across the revoke — authority only SHRINKS at the targeted holder. -/
theorem revoke_preserves_other_holders (st : RecChainedState) (holder t : CellId)
    (st' : RecChainedState) (h : RevokeSpec st holder t st') :
    ∀ l, l ≠ holder → st'.kernel.caps l = st.kernel.caps l := by
  obtain ⟨_, hcaps, _⟩ := h
  rw [hcaps]
  exact (recKRevokeTarget_correct st.kernel.caps holder t).2

/-- **`revoke_preserves_balances`.** The dual frame: a revocation edits only `caps`, so the
conserved `recTotal` (and `accounts`/`cell`) are unchanged. Revocation moves no value. -/
theorem revoke_preserves_balances (st : RecChainedState) (holder t : CellId)
    (st' : RecChainedState) (h : RevokeSpec st holder t st') :
    recTotal st'.kernel = recTotal st.kernel
    ∧ st'.kernel.accounts = st.kernel.accounts
    ∧ st'.kernel.cell = st.kernel.cell := by
  obtain ⟨_, _, _, hacc, hcell, _⟩ := h
  refine ⟨?_, hacc, hcell⟩
  unfold recTotal
  rw [hacc, hcell]

/-- **`revoke_log_advances`.** The receipt chain advances by EXACTLY one `authReceipt`
row (the chain grows by one; the dual of `Transfer`'s ChainLink). -/
theorem revoke_log_advances (st : RecChainedState) (holder t : CellId)
    (st' : RecChainedState) (h : RevokeSpec st holder t st') :
    st'.log = authReceipt holder :: st.log ∧ st'.log.length = st.log.length + 1 := by
  obtain ⟨_, _, hlog, _⟩ := h
  exact ⟨hlog, by rw [hlog]; rfl⟩

/-! ## §5 — Concrete witnesses (a revoke is decidably the `removeEdge`). -/

/-- A concrete pre-state: holder `0` holds one cap `Cap.node 7` (toy), nobody else holds anything. -/
def kR0 : RecordKernelState :=
  { accounts := {0, 1}
    cell := fun _ => .record [("balance", .int 0)]
    caps := fun l => if l = 0 then [Cap.node 7] else [] }

-- The revoke executor always commits (unconditional — no fail-closed guard):
#guard (execFullA { kernel := kR0, log := [] } (.revoke 0 7)).isSome  -- true
#guard (execFullA { kernel := kR0, log := [] } (.revokeDelegationA 0 7)).isSome  -- true

/-! ## §6 — Axiom-hygiene tripwires.

Whitelist exactly `{propext, Classical.choice, Quot.sound}`. -/

#assert_axioms removeEdgeCaps_correct
#assert_axioms recKRevokeTarget_correct
#assert_axioms recCRevoke_iff_spec
#assert_axioms execFullA_revoke_iff_spec
#assert_axioms recCRevokeDelegationFull_iff_spec
#assert_axioms execFullA_revokeDelegation_iff_spec
#assert_axioms revokeDelegationFull_stales_child
#assert_axioms revoke_drops_holder_edges
#assert_axioms revoke_preserves_other_holders
#assert_axioms revoke_preserves_balances
#assert_axioms revoke_log_advances

end Dregg2.Circuit.Spec.AuthorityRevocation
