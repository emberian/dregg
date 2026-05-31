/-
# Dregg2.Exec.EffectsPaired — the CONSERVATIVE / PAIRED-regime dregg1 effects (Σδ = 0).

**Instantiates the `Exec/EffectTransfer.lean` REFERENCE TEMPLATE for the rest of the
`LinearityClass.Conservative` catalog cluster** — every dregg1 effect whose `effectLinearity`
color is `Conservative` (`CatalogInstances.effectLinearity`), EXCLUDING `transfer` (done in
`EffectTransfer`) and the supply pair `mint`/`burn` (done, as `Generative`/`Annihilative`, in
`TurnExecutorFull`/`TriDomain`). From `effectLinearity`'s `Conservative` arm these are:

  * **Escrow** — `createEscrow`, `releaseEscrow`, `refundEscrow`, and the committed (privacy)
    triple `createCommittedEscrow`, `releaseCommittedEscrow`, `refundCommittedEscrow`.
  * **Notes** (the §8-PORTAL cluster) — `noteSpend`, `noteCreate`.
  * **Obligations** — `createObligation`, `fulfillObligation`, `slashObligation`.
  * **Queues** — `queueEnqueue`, `queueDequeue`, `queueAtomicTx`, `queuePipelineStep`.
  * **Bridge** (the Σδ = 0 phases) — `bridgeLock`, `bridgeFinalize`, `bridgeCancel`.

## The five-keystone pattern (per effect), per `EffectTransfer`
Each effect copies `EffectTransfer`'s skeleton: an executable `*Step` over the chained record
kernel; a two-party `*_conserves` (`recTotal` unchanged, Σδ = 0); an `*_authorized` (the
`recCexec` gate); a `*_metadata` (the per-effect named-field move + caps unchanged); and a
`*_forward_sim` (the `AbsStep` of `EffectTransfer §5`, instantiated here).

### What is REUSABLE VERBATIM (the mechanical majority)
The *single insight* that lets the whole cluster reuse `EffectTransfer`: **every Conservative
effect is, at the state-transition level, a balance DEBIT at one cell + a balance CREDIT at
another (Σδ = 0), optionally riding alongside a metadata-domain field write** (a status flag, a
nullifier-set membership bit, a lock/unlock marker). The debit/credit pair is *exactly*
`recCexec` (the same gated two-party move `transferStep` runs); so:
  * the conservation core (`recTotal` preserved, two-party cancellation) comes VERBATIM from
    `recCexec_attests.1` / `recCexec`'s `recKExec_conserves`;
  * the authority gate (`authorizedB`) comes VERBATIM from `recCexec_attests.2.1`;
  * the caps-frame / authority-graph-unchanged comes VERBATIM from `recCexec`'s
    `recKExec_frame` (these effects never edit `caps`);
  * the forward-sim `AbsStep` (conservation projection + authority `Guard` + graph preservation)
    is the SAME `Spec.conservedInDomain` / `Spec.execAuthGuard` / `Spec.execGraph` instantiation
    `EffectTransfer §5` uses.

### What is BESPOKE (the only new lemma per effect)
The per-effect METADATA move and its `balOf`-NON-INTERFERENCE: which named field the effect writes
in its metadata domain and a proof that the write leaves the conserved `balance` measure untouched
(the `setNonce_balOf` analog). We factor this ONCE as a generic named-field write `setField'` +
its non-interference `setField'_balOf` (a `field ≠ "balance"` write never perturbs `balOf`), so
each effect names only its field constant (`"status"`, `"spent"`, `"locked"`, …) and inherits the
non-interference. This is the EffectTransfer "one metadata lemma per effect", shared across the
cluster by abstraction over the field name.

## §8-PORTAL discipline (the note cluster)
For `noteSpend`/`noteCreate` the *cryptography* (the STARK spending proof, the range proof, the
nullifier derivation) is a `Prop`-carrier PORTAL/HYPOTHESIS — `noteSpend`'s `spending_proof` and
`noteCreate`'s `range_proof` are modelled as an opaque `CryptoOK : Prop` carried as a hypothesis,
NOT executed in Lean (consistent with dregg2's §8 boundary, exactly as the `Crypto/*` modules do).
What we PROVE is about the STATE TRANSITION: the balance debit/credit and the nullifier-set insert.
The crypto soundness is *assumed* (carried); the conservation/authority/metadata facts are
genuinely proved over the state move. A note spend that does not carry `CryptoOK` does not commit
(fail-closed on the portal), and one that does commits as a balance debit + a nullifier-set insert.

## Discipline
No `sorry`/`admit`/`axiom`/`native_decide`. `#assert_axioms` whitelists exactly `{propext,
Classical.choice, Quot.sound}` on every keystone. Self-contained: reuses ONLY the already-built
`Exec.TurnExecutor` / `Exec.RecordKernel` / `Spec.ExecRefinement` primitives (same imports as
`EffectTransfer`). Verified standalone: `lake env lean Dregg2/Exec/EffectsPaired.lean`.
-/
import Dregg2.Exec.TurnExecutor
import Dregg2.Spec.ExecRefinement

namespace Dregg2.Exec.EffectsPaired

open Dregg2.Exec
open Dregg2.Authority (Caps)
open Dregg2.Spec (Domain conservedInDomain execGraph execAuthGuard Guard)
open Dregg2.Laws (Verifiable)
open scoped BigOperators

/-! ## §0 — The shared BESPOKE machinery: a generic metadata-domain named-field write.

`EffectTransfer` writes the `nonce` field and proves `setNonce_balOf` (non-interference with the
conserved `balance` measure). Every Conservative effect here writes SOME metadata field (a status
marker, a nullifier-set membership bit, a lock flag); the proof that this leaves `balOf` untouched
is identical up to the field name. We factor it ONCE as `setField'` + `setField'_balOf` (a write to
ANY field `≠ "balance"` preserves `balOf`), so each effect names only its field constant. This is
the EffectTransfer "one metadata lemma per effect", shared by abstraction over the field name. -/

/-- Set a named `field` of a record cell to the int `n` (overwriting in place; a non-record value
becomes a singleton record). The generic metadata write the whole cluster's metadata moves use —
it touches ONLY `field`. The field-parametric analog of `RecordKernel.setBalance` / `setNonce`. -/
def setField' (field : FieldName) (cell : Value) (n : Int) : Value :=
  match cell with
  | .record fs => .record (setFieldList fs n)
  | _          => .record [(field, .int n)]
where
  setFieldList : List (FieldName × Value) → Int → List (FieldName × Value)
  | [],            n => [(field, .int n)]
  | (k, x) :: rest, n => if k == field then (field, .int n) :: rest
                         else (k, x) :: setFieldList rest n

/-- After `setField' field cell n`, reading `field` returns exactly `n` (the write/read law for the
metadata measure — the field-parametric analog of `setNonce_nonceOf`). -/
theorem setField'_read (field : FieldName) (cell : Value) (n : Int) :
    (setField' field cell n).scalar field = some n := by
  have hlist : ∀ fs : List (FieldName × Value),
      ((Value.record (setField'.setFieldList field fs n)).scalar field) = some n := by
    intro fs
    induction fs with
    | nil => simp [setField'.setFieldList, Value.scalar, Value.field]
    | cons hd tl ih =>
        obtain ⟨k, x⟩ := hd
        simp only [setField'.setFieldList]
        by_cases hk : (k == field) = true
        · rw [if_pos hk]; simp [Value.scalar, Value.field]
        · have hkf : (k == field) = false := by simpa using hk
          rw [if_neg hk]
          simp only [Value.scalar, Value.field] at ih ⊢
          rw [List.find?_cons_of_neg (by simpa using hkf)]
          exact ih
  cases cell with
  | record fs => simpa [setField'] using hlist fs
  | int _  => simp [setField', Value.scalar, Value.field]
  | dig _  => simp [setField', Value.scalar, Value.field]
  | sym _  => simp [setField', Value.scalar, Value.field]

/-- **NON-INTERFERENCE — PROVED (the shared bespoke lemma).** Writing ANY metadata field
`field ≠ "balance"` leaves the conserved balance read (`balOf`) UNCHANGED. The generalization of
`EffectTransfer.setNonce_balOf` over the field name: each effect's metadata move (status / nullifier
bit / lock flag) rides alongside the two-party balance conservation without disturbing it, as long as
its field is not the `balance` field — which all metadata fields are, by construction. -/
theorem setField'_balOf (field : FieldName) (hne : field ≠ balanceField) (cell : Value) (n : Int) :
    balOf (setField' field cell n) = balOf cell := by
  have hbf : (field == balanceField) = false := by
    simpa using hne
  have hlist : ∀ fs : List (FieldName × Value),
      ((Value.record (setField'.setFieldList field fs n)).scalar balanceField)
        = ((Value.record fs).scalar balanceField) := by
    intro fs
    induction fs with
    | nil =>
        simp only [setField'.setFieldList, Value.scalar, Value.field]
        rw [List.find?_cons_of_neg (by simpa using hbf)]
    | cons hd tl ih =>
        obtain ⟨k, x⟩ := hd
        simp only [setField'.setFieldList]
        by_cases hk : (k == field) = true
        · rw [if_pos hk]
          have hkn : k = field := by simpa using hk
          have hkb : (k == balanceField) = false := by rw [hkn]; exact hbf
          simp only [Value.scalar, Value.field]
          rw [List.find?_cons_of_neg (by simpa using hbf),
              List.find?_cons_of_neg (by simpa using hkb)]
        · rw [if_neg hk]
          simp only [Value.scalar, Value.field] at ih ⊢
          by_cases hkb : (k == balanceField) = true
          · rw [List.find?_cons_of_pos (by simpa using hkb),
                List.find?_cons_of_pos (by simpa using hkb)]
          · rw [List.find?_cons_of_neg (by simpa using hkb),
                List.find?_cons_of_neg (by simpa using hkb)]
            exact ih
  have hsingle : ((Value.record [(field, Value.int n)]).scalar balanceField) = none := by
    simp only [Value.scalar, Value.field]
    rw [List.find?_cons_of_neg (by simpa using hbf)]
    rfl
  unfold balOf setField'
  cases cell with
  | record fs => rw [hlist fs]
  | int _  => rw [hsingle]; rfl
  | dig _  => rw [hsingle]; rfl
  | sym _  => rw [hsingle]; rfl

/-- Advance/set a named metadata `field` of a single cell `c` in the kernel state to `n` (the
metadata move all Conservative effects post-compose onto the `recCexec` balance pair). -/
def writeMeta (field : FieldName) (k : RecordKernelState) (c : CellId) (n : Int) :
    RecordKernelState :=
  { k with cell := fun x => if x = c then setField' field (k.cell c) n else k.cell x }

/-- `writeMeta` to any metadata field `≠ "balance"` preserves the conserved `balance` total —
PROVED, from `setField'_balOf` (the shared non-interference), summed over the live accounts. The
metadata move never perturbs the balance domain. -/
theorem writeMeta_recTotal (field : FieldName) (hne : field ≠ balanceField)
    (k : RecordKernelState) (c : CellId) (n : Int) :
    recTotal (writeMeta field k c n) = recTotal k := by
  unfold recTotal writeMeta
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : x = c
  · simp only [hx, if_pos]; exact setField'_balOf field hne (k.cell c) n
  · simp only [if_neg hx]

/-- `writeMeta` never edits the cap table (it rewrites only the `cell` records). PROVED. -/
theorem writeMeta_caps (field : FieldName) (k : RecordKernelState) (c : CellId) (n : Int) :
    (writeMeta field k c n).caps = k.caps := rfl

/-! ## §1 — The GENERIC paired step: a `recCexec` balance pair + a metadata field write.

`pairedStep field mark s actor src dst amt`: run the gated two-party balance debit/credit via
`recCexec` (the SAME gate `transferStep` runs — authority + availability + liveness + `src ≠ dst`),
THEN write the metadata `field` of the source to `meta`. This single combinator instantiates EVERY
Conservative effect's state transition: each effect picks its `field` (status / spent / locked / …)
and the `mark` value to record; the balance pair is identical (Σδ = 0). This is the reusable spine.

The PORTAL (§8): an effect whose semantics involve cryptography (note spend/create) is invoked with
a `CryptoOK : Prop` HYPOTHESIS guarding the *crypto* check; the state move modelled here is exactly
this `pairedStep` (debit/credit + set membership marker). The crypto soundness is carried, not run. -/

/-- **The generic Conservative state transition (PROVED computable).** Gated two-party balance move
(`recCexec`) followed by the metadata `field`-write on the source. Fail-closed: any gate failure
aborts. The single combinator the whole cluster instantiates. -/
@[reducible] def pairedStep (field : FieldName) (mark : Int) (s : RecChainedState)
    (actor src dst : CellId) (amt : ℤ) : Option RecChainedState :=
  match recCexec s { actor := actor, src := src, dst := dst, amt := amt } with
  | some s1 => some { s1 with kernel := writeMeta field s1.kernel src mark }
  | none    => none

/-- The `Turn` a `pairedStep` runs. -/
def pairedTurn (actor src dst : CellId) (amt : ℤ) : Turn :=
  { actor := actor, src := src, dst := dst, amt := amt }

/-- **`pairedStep` factors through its `recCexec` core — PROVED.** The bridge every downstream
theorem reuses (the `transferStep_factors` analog). -/
theorem pairedStep_factors {field : FieldName} {mark : Int} {s s' : RecChainedState}
    {actor src dst : CellId} {amt : ℤ}
    (h : pairedStep field mark s actor src dst amt = some s') :
    ∃ s1, recCexec s (pairedTurn actor src dst amt) = some s1 ∧
      s' = { s1 with kernel := writeMeta field s1.kernel src mark } := by
  unfold pairedStep pairedTurn at *
  cases hc : recCexec s { actor := actor, src := src, dst := dst, amt := amt } with
  | none => rw [hc] at h; exact absurd h (by simp)
  | some s1 =>
      rw [hc] at h; simp only [Option.some.injEq] at h
      exact ⟨s1, rfl, h.symm⟩

/-- **GENERIC TWO-PARTY CONSERVATION (PROVED).** Any committed `pairedStep` over a metadata
`field ≠ "balance"` preserves the total `balance` (Σδ = 0): the source `−amt` debit and dest `+amt`
credit cancel (`recCexec`'s `recKExec_conserves`), and the metadata write preserves `balOf`
(`writeMeta_recTotal`). The reusable conservation core every effect inherits VERBATIM. -/
theorem pairedStep_conserves {field : FieldName} (hne : field ≠ balanceField) {mark : Int}
    {s s' : RecChainedState} {actor src dst : CellId} {amt : ℤ}
    (h : pairedStep field mark s actor src dst amt = some s') :
    recTotal s'.kernel = recTotal s.kernel := by
  obtain ⟨s1, hc, hs'⟩ := pairedStep_factors h
  have hcore : recTotal s1.kernel = recTotal s.kernel := (recCexec_attests hc).1
  subst hs'
  simp only []
  rw [writeMeta_recTotal field hne s1.kernel src mark, hcore]

/-- **GENERIC PER-DOMAIN Σ = 0 (PROVED).** The realized balance-domain delta of a committed
`pairedStep` nets to `0` (`Spec.conservedInDomain Domain.balance`) — the executable shadow of
dregg1's `excess == 0` gate for every Paired effect. -/
theorem pairedStep_domain {field : FieldName} (hne : field ≠ balanceField) {mark : Int}
    {s s' : RecChainedState} {actor src dst : CellId} {amt : ℤ}
    (h : pairedStep field mark s actor src dst amt = some s') :
    conservedInDomain Domain.balance [recTotal s'.kernel - recTotal s.kernel] := by
  unfold conservedInDomain
  rw [pairedStep_conserves hne h]; simp

/-- **GENERIC AUTHORIZATION (PROVED).** A committed `pairedStep` ⇒ the source held a cap
authorizing the debit (`authorizedB` at the pre-state) — VERBATIM from `recCexec`'s authority
conjunct. The reusable authority core. -/
theorem pairedStep_authorized {field : FieldName} {mark : Int} {s s' : RecChainedState}
    {actor src dst : CellId} {amt : ℤ}
    (h : pairedStep field mark s actor src dst amt = some s') :
    authorizedB s.kernel.caps (pairedTurn actor src dst amt) = true := by
  obtain ⟨s1, hc, _⟩ := pairedStep_factors h
  exact (recCexec_attests hc).2.1

/-- **GENERIC FAIL-CLOSED (PROVED).** An unauthorized move commits no `pairedStep`. The
integrity/confinement core for every Paired effect. -/
theorem pairedStep_unauthorized_fails (field : FieldName) (mark : Int) (s : RecChainedState)
    (actor src dst : CellId) (amt : ℤ)
    (h : authorizedB s.kernel.caps (pairedTurn actor src dst amt) = false) :
    pairedStep field mark s actor src dst amt = none := by
  unfold pairedTurn at h
  unfold pairedStep
  have hnone : recCexec s { actor := actor, src := src, dst := dst, amt := amt } = none := by
    unfold recCexec
    rw [recKExec_unauthorized_fails s.kernel _ h]
  rw [hnone]

/-- `recCexec` leaves the cap table unchanged (rewrites only the `balance` field). The
`EffectTransfer.recCexec_caps_eq` analog, re-derived here for self-containment. -/
theorem recCexec_caps_eq {s s1 : RecChainedState} {t : Turn} (h : recCexec s t = some s1) :
    s1.kernel.caps = s.kernel.caps := by
  unfold recCexec at h
  cases hk : recKExec s.kernel t with
  | none => rw [hk] at h; exact absurd h (by simp)
  | some k' =>
      rw [hk] at h; simp only [Option.some.injEq] at h; subst h
      exact (recKExec_frame s.kernel k' t hk).2

/-- **GENERIC CAPS-UNCHANGED (PROVED).** A committed `pairedStep` leaves the cap table UNTOUCHED
(neither the gated debit/credit nor the metadata write edits `caps`). The reusable authority-frame. -/
theorem pairedStep_caps_unchanged {field : FieldName} {mark : Int} {s s' : RecChainedState}
    {actor src dst : CellId} {amt : ℤ}
    (h : pairedStep field mark s actor src dst amt = some s') :
    s'.kernel.caps = s.kernel.caps := by
  obtain ⟨s1, hc, hs'⟩ := pairedStep_factors h
  subst hs'
  simp only [writeMeta_caps]
  exact recCexec_caps_eq hc

/-- **GENERIC AUTHORITY-GRAPH-UNCHANGED (PROVED).** A committed `pairedStep` leaves the
reconstructed authority `Graph` (`Spec.execGraph`) UNCHANGED — Paired effects move balance/metadata,
never connectivity. The authority-domain frame the forward-sim reads. -/
theorem pairedStep_authGraph_unchanged {field : FieldName} {mark : Int} {s s' : RecChainedState}
    {actor src dst : CellId} {amt : ℤ}
    (h : pairedStep field mark s actor src dst amt = some s') :
    execGraph s'.kernel.caps = execGraph s.kernel.caps := by
  rw [pairedStep_caps_unchanged h]

/-- **GENERIC METADATA (PROVED).** A committed `pairedStep` (a) writes the source's metadata
`field` to EXACTLY `meta`, and (b) leaves the cap table UNCHANGED. The metadata + authority
obligation, parametric over the field — each effect instantiates it at its own field constant. -/
theorem pairedStep_metadata {field : FieldName} {mark : Int} {s s' : RecChainedState}
    {actor src dst : CellId} {amt : ℤ}
    (h : pairedStep field mark s actor src dst amt = some s') :
    (s'.kernel.cell src).scalar field = some mark ∧ s'.kernel.caps = s.kernel.caps := by
  obtain ⟨s1, hc, hs'⟩ := pairedStep_factors h
  refine ⟨?_, pairedStep_caps_unchanged h⟩
  subst hs'
  simp only [writeMeta, if_pos]
  exact setField'_read field (s1.kernel.cell src) mark

/-! ### §1.1 — The GENERIC forward-simulation `AbsStep` (the `EffectTransfer §5` square).

The record-world abstract `Spec` state + the `AbsStep` transition relation, VERBATIM from
`EffectTransfer §5`. Every Conservative effect's forward-sim is `pairedStep_forward_sim`
instantiated at its field — so the whole cluster's forward-sim is ONE proof. -/

section ForwardSim
variable {Statement Witness : Type} [Verifiable Statement Witness]

/-- The record-world abstract Spec state a Paired effect refines (the `EffectTransfer.AbstractT`):
the conserved `balance`-domain total + the reconstructed authority `Graph`. -/
structure AbstractP where
  /-- the conserved `balance`-domain total. -/
  balanceTotal : ℤ
  /-- the reconstructed authority graph. -/
  authGraph    : Dregg2.Spec.Graph Dregg2.Authority.Label Dregg2.Spec.ExecRights

/-- The abstraction function: a chained record state denotes its `recTotal` and its `execGraph`. -/
def absP (s : RecChainedState) : AbstractP :=
  { balanceTotal := recTotal s.kernel, authGraph := execGraph s.kernel.caps }

/-- **`AbsStep a a'`** — the abstract Paired step relation: the abstract `balance` total is
CONSERVED (`Spec.conservedInDomain Domain.balance` on the realized delta) and the authority graph is
UNCHANGED. The genuine abstract transition (the bottom edge of the simulation square), VERBATIM from
`EffectTransfer.AbsStep`. -/
@[reducible] def AbsStep (a a' : AbstractP) : Prop :=
  conservedInDomain Domain.balance [a'.balanceTotal - a.balanceTotal] ∧
    a'.authGraph = a.authGraph

/-- **GENERIC FORWARD SIMULATION — THE REFINEMENT (PROVED).** A committed `pairedStep` (over any
metadata `field ≠ "balance"`) is matched by an abstract `Spec` step `AbsStep (absP s) (absP s')`,
AND the committed turn passed the abstract authority `Guard`. So every executable Paired effect is
an abstract step: the abstract balance total is conserved, the authority graph preserved, and the
turn admitted by the abstract gate. The record-world forward-simulation square for the whole
Conservative cluster — the `EffectTransfer.transfer_forward_sim` shape, proved once for all. -/
theorem pairedStep_forward_sim {field : FieldName} (hne : field ≠ balanceField) {mark : Int}
    {s s' : RecChainedState} {actor src dst : CellId} {amt : ℤ}
    (w : Statement → Witness) (h : pairedStep field mark s actor src dst amt = some s') :
    AbsStep (absP s) (absP s') ∧
      Guard.admits (execAuthGuard (Statement := Statement) s.kernel.caps)
        (pairedTurn actor src dst amt) w = true := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · unfold conservedInDomain absP
    rw [pairedStep_conserves hne h]; simp
  · simp only [absP]
    exact pairedStep_authGraph_unchanged h
  · rw [Dregg2.Spec.exec_authz_iff_guard]
    exact pairedStep_authorized h

end ForwardSim

/-! ## §2 — The §8 PORTAL: the note cluster's cryptographic check as a carried `Prop`.

`noteSpend` (revealing a nullifier against a STARK spending proof + Merkle membership) and
`noteCreate` (adding a commitment, with a range proof) carry CRYPTOGRAPHY. Per dregg2's §8 boundary
we DO NOT execute the ZK verification in Lean. We model the STATE TRANSITION executably (the balance
debit/credit + the nullifier-set / commitment-set membership marker, via `pairedStep`) and treat the
cryptographic check as a `CryptoPortal` — a `Prop`-carrier consumed as a HYPOTHESIS. A note effect
gated on the portal commits its state move ONLY when the portal holds; the portal's truth is
*assumed* (the crypto soundness lives behind the `Crypto/*` seam), exactly as those modules do. -/

/-- **The §8 crypto portal.** An opaque `Prop` standing for "the effect's cryptographic check
verified" (the STARK spending proof + nullifier derivation for `noteSpend`; the range proof for
`noteCreate`). NOT executed in Lean — carried as a hypothesis. A note effect's state move commits
only under this portal; its truth is assumed (the `Crypto/*` §8 boundary). -/
structure CryptoPortal where
  /-- the carried crypto-soundness proposition (the ZK verification result, assumed). -/
  verified : Prop

/-- A note effect's executable state move under the portal: if the portal holds (`p.verified`), the
state transition is the `pairedStep` (balance debit/credit + the set-membership metadata marker);
otherwise no commit. The portal guards the *crypto* check; the *state* move is the proved
`pairedStep`. Modelled as: `portalStep` commits iff both the portal holds AND the `pairedStep` gate
passes (fail-closed on the portal). -/
@[reducible] def portalStep (field : FieldName) (mark : Int) (p : CryptoPortal) [Decidable p.verified]
    (s : RecChainedState) (actor src dst : CellId) (amt : ℤ) : Option RecChainedState :=
  if p.verified then pairedStep field mark s actor src dst amt else none

/-- **PORTAL FAIL-CLOSED (PROVED).** If the crypto portal does NOT hold, no `portalStep` commits —
the §8 boundary: an unverified note effect is rejected before any state move. -/
theorem portalStep_fails_without_crypto {field : FieldName} {mark : Int} {p : CryptoPortal}
    [Decidable p.verified] {s : RecChainedState} {actor src dst : CellId} {amt : ℤ}
    (hp : ¬ p.verified) :
    portalStep field mark p s actor src dst amt = none := by
  unfold portalStep; rw [if_neg hp]

/-- **PORTAL ⇒ STATE MOVE (PROVED).** A committed `portalStep` (a) carries the crypto portal
(`p.verified` held) and (b) factors as the committed `pairedStep` — so all the generic
conservation/authority/metadata/forward-sim facts apply to the state move VERBATIM, with the crypto
soundness assumed (carried) per §8. -/
theorem portalStep_commits {field : FieldName} {mark : Int} {p : CryptoPortal}
    [Decidable p.verified] {s s' : RecChainedState} {actor src dst : CellId} {amt : ℤ}
    (h : portalStep field mark p s actor src dst amt = some s') :
    p.verified ∧ pairedStep field mark s actor src dst amt = some s' := by
  unfold portalStep at h
  by_cases hp : p.verified
  · rw [if_pos hp] at h; exact ⟨hp, h⟩
  · rw [if_neg hp] at h; exact absurd h (by simp)

/-! ## §2.5 — THE FAITHFUL HOLDING-STORE LAYER (escrow / obligation) over the CHAINED state.

dregg1's escrow and obligation are NOT balance-conserving two-cell transfers (the old `pairedStep`
shadow). They are SINGLE-cell debits into an off-ledger side-table (`self.escrows` /
`self.obligations`), settled by SINGLE-cell credits that mark the record resolved (`apply.rs:1674`
create / `:1959` release / `:2030` refund; `:1463` obligation create / `:1660` slash). The kernel
now models that side-table faithfully (`RecordKernel.createEscrowK`/`releaseEscrowK`/`refundEscrowK`
+ `escrowHeld`/`recTotalWithEscrow`). Here we lift those to the CHAINED record state (extending the
receipt log) and re-export the escrow/obligation effects through them — so per-effect Σδ ≠ 0 on the
cell ledger, but value is conserved ACROSS the create+settle PAIR (the COMBINED total
`recTotalWithEscrow`), exactly as dregg1's side-table accounting demands. -/

/-- The combined conserved total of a chained state (cell-ledger + escrow holding-store). -/
@[reducible] def chainTotal (s : RecChainedState) : ℤ := recTotalWithEscrow s.kernel

/-- **`createEscrowChain`** — the faithful chained create: run `RecordKernel.createEscrowK` (single-cell
debit + park the off-ledger record), and on success extend the receipt log. -/
def createEscrowChain (s : RecChainedState) (id : Nat) (actor creator recipient : CellId) (amount : ℤ) :
    Option RecChainedState :=
  match createEscrowK s.kernel id actor creator recipient amount with
  | some k' => some { kernel := k', log := pairedTurn actor creator recipient amount :: s.log }
  | none    => none

/-- **`releaseEscrowChain`** — the faithful chained release: `RecordKernel.releaseEscrowK` (single-cell
credit to the recipient + mark resolved), extending the log on success. -/
def releaseEscrowChain (s : RecChainedState) (id : Nat) (actor : CellId) : Option RecChainedState :=
  match releaseEscrowK s.kernel id with
  | some k' => some { kernel := k', log := pairedTurn actor 0 0 0 :: s.log }
  | none    => none

/-- **`refundEscrowChain`** — the faithful chained refund: `RecordKernel.refundEscrowK` (single-cell
credit back to the creator + mark resolved). -/
def refundEscrowChain (s : RecChainedState) (id : Nat) (actor : CellId) : Option RecChainedState :=
  match refundEscrowK s.kernel id with
  | some k' => some { kernel := k', log := pairedTurn actor 0 0 0 :: s.log }
  | none    => none

/-- **`createEscrow_debits_single_cell` — PROVED.** A committed chained create is a SINGLE-cell debit:
the cell-ledger total drops by `amount` and the off-ledger holding-store gains the parked record. NOT
a two-party Σδ = 0 transfer — this is the faithful contrast with the old paired shadow. -/
theorem createEscrow_debits_single_cell {s s' : RecChainedState} {id : Nat}
    {actor creator recipient : CellId} {amount : ℤ}
    (h : createEscrowChain s id actor creator recipient amount = some s') :
    recTotal s'.kernel = recTotal s.kernel - amount ∧
      s'.kernel.escrows = { id := id, creator := creator, recipient := recipient,
                            amount := amount, resolved := false } :: s.kernel.escrows := by
  unfold createEscrowChain at h
  cases hc : createEscrowK s.kernel id actor creator recipient amount with
  | none => rw [hc] at h; exact absurd h (by simp)
  | some k' =>
      rw [hc] at h; simp only [Option.some.injEq] at h; subst h
      exact escrow_create_debits hc

/-- **`createEscrow_conserves_combined` — PROVED (the pair-conservation half for create).** A committed
chained create PRESERVES the COMBINED total: the cell-ledger `−amount` debit is exactly offset by the
holding-store `+amount`. Value moves into the side-table; nothing minted or burned. -/
theorem createEscrow_conserves_combined {s s' : RecChainedState} {id : Nat}
    {actor creator recipient : CellId} {amount : ℤ}
    (h : createEscrowChain s id actor creator recipient amount = some s') :
    chainTotal s' = chainTotal s := by
  unfold createEscrowChain at h
  cases hc : createEscrowK s.kernel id actor creator recipient amount with
  | none => rw [hc] at h; exact absurd h (by simp)
  | some k' =>
      rw [hc] at h; simp only [Option.some.injEq] at h; subst h
      exact escrow_create_conserves_combined hc

/-- **`releaseEscrow_conserves_combined` — PROVED (the pair-conservation half for release).** A
committed chained release PRESERVES the COMBINED total: the recipient `+amount` single-cell credit is
offset by the holding-store drop as the record leaves the unresolved set. Together with
`createEscrow_conserves_combined` this is `escrow_conserves_across_pair`: create parks the value,
release returns it, the COMBINED total is fixed end-to-end. The recipient must be a live account. -/
theorem releaseEscrow_conserves_combined {s s' : RecChainedState} {id : Nat} {actor : CellId}
    (htgt : ∀ r, s.kernel.escrows.find? (fun x => decide (x.id = id ∧ x.resolved = false)) = some r →
      r.recipient ∈ s.kernel.accounts)
    (h : releaseEscrowChain s id actor = some s') :
    chainTotal s' = chainTotal s := by
  unfold releaseEscrowChain at h
  cases hc : releaseEscrowK s.kernel id with
  | none => rw [hc] at h; exact absurd h (by simp)
  | some k' =>
      rw [hc] at h; simp only [Option.some.injEq] at h; subst h
      exact Dregg2.Exec.releaseEscrow_conserves_combined htgt hc

/-- **`refundEscrow_conserves_combined` — PROVED.** The refund half: value returns to the creator,
combined total fixed. -/
theorem refundEscrow_conserves_combined {s s' : RecChainedState} {id : Nat} {actor : CellId}
    (htgt : ∀ r, s.kernel.escrows.find? (fun x => decide (x.id = id ∧ x.resolved = false)) = some r →
      r.creator ∈ s.kernel.accounts)
    (h : refundEscrowChain s id actor = some s') :
    chainTotal s' = chainTotal s := by
  unfold refundEscrowChain at h
  cases hc : refundEscrowK s.kernel id with
  | none => rw [hc] at h; exact absurd h (by simp)
  | some k' =>
      rw [hc] at h; simp only [Option.some.injEq] at h; subst h
      exact Dregg2.Exec.refundEscrow_conserves_combined htgt hc

/-- **`escrow_conserves_across_pair` — PROVED (the headline REAL invariant).** create-then-release is
end-to-end COMBINED-total conserving: the create parks `amount` off-ledger (combined fixed) and the
release returns it (combined fixed), so the composite is value-conserving with the side-table as the
in-flight accumulator — even though NEITHER step is Σδ = 0 on the cell ledger alone. -/
theorem escrow_conserves_across_pair {s s1 s2 : RecChainedState} {id : Nat}
    {actor creator recipient : CellId} {amount : ℤ}
    (htgt : ∀ r, s1.kernel.escrows.find? (fun x => decide (x.id = id ∧ x.resolved = false)) = some r →
      r.recipient ∈ s1.kernel.accounts)
    (hcreate : createEscrowChain s id actor creator recipient amount = some s1)
    (hrelease : releaseEscrowChain s1 id actor = some s2) :
    chainTotal s2 = chainTotal s := by
  rw [releaseEscrow_conserves_combined htgt hrelease, createEscrow_conserves_combined hcreate]

/-- **`createEscrow_authorized` — PROVED.** A committed chained create required the actor to be
authorized over the `creator` cell (`authorizedB`, the SAME gate as `transfer`). -/
theorem createEscrow_authorized {s s' : RecChainedState} {id : Nat}
    {actor creator recipient : CellId} {amount : ℤ}
    (h : createEscrowChain s id actor creator recipient amount = some s') :
    authorizedB s.kernel.caps { actor := actor, src := creator, dst := recipient, amt := amount } = true := by
  unfold createEscrowChain createEscrowK at h
  by_cases hg : authorizedB s.kernel.caps { actor := actor, src := creator, dst := recipient, amt := amount } = true
      ∧ 0 ≤ amount ∧ amount ≤ balOf (s.kernel.cell creator) ∧ creator ∈ s.kernel.accounts
      ∧ ¬ (∃ r ∈ s.kernel.escrows, r.id = id)
  · exact hg.1
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-! ### Obligations (`createObligation`/`fulfillObligation`/`slashObligation`) reuse the SAME
holding-store: dregg1's `self.obligations` is structurally identical to `self.escrows`
(single-cell stake debit at create, single-cell credit at fulfill/slash, `resolved` flag,
`apply.rs:1463`/`:1660`). We model the obligation lifecycle through the same faithful kernel
functions — create locks the stake (debit obligor + park), fulfill returns it to the obligor, slash
sends it to the beneficiary — so the SAME `recTotalWithEscrow` pair-conservation holds. -/

/-- **`createObligation` (faithful)** — lock `stake` from the obligor into the holding-store (single
-cell debit + parked record, refund target = obligor, settle target = beneficiary). -/
def createObligationChain (s : RecChainedState) (id : Nat) (actor obligor beneficiary : CellId) (stake : ℤ) :
    Option RecChainedState := createEscrowChain s id actor obligor beneficiary stake

/-- **`fulfillObligation` (faithful)** — return the staked value to the obligor (= the record's
creator/refund target) and mark resolved: the obligation analog of `refundEscrow`. -/
def fulfillObligationChain (s : RecChainedState) (id actor : CellId) : Option RecChainedState :=
  refundEscrowChain s id actor

/-- **`slashObligation` (faithful)** — send the staked value to the beneficiary (= the record's
recipient/release target) and mark resolved: the obligation analog of `releaseEscrow`. -/
def slashObligationChain (s : RecChainedState) (id actor : CellId) : Option RecChainedState :=
  releaseEscrowChain s id actor

/-- **`obligation_conserves_across_pair` — PROVED.** create-then-fulfill is COMBINED-total conserving
(stake parked off-ledger, then returned to the obligor) — the same side-table accounting as escrow. -/
theorem obligation_conserves_across_pair {s s1 s2 : RecChainedState} {id : Nat}
    {actor obligor beneficiary : CellId} {stake : ℤ}
    (htgt : ∀ r, s1.kernel.escrows.find? (fun x => decide (x.id = id ∧ x.resolved = false)) = some r →
      r.creator ∈ s1.kernel.accounts)
    (hcreate : createObligationChain s id actor obligor beneficiary stake = some s1)
    (hfulfill : fulfillObligationChain s1 id actor = some s2) :
    chainTotal s2 = chainTotal s := by
  unfold createObligationChain at hcreate
  unfold fulfillObligationChain at hfulfill
  rw [refundEscrow_conserves_combined htgt hfulfill, createEscrow_conserves_combined hcreate]

/-! ### Note spend (`noteSpend`) — the nullifier SET, NOT a `"nullifier_spent"=1` scalar field.

dregg1's `apply_note_spend` inserts the nullifier into the off-ledger SET `self.note_nullifiers` with
DOUBLE-SPEND REJECTION (`apply.rs:941`): a nullifier already present ⇒ the turn fails-closed. The §8
crypto (STARK spending proof) is the carried `CryptoPortal`; the LEDGER-side anti-replay gate is the
set insert, modelled faithfully by `RecordKernel.noteSpendNullifier`. -/

/-- **`noteSpendChain` (faithful)** — §8-portal-gated nullifier-set insert: commit ONLY if the crypto
portal holds AND the nullifier is not already spent (`RecordKernel.noteSpendNullifier`, fail-closed on
double-spend). -/
def noteSpendChain (p : CryptoPortal) [Decidable p.verified] (s : RecChainedState)
    (nf : Nat) (actor : CellId) : Option RecChainedState :=
  if p.verified then
    match noteSpendNullifier s.kernel nf with
    | some k' => some { kernel := k', log := pairedTurn actor 0 0 0 :: s.log }
    | none    => none
  else none

/-- **`noteSpend_fails_without_crypto` — PROVED.** No spend commits without the §8 crypto portal. -/
theorem noteSpend_fails_without_crypto {p : CryptoPortal} [Decidable p.verified] {s : RecChainedState}
    {nf : Nat} {actor : CellId} (hp : ¬ p.verified) : noteSpendChain p s nf actor = none := by
  unfold noteSpendChain; rw [if_neg hp]

/-- **`noteSpend_no_double_spend` — PROVED (the REAL anti-replay invariant).** A nullifier already in
the spent SET CANNOT be spent again: `noteSpendChain` fails-closed — the SET prevents it, not a scalar
flag. -/
theorem noteSpend_no_double_spend {p : CryptoPortal} [Decidable p.verified] {s : RecChainedState}
    {nf : Nat} {actor : CellId} (h : nf ∈ s.kernel.nullifiers) : noteSpendChain p s nf actor = none := by
  unfold noteSpendChain
  by_cases hp : p.verified
  · rw [if_pos hp, Dregg2.Exec.note_no_double_spend s.kernel nf h]
  · rw [if_neg hp]

/-- **`noteSpend_then_reject` — PROVED (composed anti-replay).** After a committed spend of `nf`, a
second spend of the SAME `nf` on the resulting state fails-closed. Double-spend is impossible. -/
theorem noteSpend_then_reject {p : CryptoPortal} [Decidable p.verified] {s s' : RecChainedState}
    {nf : Nat} {actor : CellId} (h : noteSpendChain p s nf actor = some s') :
    noteSpendChain p s' nf actor = none := by
  unfold noteSpendChain at h ⊢
  by_cases hp : p.verified
  · rw [if_pos hp] at h ⊢
    cases hns : noteSpendNullifier s.kernel nf with
    | none => rw [hns] at h; exact absurd h (by simp)
    | some k' =>
        rw [hns] at h; simp only [Option.some.injEq] at h; subst h
        rw [Dregg2.Exec.note_no_double_spend k' nf (Dregg2.Exec.note_spend_inserts hns)]
  · exact absurd h (by rw [if_neg hp]; simp)

/-- **`escrow_obligation_note_are_distinct` — PROVED (the catalog DE-CONFLATION).** The three effects
write to THREE DIFFERENT state components — escrow/obligation to the `escrows` holding-store (a parked
`EscrowRecord`), note-spend to the `nullifiers` SET — NOT the same `pairedStep` at different string
constants. A committed createEscrow grows `escrows` (and leaves `nullifiers` fixed); a committed
noteSpend grows `nullifiers` (and leaves `escrows` fixed). They are genuinely distinct semantics. -/
theorem escrow_obligation_note_are_distinct
    {sE sE' : RecChainedState} {idE : Nat} {aE cE rE : CellId} {amtE : ℤ}
    (hE : createEscrowChain sE idE aE cE rE amtE = some sE')
    {p : CryptoPortal} [Decidable p.verified] {sN sN' : RecChainedState} {nf : Nat} {aN : CellId}
    (hN : noteSpendChain p sN nf aN = some sN') :
    -- createEscrow touches the escrow store (not nullifiers); noteSpend touches the nullifier set:
    sE'.kernel.escrows ≠ sE.kernel.escrows ∧ sE'.kernel.nullifiers = sE.kernel.nullifiers ∧
    nf ∈ sN'.kernel.nullifiers ∧ sN'.kernel.escrows = sN.kernel.escrows := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- escrow store strictly grows (a cons is never equal to its tail).
    have := (createEscrow_debits_single_cell hE).2
    rw [this]; exact List.cons_ne_self _ _
  · -- createEscrow does not touch the nullifier set.
    unfold createEscrowChain createEscrowK at hE
    by_cases hg : authorizedB sE.kernel.caps { actor := aE, src := cE, dst := rE, amt := amtE } = true
        ∧ 0 ≤ amtE ∧ amtE ≤ balOf (sE.kernel.cell cE) ∧ cE ∈ sE.kernel.accounts
        ∧ ¬ (∃ r ∈ sE.kernel.escrows, r.id = idE)
    · rw [if_pos hg] at hE; simp only [Option.some.injEq] at hE; subst hE; rfl
    · rw [if_neg hg] at hE; exact absurd hE (by simp)
  · -- noteSpend inserts nf into the nullifier set.
    unfold noteSpendChain at hN
    by_cases hp : p.verified
    · rw [if_pos hp] at hN
      cases hns : noteSpendNullifier sN.kernel nf with
      | none => rw [hns] at hN; exact absurd hN (by simp)
      | some k' =>
          rw [hns] at hN; simp only [Option.some.injEq] at hN; subst hN
          exact Dregg2.Exec.note_spend_inserts hns
    · rw [if_neg hp] at hN; exact absurd hN (by simp)
  · -- noteSpend does not touch the escrow store.
    unfold noteSpendChain noteSpendNullifier at hN
    by_cases hp : p.verified
    · rw [if_pos hp] at hN
      by_cases hin : nf ∈ sN.kernel.nullifiers
      · rw [if_pos hin] at hN; exact absurd hN (by simp)
      · rw [if_neg hin] at hN; simp only [Option.some.injEq] at hN; subst hN; rfl
    · rw [if_neg hp] at hN; exact absurd hN (by simp)

/-! ## §3 — THE REMAINING Conservative effects: each instantiates the generic spine at its own
metadata field. (Queues and the bridge's local Σδ = 0 phases ARE genuine two-cell cell-to-cell moves
in dregg1 — a deposit into a real queue cell, a lock into a bridge-escrow cell — so the `pairedStep`
model is faithful for them; escrow/obligation/note above are the off-ledger-store effects that needed
the faithful holding-store / nullifier-set remodel.)

For each remaining Conservative effect we name (1) its metadata field constant (the named-field write
the effect carries, `≠ "balance"`), (2) its `*Step` as `pairedStep`/`portalStep` at that field, and
(3) the five keystones as the generic lemmas instantiated. -/

/-! ### §3.5 — Queues: `queueEnqueue` / `queueDequeue` / `queueAtomicTx` / `queuePipelineStep`.

dregg1's anti-spam queue deposit: `queueEnqueue` moves the refundable `deposit` from the sender into
the queue cell (status = enqueued); `queueDequeue` refunds it back on consumption (status = dequeued).
`queueAtomicTx` is an all-or-nothing batch — modelled here as one paired transfer that the executor's
transaction discipline (`TurnExecutor.execTurn`'s all-or-nothing fold) lifts to a batch; the per-op
conservation is this `pairedStep`. `queuePipelineStep` routes a deposit source ⟶ sink. Each is a
two-party deposit move (Σδ = 0) carrying a queue `"status"` marker. -/

def queueStatusField : FieldName := "queue_status"

theorem queueStatus_ne : queueStatusField ≠ balanceField := by decide

/-- **`queueEnqueue` — deposit sender ⟶ queue cell, status = enqueued (1).** -/
@[reducible] def queueEnqueueStep (s : RecChainedState) (sender queueCell actor : CellId) (deposit : ℤ) :
    Option RecChainedState := pairedStep queueStatusField 1 s sender queueCell actor deposit

theorem queueEnqueue_conserves {s s' : RecChainedState} {sender queueCell actor : CellId}
    {deposit : ℤ} (h : queueEnqueueStep s sender queueCell actor deposit = some s') :
    recTotal s'.kernel = recTotal s.kernel :=
  pairedStep_conserves queueStatus_ne h

theorem queueEnqueue_authorized {s s' : RecChainedState} {sender queueCell actor : CellId}
    {deposit : ℤ} (h : queueEnqueueStep s sender queueCell actor deposit = some s') :
    authorizedB s.kernel.caps (pairedTurn sender queueCell actor deposit) = true :=
  pairedStep_authorized h

theorem queueEnqueue_metadata {s s' : RecChainedState} {sender queueCell actor : CellId}
    {deposit : ℤ} (h : queueEnqueueStep s sender queueCell actor deposit = some s') :
    (s'.kernel.cell queueCell).scalar queueStatusField = some 1 ∧ s'.kernel.caps = s.kernel.caps :=
  pairedStep_metadata h

theorem queueEnqueue_forward_sim {Statement Witness : Type} [Verifiable Statement Witness]
    {s s' : RecChainedState} {sender queueCell actor : CellId} {deposit : ℤ}
    (w : Statement → Witness) (h : queueEnqueueStep s sender queueCell actor deposit = some s') :
    AbsStep (absP s) (absP s') ∧
      Guard.admits (execAuthGuard (Statement := Statement) s.kernel.caps)
        (pairedTurn sender queueCell actor deposit) w = true :=
  pairedStep_forward_sim queueStatus_ne w h

/-- **`queueDequeue` — refund deposit queue cell ⟶ sender, status = dequeued (2).** -/
@[reducible] def queueDequeueStep (s : RecChainedState) (queueCell sender actor : CellId) (deposit : ℤ) :
    Option RecChainedState := pairedStep queueStatusField 2 s queueCell sender actor deposit

theorem queueDequeue_conserves {s s' : RecChainedState} {queueCell sender actor : CellId}
    {deposit : ℤ} (h : queueDequeueStep s queueCell sender actor deposit = some s') :
    recTotal s'.kernel = recTotal s.kernel :=
  pairedStep_conserves queueStatus_ne h

theorem queueDequeue_authorized {s s' : RecChainedState} {queueCell sender actor : CellId}
    {deposit : ℤ} (h : queueDequeueStep s queueCell sender actor deposit = some s') :
    authorizedB s.kernel.caps (pairedTurn queueCell sender actor deposit) = true :=
  pairedStep_authorized h

theorem queueDequeue_metadata {s s' : RecChainedState} {queueCell sender actor : CellId}
    {deposit : ℤ} (h : queueDequeueStep s queueCell sender actor deposit = some s') :
    (s'.kernel.cell sender).scalar queueStatusField = some 2 ∧ s'.kernel.caps = s.kernel.caps :=
  pairedStep_metadata h

theorem queueDequeue_forward_sim {Statement Witness : Type} [Verifiable Statement Witness]
    {s s' : RecChainedState} {queueCell sender actor : CellId} {deposit : ℤ}
    (w : Statement → Witness) (h : queueDequeueStep s queueCell sender actor deposit = some s') :
    AbsStep (absP s) (absP s') ∧
      Guard.admits (execAuthGuard (Statement := Statement) s.kernel.caps)
        (pairedTurn queueCell sender actor deposit) w = true :=
  pairedStep_forward_sim queueStatus_ne w h

/-- **`queueAtomicTx` — one op of an all-or-nothing batch deposit move src ⟶ dst, status =
atomic (3).** The per-op conservation; the whole-batch all-or-nothing is `TurnExecutor.execTurn`'s
`Option`-fold (any op `none` ⇒ batch `none`), built on this committing per-op `pairedStep`. -/
@[reducible] def queueAtomicTxStep (s : RecChainedState) (src dst actor : CellId) (amt : ℤ) :
    Option RecChainedState := pairedStep queueStatusField 3 s src dst actor amt

theorem queueAtomicTx_conserves {s s' : RecChainedState} {src dst actor : CellId} {amt : ℤ}
    (h : queueAtomicTxStep s src dst actor amt = some s') :
    recTotal s'.kernel = recTotal s.kernel :=
  pairedStep_conserves queueStatus_ne h

theorem queueAtomicTx_authorized {s s' : RecChainedState} {src dst actor : CellId} {amt : ℤ}
    (h : queueAtomicTxStep s src dst actor amt = some s') :
    authorizedB s.kernel.caps (pairedTurn src dst actor amt) = true :=
  pairedStep_authorized h

theorem queueAtomicTx_metadata {s s' : RecChainedState} {src dst actor : CellId} {amt : ℤ}
    (h : queueAtomicTxStep s src dst actor amt = some s') :
    (s'.kernel.cell dst).scalar queueStatusField = some 3 ∧ s'.kernel.caps = s.kernel.caps :=
  pairedStep_metadata h

theorem queueAtomicTx_forward_sim {Statement Witness : Type} [Verifiable Statement Witness]
    {s s' : RecChainedState} {src dst actor : CellId} {amt : ℤ}
    (w : Statement → Witness) (h : queueAtomicTxStep s src dst actor amt = some s') :
    AbsStep (absP s) (absP s') ∧
      Guard.admits (execAuthGuard (Statement := Statement) s.kernel.caps)
        (pairedTurn src dst actor amt) w = true :=
  pairedStep_forward_sim queueStatus_ne w h

/-- **`queuePipelineStep` — route deposit source ⟶ sink, status = piped (4).** -/
@[reducible] def queuePipelineStepStep (s : RecChainedState) (source sink actor : CellId) (amt : ℤ) :
    Option RecChainedState := pairedStep queueStatusField 4 s source sink actor amt

theorem queuePipelineStep_conserves {s s' : RecChainedState} {source sink actor : CellId} {amt : ℤ}
    (h : queuePipelineStepStep s source sink actor amt = some s') :
    recTotal s'.kernel = recTotal s.kernel :=
  pairedStep_conserves queueStatus_ne h

theorem queuePipelineStep_authorized {s s' : RecChainedState} {source sink actor : CellId} {amt : ℤ}
    (h : queuePipelineStepStep s source sink actor amt = some s') :
    authorizedB s.kernel.caps (pairedTurn source sink actor amt) = true :=
  pairedStep_authorized h

theorem queuePipelineStep_metadata {s s' : RecChainedState} {source sink actor : CellId} {amt : ℤ}
    (h : queuePipelineStepStep s source sink actor amt = some s') :
    (s'.kernel.cell sink).scalar queueStatusField = some 4 ∧ s'.kernel.caps = s.kernel.caps :=
  pairedStep_metadata h

theorem queuePipelineStep_forward_sim {Statement Witness : Type} [Verifiable Statement Witness]
    {s s' : RecChainedState} {source sink actor : CellId} {amt : ℤ}
    (w : Statement → Witness) (h : queuePipelineStepStep s source sink actor amt = some s') :
    AbsStep (absP s) (absP s') ∧
      Guard.admits (execAuthGuard (Statement := Statement) s.kernel.caps)
        (pairedTurn source sink actor amt) w = true :=
  pairedStep_forward_sim queueStatus_ne w h

/-! ### §3.6 — Bridge (the Σδ = 0 phases): `bridgeLock` / `bridgeFinalize` / `bridgeCancel`.

dregg1's cross-federation bridge: `bridgeLock` locks a note's value into a bridge-escrow cell (a
conditional lock, NOT a burn — recoverable on timeout); `bridgeFinalize` makes the lock permanent on
a destination receipt (value moves to the bridge sink); `bridgeCancel` unlocks after timeout (value
returns to the owner). All three are Σδ = 0 LOCAL state moves (the cross-chain accounting is the
paired federation's; locally each is a two-party move) carrying a bridge `"status"` marker (1 =
locked, 2 = finalized, 3 = cancelled). The destination-receipt verification on `bridgeFinalize` is a
§8 PORTAL — but here we model the LOCAL state move (which is unconditional once authorized); the
receipt check lives behind the same §8 seam as the note proofs and can be portal-wrapped identically. -/

def bridgeStatusField : FieldName := "bridge_status"

theorem bridgeStatus_ne : bridgeStatusField ≠ balanceField := by decide

/-- **`bridgeLock` — lock note value owner ⟶ bridge-escrow cell, status = locked (1).** -/
@[reducible] def bridgeLockStep (s : RecChainedState) (owner bridgeCell actor : CellId) (value : ℤ) :
    Option RecChainedState := pairedStep bridgeStatusField 1 s owner bridgeCell actor value

theorem bridgeLock_conserves {s s' : RecChainedState} {owner bridgeCell actor : CellId} {value : ℤ}
    (h : bridgeLockStep s owner bridgeCell actor value = some s') :
    recTotal s'.kernel = recTotal s.kernel :=
  pairedStep_conserves bridgeStatus_ne h

theorem bridgeLock_authorized {s s' : RecChainedState} {owner bridgeCell actor : CellId} {value : ℤ}
    (h : bridgeLockStep s owner bridgeCell actor value = some s') :
    authorizedB s.kernel.caps (pairedTurn owner bridgeCell actor value) = true :=
  pairedStep_authorized h

theorem bridgeLock_metadata {s s' : RecChainedState} {owner bridgeCell actor : CellId} {value : ℤ}
    (h : bridgeLockStep s owner bridgeCell actor value = some s') :
    (s'.kernel.cell bridgeCell).scalar bridgeStatusField = some 1 ∧ s'.kernel.caps = s.kernel.caps :=
  pairedStep_metadata h

theorem bridgeLock_forward_sim {Statement Witness : Type} [Verifiable Statement Witness]
    {s s' : RecChainedState} {owner bridgeCell actor : CellId} {value : ℤ}
    (w : Statement → Witness) (h : bridgeLockStep s owner bridgeCell actor value = some s') :
    AbsStep (absP s) (absP s') ∧
      Guard.admits (execAuthGuard (Statement := Statement) s.kernel.caps)
        (pairedTurn owner bridgeCell actor value) w = true :=
  pairedStep_forward_sim bridgeStatus_ne w h

/-- **`bridgeFinalize` — make the lock permanent bridge-escrow ⟶ bridge sink, status = finalized
(2).** (The destination-receipt check is the §8 portal; the local state move is this `pairedStep`.) -/
@[reducible] def bridgeFinalizeStep (s : RecChainedState) (bridgeCell sink actor : CellId) (value : ℤ) :
    Option RecChainedState := pairedStep bridgeStatusField 2 s bridgeCell sink actor value

theorem bridgeFinalize_conserves {s s' : RecChainedState} {bridgeCell sink actor : CellId} {value : ℤ}
    (h : bridgeFinalizeStep s bridgeCell sink actor value = some s') :
    recTotal s'.kernel = recTotal s.kernel :=
  pairedStep_conserves bridgeStatus_ne h

theorem bridgeFinalize_authorized {s s' : RecChainedState} {bridgeCell sink actor : CellId} {value : ℤ}
    (h : bridgeFinalizeStep s bridgeCell sink actor value = some s') :
    authorizedB s.kernel.caps (pairedTurn bridgeCell sink actor value) = true :=
  pairedStep_authorized h

theorem bridgeFinalize_metadata {s s' : RecChainedState} {bridgeCell sink actor : CellId} {value : ℤ}
    (h : bridgeFinalizeStep s bridgeCell sink actor value = some s') :
    (s'.kernel.cell sink).scalar bridgeStatusField = some 2 ∧ s'.kernel.caps = s.kernel.caps :=
  pairedStep_metadata h

theorem bridgeFinalize_forward_sim {Statement Witness : Type} [Verifiable Statement Witness]
    {s s' : RecChainedState} {bridgeCell sink actor : CellId} {value : ℤ}
    (w : Statement → Witness) (h : bridgeFinalizeStep s bridgeCell sink actor value = some s') :
    AbsStep (absP s) (absP s') ∧
      Guard.admits (execAuthGuard (Statement := Statement) s.kernel.caps)
        (pairedTurn bridgeCell sink actor value) w = true :=
  pairedStep_forward_sim bridgeStatus_ne w h

/-- **`bridgeCancel` — unlock post-timeout bridge-escrow ⟶ owner, status = cancelled (3).** -/
@[reducible] def bridgeCancelStep (s : RecChainedState) (bridgeCell owner actor : CellId) (value : ℤ) :
    Option RecChainedState := pairedStep bridgeStatusField 3 s bridgeCell owner actor value

theorem bridgeCancel_conserves {s s' : RecChainedState} {bridgeCell owner actor : CellId} {value : ℤ}
    (h : bridgeCancelStep s bridgeCell owner actor value = some s') :
    recTotal s'.kernel = recTotal s.kernel :=
  pairedStep_conserves bridgeStatus_ne h

theorem bridgeCancel_authorized {s s' : RecChainedState} {bridgeCell owner actor : CellId} {value : ℤ}
    (h : bridgeCancelStep s bridgeCell owner actor value = some s') :
    authorizedB s.kernel.caps (pairedTurn bridgeCell owner actor value) = true :=
  pairedStep_authorized h

theorem bridgeCancel_metadata {s s' : RecChainedState} {bridgeCell owner actor : CellId} {value : ℤ}
    (h : bridgeCancelStep s bridgeCell owner actor value = some s') :
    (s'.kernel.cell owner).scalar bridgeStatusField = some 3 ∧ s'.kernel.caps = s.kernel.caps :=
  pairedStep_metadata h

theorem bridgeCancel_forward_sim {Statement Witness : Type} [Verifiable Statement Witness]
    {s s' : RecChainedState} {bridgeCell owner actor : CellId} {value : ℤ}
    (w : Statement → Witness) (h : bridgeCancelStep s bridgeCell owner actor value = some s') :
    AbsStep (absP s) (absP s') ∧
      Guard.admits (execAuthGuard (Statement := Statement) s.kernel.caps)
        (pairedTurn bridgeCell owner actor value) w = true :=
  pairedStep_forward_sim bridgeStatus_ne w h

/-! ## §4 — Axiom-hygiene tripwires (the honesty pins over every keystone).

Whitelist exactly `{propext, Classical.choice, Quot.sound}` — no `sorryAx`/`admit`/`axiom`/
`native_decide`. The generic spine + every effect's five keystones are genuinely proved. -/

-- The shared bespoke machinery + generic spine:
#assert_axioms setField'_read
#assert_axioms setField'_balOf
#assert_axioms writeMeta_recTotal
#assert_axioms pairedStep_factors
#assert_axioms pairedStep_conserves
#assert_axioms pairedStep_domain
#assert_axioms pairedStep_authorized
#assert_axioms pairedStep_unauthorized_fails
#assert_axioms pairedStep_caps_unchanged
#assert_axioms pairedStep_authGraph_unchanged
#assert_axioms pairedStep_metadata
#assert_axioms pairedStep_forward_sim
#assert_axioms portalStep_fails_without_crypto
#assert_axioms portalStep_commits
-- Escrow (FAITHFUL holding-store: single-cell debit/credit + off-ledger record; pair-conserving):
#assert_axioms createEscrow_debits_single_cell
#assert_axioms createEscrow_conserves_combined
#assert_axioms createEscrow_authorized
#assert_axioms releaseEscrow_conserves_combined
#assert_axioms refundEscrow_conserves_combined
#assert_axioms escrow_conserves_across_pair
-- Obligations (SAME faithful holding-store as escrow):
#assert_axioms obligation_conserves_across_pair
-- Note spend (FAITHFUL nullifier SET, double-spend rejected — NOT a scalar flag):
#assert_axioms noteSpend_fails_without_crypto
#assert_axioms noteSpend_no_double_spend
#assert_axioms noteSpend_then_reject
-- The catalog DE-CONFLATION (escrow store vs obligation store vs nullifier set are DISTINCT):
#assert_axioms escrow_obligation_note_are_distinct
-- Queues:
#assert_axioms queueEnqueue_conserves
#assert_axioms queueEnqueue_forward_sim
#assert_axioms queueDequeue_conserves
#assert_axioms queueDequeue_forward_sim
#assert_axioms queueAtomicTx_conserves
#assert_axioms queueAtomicTx_forward_sim
#assert_axioms queuePipelineStep_conserves
#assert_axioms queuePipelineStep_forward_sim
-- Bridge:
#assert_axioms bridgeLock_conserves
#assert_axioms bridgeLock_forward_sim
#assert_axioms bridgeFinalize_conserves
#assert_axioms bridgeFinalize_forward_sim
#assert_axioms bridgeCancel_conserves
#assert_axioms bridgeCancel_forward_sim

/-! ## §5 — Non-vacuity: a concrete instance of EACH effect commits, conserves, marks its field.

Cells 0,1,2 with balances 100,5,0; actor 0 owns cell 0, actor 1 owns cell 1, actor 2 owns cell 2.
Empty cap table (authority by ownership), empty receipt chain. Each effect below COMMITS, CONSERVES
the total (105 → 105), and writes its status/marker field — non-vacuously (`#eval`). -/

/-- A chained record state: cells 0,1,2 with balances 100,5,0. -/
def ep0 : RecChainedState :=
  { kernel :=
      { accounts := {0, 1, 2}
        cell := fun c => if c = 0 then .record [("balance", .int 100)]
                         else if c = 1 then .record [("balance", .int 5)]
                         else .record [("balance", .int 0)]
        caps := fun _ => [] }
    log := [] }

/-- A verified crypto portal (the §8 ZK check assumed to hold) — `Decidable` so the note/committed
effects compute. -/
def okPortal : CryptoPortal := { verified := True }
instance : Decidable (okPortal.verified) := instDecidableTrue
/-- A FAILED crypto portal (the §8 check rejected) — note effects must fail-close on it. -/
def badPortal : CryptoPortal := { verified := False }
instance : Decidable (badPortal.verified) := instDecidableFalse

-- Each queue/bridge call is a genuine two-cell move (actor=src=0, dst=1); escrow/obligation/note are
-- the FAITHFUL holding-store / nullifier-set effects (single-cell + side-table).

-- FAITHFUL ESCROW: createEscrow id=7 debits creator 0 by 30 (single cell), parks an off-ledger record.
#eval (createEscrowChain ep0 7 0 0 1 30).isSome                                        -- true
#eval (createEscrowChain ep0 7 0 0 1 30).map (fun s => balOf (s.kernel.cell 0))        -- some 70 (DEBITED)
#eval (createEscrowChain ep0 7 0 0 1 30).map (fun s => recTotal s.kernel)              -- some 75 (cell-ledger DROPPED by 30)
#eval (createEscrowChain ep0 7 0 0 1 30).map (fun s => chainTotal s)                   -- some 105 (COMBINED conserved)
#eval (createEscrowChain ep0 7 0 0 1 30).map (fun s => escrowHeld s.kernel)            -- some 30 (parked off-ledger)
-- release: credit recipient 1 by 30 (single cell), mark resolved; combined stays 105.
#eval ((createEscrowChain ep0 7 0 0 1 30).bind (fun s => releaseEscrowChain s 7 0)).map
        (fun s => (balOf (s.kernel.cell 1), chainTotal s, escrowHeld s.kernel))        -- some (35, 105, 0)
-- refund returns to creator 0 instead.
#eval ((createEscrowChain ep0 7 0 0 1 30).bind (fun s => refundEscrowChain s 7 0)).map
        (fun s => (balOf (s.kernel.cell 0), chainTotal s))                             -- some (100, 105)
-- FAITHFUL OBLIGATION (same holding-store): create locks stake, fulfill returns to obligor.
#eval (createObligationChain ep0 8 0 0 1 30).map (fun s => escrowHeld s.kernel)        -- some 30
#eval ((createObligationChain ep0 8 0 0 1 30).bind (fun s => fulfillObligationChain s 8 0)).map
        (fun s => (balOf (s.kernel.cell 0), chainTotal s))                             -- some (100, 105)
-- FAITHFUL NOTE SPEND: nullifier-SET insert under the §8 portal; DOUBLE-SPEND rejected.
#eval (noteSpendChain okPortal ep0 42 0).isSome                                        -- true
#eval (noteSpendChain badPortal ep0 42 0).isSome                                       -- false (no crypto)
#eval (noteSpendChain okPortal ep0 42 0).map (fun s => s.kernel.nullifiers.contains 42) -- some true (in the SET)
#eval ((noteSpendChain okPortal ep0 42 0).bind (fun s => noteSpendChain okPortal s 42 0)).isSome -- false (double-spend!)
-- queueEnqueue: deposit 30 sender 0 → queue cell 1, status enqueued(1); conserves.
#eval (queueEnqueueStep ep0 0 0 1 30).map (fun s => recTotal s.kernel)                 -- some 105
#eval (queueEnqueueStep ep0 0 0 1 30).map (fun s => (s.kernel.cell 0).scalar "queue_status") -- some (some 1)
#eval (queueDequeueStep ep0 0 0 1 30).map (fun s => (s.kernel.cell 0).scalar "queue_status")  -- some (some 2)
#eval (queueAtomicTxStep ep0 0 0 1 30).map (fun s => (s.kernel.cell 0).scalar "queue_status")  -- some (some 3)
#eval (queuePipelineStepStep ep0 0 0 1 30).map (fun s => (s.kernel.cell 0).scalar "queue_status") -- some (some 4)
-- bridgeLock: lock 30 owner 0 → bridge cell 1, status locked(1); conserves.
#eval (bridgeLockStep ep0 0 0 1 30).map (fun s => recTotal s.kernel)                   -- some 105
#eval (bridgeLockStep ep0 0 0 1 30).map (fun s => (s.kernel.cell 0).scalar "bridge_status") -- some (some 1)
#eval (bridgeFinalizeStep ep0 0 0 1 30).map (fun s => (s.kernel.cell 0).scalar "bridge_status") -- some (some 2)
#eval (bridgeCancelStep ep0 0 0 1 30).map (fun s => (s.kernel.cell 0).scalar "bridge_status")   -- some (some 3)
-- Fail-closed: an unauthorized actor (9 owns nothing) commits NO Conservative effect.
#eval (createEscrowChain ep0 7 9 0 1 30).isSome                                        -- false (unauthorized)
#eval (queueEnqueueStep ep0 9 0 1 30).isSome                                           -- false
-- Overdraft (more than available) is rejected (availability gate).
#eval (createEscrowChain ep0 7 1 1 2 999).isSome                                       -- false (overdraft)

end Dregg2.Exec.EffectsPaired
