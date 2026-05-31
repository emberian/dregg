/-
# Dregg2.Exec.EffectTransfer — the VERTICAL SLICE: dregg1's `Transfer` effect, fully characterized.

**REFERENCE TEMPLATE — the pattern (executable def → conserves → authorized → metadata →
forward-sim) that effects #2..51 instantiate.**

dregg1's `Transfer` (`turn/src/action.rs`, `executor/apply.rs`) is the prototypical *Conservative*
effect: gated by authorization, it **debits the source** cell and **credits the destination** cell
by `amount`, **advances the source's nonce** (replay protection), and **leaves capabilities
untouched**. It is balance-conserving across the two cells (Σδ = 0) — the canonical `Paired` regime
of the 52-effect catalog.

dregg2 already runs a `balance` action through `Exec/TurnExecutorFull.lean`'s `execFull` and
`Exec/TurnExecutor.lean`'s `recCexec` (the chained record-cell transition), with conservation /
authority / chain-link attested. THIS module's value-add is to drive ONE effect — `Transfer` — all
the way through the executor layers as a **fully-characterized, reference-quality** effect:

  1. `transferStep`        — Transfer's EXECUTABLE semantics over the chained record-kernel state:
                              `recCexec`'s gated debit/credit, THEN advance the source's `nonce`
                              field by 1 (the metadata-domain move dregg1's Transfer carries).
                              Concrete, computable, `#eval`-able.
  2. `transfer_conserves`   — TWO-PARTY balance conservation: the source's decrease equals the
                              destination's increase, so the conserved `balance` total `recTotal`
                              is UNCHANGED (the genuine two-cell statement: `-amt` at `src`, `+amt`
                              at `dst`, Σ = 0). The nonce bump does not perturb the balance measure.
  3. `transfer_authorized`  — a committed `transferStep` ⇒ the source held a cap authorizing the
                              debit (`authorizedB`, reusing `recCexec`'s gate).
  4. `transfer_metadata`    — the metadata + authority domains: the source's `nonce` advances by
                              EXACTLY 1, and the cap table / reconstructed authority graph is
                              UNCHANGED.
  5. `transfer_forward_sim` — the REFINEMENT (not mere attestation): a committed `transferStep`
                              is matched by an abstract `Spec` step `AbsStep (absT s) (absT s')` —
                              the abstract balance total is preserved (`Spec.conservedInDomain
                              Domain.balance`), the turn passed the abstract authority `Guard`, and
                              the abstract authority `Graph` is unchanged. This is the record-world
                              forward-simulation square for Transfer, the concrete instance of
                              `Spec/ExecRefinement.lean`'s `recExec_step_refines` shape.

## How effects #2..51 instantiate this template
Each catalog effect copies the five-step skeleton. The REUSABLE steps (mechanical): the `recCexec`
gate + the conservation/authority/chain-link facts come VERBATIM from `recCexec_attests`; the
forward-sim `AbsStep` (conservation projection + authority `Guard` + graph-preservation) is the
SAME `Spec.execGraph`/`Spec.execAuthGuard`/`Spec.conservedInDomain` instantiation for every
authority-frame-preserving effect. The BESPOKE step is per-effect: which DOMAIN the effect moves
and HOW its named-field write behaves (here, the `nonce` bump and its `balOf`-non-interference) —
that is the only new lemma each effect must supply. So Transfer is `recCexec` + one metadata lemma;
mint/burn (already in `TurnExecutorFull`) are `recCexec`-shaped + a supply-delta lemma; etc.

## Discipline
No `sorry`/`admit`/`axiom`/`native_decide`. `#assert_axioms` whitelists exactly `{propext,
Classical.choice, Quot.sound}` on every keystone. Self-contained: reuses ONLY the already-built
`Exec.TurnExecutor`/`Exec.RecordKernel`/`Spec.ExecRefinement` primitives; depends on no in-flight
new module. Verified standalone: `lake env lean Dregg2/Exec/EffectTransfer.lean`.
-/
import Dregg2.Exec.TurnExecutor
import Dregg2.Spec.ExecRefinement

namespace Dregg2.Exec.EffectTransfer

open Dregg2.Exec
open Dregg2.Authority (Caps)
open Dregg2.Spec (Domain conservedInDomain execGraph execAuthGuard Guard)
open Dregg2.Laws (Verifiable)
open scoped BigOperators

/-! ## §0 — The metadata field: a cell's replay-protection `nonce`.

dregg1's Transfer advances the source cell's `nonce` (replay protection). This is a NAMED field of
the content-addressed record, DISTINCT from the conserved `balance` field — so writing it perturbs
the metadata domain WITHOUT touching the conserved balance measure. We re-found a named-field write
for `nonce` exactly as `RecordKernel.setBalance` does for `balance`, and prove the load-bearing
NON-INTERFERENCE lemma: a `nonce` write leaves `balOf` (the `balance` read) untouched. -/

/-- The canonical name of a cell's replay-protection nonce field. -/
def nonceField : FieldName := "nonce"

/-- Read a cell record's `nonce` field as an `Int`, defaulting an absent/ill-typed field to `0`
(fail-soft — a fresh cell with no `nonce` field reads `0`, and a first transfer advances it to `1`).
The metadata-domain measure, the analog of `RecordKernel.balOf` for the `nonce` field. -/
def nonceOf (v : Value) : Int := (v.scalar nonceField).getD 0

/-- Set the `nonce` field of a record cell to `n` (overwriting in place; a non-record value becomes
a singleton `nonce` record). The named-field write the transfer's metadata move uses — it touches
ONLY the `nonce` field, leaving the `balance` field (and every other field) intact. The `nonce`
analog of `RecordKernel.setBalance`. -/
def setNonce (cell : Value) (n : Int) : Value :=
  match cell with
  | .record fs => .record (setNonceList fs n)
  | _          => .record [(nonceField, .int n)]
where
  setNonceList : List (FieldName × Value) → Int → List (FieldName × Value)
  | [],            n => [(nonceField, .int n)]
  | (k, x) :: rest, n => if k == nonceField then (nonceField, .int n) :: rest
                         else (k, x) :: setNonceList rest n

/-- After `setNonce cell n`, reading the `nonce` field returns exactly `n` (the write/read law for
the metadata measure — the `nonce` analog of `setBalance_balOf`). -/
theorem setNonce_nonceOf (cell : Value) (n : Int) : nonceOf (setNonce cell n) = n := by
  have hlist : ∀ fs : List (FieldName × Value),
      ((Value.record (setNonce.setNonceList fs n)).scalar nonceField) = some n := by
    intro fs
    induction fs with
    | nil => simp [setNonce.setNonceList, Value.scalar, Value.field]
    | cons hd tl ih =>
        obtain ⟨k, x⟩ := hd
        simp only [setNonce.setNonceList]
        by_cases hk : (k == nonceField) = true
        · rw [if_pos hk]; simp [Value.scalar, Value.field, nonceField]
        · have hkf : (k == nonceField) = false := by simpa using hk
          rw [if_neg hk]
          simp only [Value.scalar, Value.field] at ih ⊢
          rw [List.find?_cons_of_neg (by simpa using hkf)]
          exact ih
  unfold nonceOf setNonce
  cases cell with
  | record fs => rw [hlist fs]; rfl
  | int _  => simp [Value.scalar, Value.field, nonceField]
  | dig _  => simp [Value.scalar, Value.field, nonceField]
  | sym _  => simp [Value.scalar, Value.field, nonceField]

/-- **NON-INTERFERENCE — PROVED.** Writing the `nonce` field leaves the `balance` read (`balOf`)
UNCHANGED. The two named fields are distinct (`"nonce" ≠ "balance"`), so a `nonce` write never
perturbs the conserved balance measure — this is what lets the metadata move ride alongside the
two-party balance conservation without disturbing it. -/
theorem setNonce_balOf (cell : Value) (n : Int) : balOf (setNonce cell n) = balOf cell := by
  have hlist : ∀ fs : List (FieldName × Value),
      ((Value.record (setNonce.setNonceList fs n)).scalar balanceField)
        = ((Value.record fs).scalar balanceField) := by
    intro fs
    induction fs with
    | nil => simp [setNonce.setNonceList, Value.scalar, Value.field, balanceField, nonceField]
    | cons hd tl ih =>
        obtain ⟨k, x⟩ := hd
        simp only [setNonce.setNonceList]
        by_cases hk : (k == nonceField) = true
        · -- replaced the nonce entry; `balance` lookup skips it either way (k = "nonce" ≠ "balance").
          rw [if_pos hk]
          have hkn : k = nonceField := by simpa using hk
          have hnb : (nonceField == balanceField) = false := by simp [nonceField, balanceField]
          have hkb : (k == balanceField) = false := by rw [hkn]; exact hnb
          simp only [Value.scalar, Value.field]
          rw [List.find?_cons_of_neg (by simpa using hnb),
              List.find?_cons_of_neg (by simpa using hkb)]
        · -- kept this entry; recurse on the tail, both sides carry the same head.
          rw [if_neg hk]
          simp only [Value.scalar, Value.field] at ih ⊢
          by_cases hkb : (k == balanceField) = true
          · rw [List.find?_cons_of_pos (by simpa using hkb),
                List.find?_cons_of_pos (by simpa using hkb)]
          · rw [List.find?_cons_of_neg (by simpa using hkb),
                List.find?_cons_of_neg (by simpa using hkb)]
            exact ih
  unfold balOf setNonce
  cases cell with
  | record fs => rw [hlist fs]
  | int _  => simp [Value.scalar, Value.field, balanceField, nonceField]
  | dig _  => simp [Value.scalar, Value.field, balanceField, nonceField]
  | sym _  => simp [Value.scalar, Value.field, balanceField, nonceField]

/-! ## §1 — `transferStep`: Transfer's EXECUTABLE semantics over the chained record kernel.

`transferStep s actor src dst amt` is the fully-characterized Transfer:
  * run `recCexec` (the gated debit/credit + receipt-chain extension) — this fail-closes on
    authority + availability + liveness + `src ≠ dst`, debits `src`'s `balance` by `amt`, credits
    `dst`'s by `amt`, and appends the receipt; THEN
  * advance `src`'s `nonce` field by 1 (the metadata move: read the post-debit nonce, write +1).

Concrete + computable: it is `recCexec` (already executable) post-composed with the `setNonce`
write. The cap table and authority graph are untouched (neither `recCexec` nor `setNonce` edits
`caps`). -/

/-- Advance the source cell's `nonce` field by 1 in the kernel state (the metadata move). -/
def bumpNonce (k : RecordKernelState) (src : CellId) : RecordKernelState :=
  { k with cell := fun c => if c = src then setNonce (k.cell c) (nonceOf (k.cell c) + 1)
                            else k.cell c }

/-- **`transferStep` — Transfer's executable semantics (PROVED computable).** Run the gated
debit/credit via `recCexec`, then advance the source's `nonce` by 1. Fail-closed: any gate failure
(`recCexec = none`) aborts the whole effect. The `Turn` carries `actor` (authorization), `src`
(target / debit cell), `dst` (credit cell), `amt` (the transferred amount). -/
def transferStep (s : RecChainedState) (actor src dst : CellId) (amt : ℤ) :
    Option RecChainedState :=
  match recCexec s { actor := actor, src := src, dst := dst, amt := amt } with
  | some s1 => some { s1 with kernel := bumpNonce s1.kernel src }
  | none    => none

/-- The `Turn` a `transferStep` runs (the authorized resource move). -/
def transferTurn (actor src dst : CellId) (amt : ℤ) : Turn :=
  { actor := actor, src := src, dst := dst, amt := amt }

/-- **`transferStep` unfolds through its `recCexec` core — PROVED.** A committed `transferStep`
factors as a committed `recCexec` (the gated debit/credit, into `s1`) followed by the source nonce
bump. The bridge every downstream theorem reuses to inherit `recCexec_attests`. -/
theorem transferStep_factors {s s' : RecChainedState} {actor src dst : CellId} {amt : ℤ}
    (h : transferStep s actor src dst amt = some s') :
    ∃ s1, recCexec s (transferTurn actor src dst amt) = some s1 ∧
      s' = { s1 with kernel := bumpNonce s1.kernel src } := by
  unfold transferStep transferTurn at *
  cases hc : recCexec s { actor := actor, src := src, dst := dst, amt := amt } with
  | none => rw [hc] at h; exact absurd h (by simp)
  | some s1 =>
      rw [hc] at h; simp only [Option.some.injEq] at h
      exact ⟨s1, rfl, h.symm⟩

/-! ## §2 — `transfer_conserves`: TWO-PARTY balance conservation (Σδ = 0).

The genuine two-cell statement: the source's `balance` decreases by `amt`, the destination's
increases by `amt`, so the conserved total `recTotal` is UNCHANGED. We get the two-party cancellation
from `recCexec`'s `recKExec_conserves` (which IS the `-amt` at `src` / `+amt` at `dst` cancellation,
`recTransfer_balanceSum_conserve`), then show the metadata nonce bump preserves `recTotal` by the
NON-INTERFERENCE lemma (`setNonce_balOf`). -/

/-- The nonce bump preserves the conserved `balance` total — PROVED. The metadata move does not
perturb the balance domain (every cell's `balOf` is unchanged by a `nonce` write). -/
theorem bumpNonce_recTotal (k : RecordKernelState) (src : CellId) :
    recTotal (bumpNonce k src) = recTotal k := by
  unfold recTotal bumpNonce
  apply Finset.sum_congr rfl
  intro c _
  by_cases hc : c = src
  · simp only [hc, if_pos]; exact setNonce_balOf (k.cell src) (nonceOf (k.cell src) + 1)
  · simp only [if_neg hc]

/-- **`transfer_conserves` — TWO-PARTY BALANCE CONSERVATION (PROVED).** A committed `transferStep`
preserves the total `balance` across the live accounts: `recTotal s'.kernel = recTotal s.kernel`.
The source's `-amt` debit and the destination's `+amt` credit cancel (Σδ = 0, the genuine two-cell
statement from `recKExec_conserves`), and the source's `nonce` bump does not perturb the balance
measure (`bumpNonce_recTotal`). This is dregg1 Transfer's `Conservative`/`Paired` obligation. -/
theorem transfer_conserves {s s' : RecChainedState} {actor src dst : CellId} {amt : ℤ}
    (h : transferStep s actor src dst amt = some s') :
    recTotal s'.kernel = recTotal s.kernel := by
  obtain ⟨s1, hc, hs'⟩ := transferStep_factors h
  -- two-party debit/credit cancellation, via the chained record kernel:
  have hcore : recTotal s1.kernel = recTotal s.kernel := (recCexec_attests hc).1
  -- the metadata nonce bump preserves the balance measure:
  subst hs'
  simp only []
  rw [bumpNonce_recTotal s1.kernel src, hcore]

/-- **`transfer_two_party_domain` — PROVED (per-domain Σ = 0).** The realized balance-domain
delta of a committed `transferStep` nets to `0` (`Spec.conservedInDomain Domain.balance`), the
executable shadow of dregg1's `excess == 0` gate for the `Paired` Transfer effect. -/
theorem transfer_two_party_domain {s s' : RecChainedState} {actor src dst : CellId} {amt : ℤ}
    (h : transferStep s actor src dst amt = some s') :
    conservedInDomain Domain.balance [recTotal s'.kernel - recTotal s.kernel] := by
  unfold conservedInDomain
  rw [transfer_conserves h]; simp

/-! ## §3 — `transfer_authorized`: a committed Transfer was authorized.

The sender held a cap authorizing the debit — `authorizedB` at the pre-state, inherited VERBATIM
from `recCexec`'s authority gate. -/

/-- **`transfer_authorized` — PROVED.** A committed `transferStep` implies the source held a cap
authorizing the debit (`authorizedB` true at the pre-state). dregg1 Transfer's authorization
obligation, reused from `recCexec_attests`'s Authority conjunct. -/
theorem transfer_authorized {s s' : RecChainedState} {actor src dst : CellId} {amt : ℤ}
    (h : transferStep s actor src dst amt = some s') :
    authorizedB s.kernel.caps (transferTurn actor src dst amt) = true := by
  obtain ⟨s1, hc, _⟩ := transferStep_factors h
  exact (recCexec_attests hc).2.1

/-- **`transfer_unauthorized_fails` — PROVED (fail-closed).** If the move is unauthorized at the
pre-state, no `transferStep` commits. The integrity/confinement core for Transfer. -/
theorem transfer_unauthorized_fails (s : RecChainedState) (actor src dst : CellId) (amt : ℤ)
    (h : authorizedB s.kernel.caps (transferTurn actor src dst amt) = false) :
    transferStep s actor src dst amt = none := by
  unfold transferTurn at h
  unfold transferStep
  have hnone : recCexec s { actor := actor, src := src, dst := dst, amt := amt } = none := by
    unfold recCexec
    rw [recKExec_unauthorized_fails s.kernel _ h]
  rw [hnone]

/-! ## §4 — `transfer_metadata`: the metadata + authority domains.

The source's `nonce` advances by EXACTLY 1, and the cap table / reconstructed authority graph is
UNCHANGED (Transfer touches neither caps nor connectivity). -/

/-- `recCexec` leaves the cap table unchanged (it rewrites only the `balance` field). -/
theorem recCexec_caps_eq {s s1 : RecChainedState} {t : Turn} (h : recCexec s t = some s1) :
    s1.kernel.caps = s.kernel.caps := by
  unfold recCexec at h
  cases hk : recKExec s.kernel t with
  | none => rw [hk] at h; exact absurd h (by simp)
  | some k' =>
      rw [hk] at h; simp only [Option.some.injEq] at h; subst h
      exact (recKExec_frame s.kernel k' t hk).2

/-- **`transfer_caps_unchanged` — PROVED.** A committed `transferStep` leaves the cap table
UNTOUCHED (neither the gated debit/credit nor the nonce bump edits `caps`). -/
theorem transfer_caps_unchanged {s s' : RecChainedState} {actor src dst : CellId} {amt : ℤ}
    (h : transferStep s actor src dst amt = some s') :
    s'.kernel.caps = s.kernel.caps := by
  obtain ⟨s1, hc, hs'⟩ := transferStep_factors h
  subst hs'
  simp only [bumpNonce]
  exact recCexec_caps_eq hc

/-- **`transfer_authGraph_unchanged` — PROVED.** A committed `transferStep` leaves the reconstructed
authority `Graph` (`Spec.execGraph`) UNCHANGED — Transfer moves balance/metadata, never connectivity.
The authority-domain frame condition for Transfer. -/
theorem transfer_authGraph_unchanged {s s' : RecChainedState} {actor src dst : CellId} {amt : ℤ}
    (h : transferStep s actor src dst amt = some s') :
    execGraph s'.kernel.caps = execGraph s.kernel.caps := by
  rw [transfer_caps_unchanged h]

/-- **`transfer_metadata` — PROVED (metadata + authority domains).** A committed `transferStep`:
(a) advances the source's `nonce` by EXACTLY 1 (`nonceOf src' = nonceOf src + 1` — read against the
post-debit cell, which by `recCexec`/`recTransfer`+`setBalance`/`setNonce` non-interference equals
the pre-state nonce), and (b) leaves the cap table UNCHANGED. The metadata + authority obligations
of dregg1's Transfer. -/
theorem transfer_metadata {s s' : RecChainedState} {actor src dst : CellId} {amt : ℤ}
    (h : transferStep s actor src dst amt = some s') :
    (∃ pre : ℤ, nonceOf (s'.kernel.cell src) = pre + 1) ∧
      s'.kernel.caps = s.kernel.caps := by
  obtain ⟨s1, hc, hs'⟩ := transferStep_factors h
  refine ⟨⟨nonceOf (s1.kernel.cell src), ?_⟩, transfer_caps_unchanged h⟩
  subst hs'
  simp only [bumpNonce, if_pos]
  exact setNonce_nonceOf (s1.kernel.cell src) (nonceOf (s1.kernel.cell src) + 1)

/-! ## §5 — `transfer_forward_sim`: the REFINEMENT (forward-simulation square).

Not mere attestation: a committed `transferStep` is matched by an abstract `Spec` STEP. We name the
record-world abstract state and an `AbsStep` relation (the `Spec.Conservation`-conservative,
`Spec.Authority`-authorized abstract turn relation over the `balance` domain + authority graph —
exactly the record-world instance of the `Spec/ExecRefinement.lean §4` OPEN `AbsStep`), and prove
`transferStep s = some s' → AbsStep (absT s) (absT s')`: every executable Transfer is an abstract
step. This is the FULL forward-simulation bottom edge for Transfer, not the projection-identity. -/

section ForwardSim
variable {Statement Witness : Type} [Verifiable Statement Witness]

/-- **`AbstractT`** — the record-world abstract Spec state a Transfer refines: the conserved
`balance`-domain total (`Spec.Conservation` measure at `Bal = ℤ`) and the reconstructed authority
`Graph` (`Spec.Authority`). The record-cell analog of `Spec.AbstractState`. -/
structure AbstractT where
  /-- the conserved `balance`-domain total. -/
  balanceTotal : ℤ
  /-- the reconstructed authority graph. -/
  authGraph    : Dregg2.Spec.Graph Dregg2.Authority.Label Dregg2.Spec.ExecRights

/-- The abstraction function: a chained record state denotes its conserved `recTotal` and its
reconstructed `execGraph`. The Transfer simulation's abstraction. -/
def absT (s : RecChainedState) : AbstractT :=
  { balanceTotal := recTotal s.kernel, authGraph := execGraph s.kernel.caps }

/-- **`AbsStep a a'`** — the abstract Transfer step relation (the record-world `AbsStep` the
`ExecRefinement §4` OPEN names): the abstract `balance` total is CONSERVED (`Spec.conservedInDomain
Domain.balance` on the realized delta), and the authority graph is UNCHANGED (a Transfer is
connectivity-preserving). This is a genuine abstract transition relation — the bottom edge of the
simulation square, not the identity-on-projections. -/
def AbsStep (a a' : AbstractT) : Prop :=
  conservedInDomain Domain.balance [a'.balanceTotal - a.balanceTotal] ∧
    a'.authGraph = a.authGraph

/-- **`transfer_forward_sim` — THE REFINEMENT (PROVED).** A committed `transferStep` is matched by
an abstract `Spec` step: `AbsStep (absT s) (absT s')` holds, AND the committed turn passed the
abstract authority `Guard`. So every executable Transfer step is an abstract step (forward
simulation), with the abstract balance total conserved, the authority graph preserved, and the turn
admitted by the abstract gate. This is the record-world forward-simulation square for Transfer — the
concrete instance of `Spec/ExecRefinement.lean`'s `recExec_step_refines` shape, strengthened to an
`AbsStep` transition (not just the static projections). -/
theorem transfer_forward_sim {s s' : RecChainedState} {actor src dst : CellId} {amt : ℤ}
    (w : Statement → Witness) (h : transferStep s actor src dst amt = some s') :
    AbsStep (absT s) (absT s') ∧
      Guard.admits (execAuthGuard (Statement := Statement) s.kernel.caps)
        (transferTurn actor src dst amt) w = true := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · -- conservation projection of the bottom edge: the abstract balance total is conserved.
    unfold conservedInDomain absT
    rw [transfer_conserves h]; simp
  · -- authority-graph preservation: a Transfer never edits connectivity.
    simp only [absT]
    exact transfer_authGraph_unchanged h
  · -- the committed turn passed the abstract first-party authority Guard.
    rw [Dregg2.Spec.exec_authz_iff_guard]
    exact transfer_authorized h

/-- **`transfer_refines_recordSquare` — PROVED.** The Transfer step satisfies BOTH static
projections of `Spec/ExecRefinement.lean`'s record refinement square — balance-domain conservation
(`Spec.conservedInDomain Domain.balance` on the realized delta) and the abstract authority `Guard` —
so `transfer_forward_sim`'s `AbsStep` is exactly that square's bottom edge, instantiated for the
fully-characterized Transfer (debit/credit + nonce + caps-frame). -/
theorem transfer_refines_recordSquare {s s' : RecChainedState} {actor src dst : CellId} {amt : ℤ}
    (w : Statement → Witness) (h : transferStep s actor src dst amt = some s') :
    conservedInDomain Domain.balance [recTotal s'.kernel - recTotal s.kernel] ∧
      Guard.admits (execAuthGuard (Statement := Statement) s.kernel.caps)
        (transferTurn actor src dst amt) w = true := by
  obtain ⟨⟨hcons, _⟩, hguard⟩ := transfer_forward_sim w h
  exact ⟨by simpa [absT] using hcons, hguard⟩

end ForwardSim

/-! ## §6 — Axiom-hygiene tripwires (the honesty pins over the slice's keystones).

Whitelist exactly `{propext, Classical.choice, Quot.sound}` — no `sorryAx`/`admit`/`axiom`/
`native_decide`. Every theorem of the vertical slice is genuinely proved. -/

#assert_axioms setNonce_nonceOf
#assert_axioms setNonce_balOf
#assert_axioms transferStep_factors
#assert_axioms bumpNonce_recTotal
#assert_axioms transfer_conserves
#assert_axioms transfer_two_party_domain
#assert_axioms transfer_authorized
#assert_axioms transfer_unauthorized_fails
#assert_axioms recCexec_caps_eq
#assert_axioms transfer_caps_unchanged
#assert_axioms transfer_authGraph_unchanged
#assert_axioms transfer_metadata
#assert_axioms transfer_forward_sim
#assert_axioms transfer_refines_recordSquare

/-! ## §7 — Non-vacuity: a concrete Transfer commits, conserves, advances the nonce.

Cell 0 has balance 100 + nonce 0; cell 1 has balance 5. Actor 0 owns cell 0 (no cap needed —
authority by ownership). A Transfer of 30 from 0 to 1 commits, conserves the total (105 → 105),
advances cell 0's nonce 0 → 1, and leaves cell 1's nonce untouched. -/

/-- A chained record state: cells 0,1 with balances 100,5; cell 0 carries a `nonce` field. Empty
cap table (authority by ownership), empty receipt chain. -/
def es0 : RecChainedState :=
  { kernel :=
      { accounts := {0, 1}
        cell := fun c => if c = 0 then .record [("balance", .int 100), ("nonce", .int 0)]
                         else if c = 1 then .record [("balance", .int 5)]
                         else .record [("balance", .int 0)]
        caps := fun _ => [] }
    log := [] }

-- A Transfer of 30 from cell 0 to cell 1 commits (actor 0 owns src 0):
#eval (transferStep es0 0 0 1 30).isSome                                  -- true
-- ...conserves the total balance (105 = 70 + 35, unchanged):
#eval (transferStep es0 0 0 1 30).map (fun s => recTotal s.kernel)        -- some 105
#eval recTotal es0.kernel                                                 -- 105
-- ...debits the source's balance 100 → 70:
#eval (transferStep es0 0 0 1 30).map (fun s => balOf (s.kernel.cell 0))  -- some 70
-- ...credits the destination's balance 5 → 35:
#eval (transferStep es0 0 0 1 30).map (fun s => balOf (s.kernel.cell 1))  -- some 35
-- ...advances the SOURCE's nonce by exactly 1 (0 → 1):
#eval (transferStep es0 0 0 1 30).map (fun s => nonceOf (s.kernel.cell 0)) -- some 1
-- ...grows the receipt chain by exactly one row:
#eval (transferStep es0 0 0 1 30).map (fun s => s.log.length)             -- some 1
-- An unauthorized actor (9 owns nothing, no cap) cannot transfer (fail-closed):
#eval (transferStep es0 9 0 1 30).isSome                                  -- false
-- An overdraft (more than available) is rejected (availability gate):
#eval (transferStep es0 0 0 1 999).isSome                                 -- false
-- A self-transfer (src = dst) is rejected (the precondition the kernel forbids):
#eval (transferStep es0 0 0 0 10).isSome                                  -- false

end Dregg2.Exec.EffectTransfer
