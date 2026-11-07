/-
# Dregg2.Circuit.Emit.EffectVmEmitBridge — the FAITHFUL-ENCODING bridge for the TRANSFER row.

`EffectVmEmitTransfer.transferVm_faithful` proves the emitted gates accept a row IFF the
ROW-level `TransferRowIntent` holds. `Spec.CircuitSpecTriangle.transfer_circuit_pins_intent`
proves the ABSTRACT circuit pins the kernel transfer `intentTransfer`/`recTransferBal` over
`RecordKernelState`. The amplification-worklist §5 finding #1 flags these as TWO UNBRIDGED
proof layers: nothing proves the 186-column row IS a faithful encoding of the kernel record, so
the per-row faithfulness does NOT inherit the abstract intent guarantee.

This module builds that bridge for TRANSFER. It defines a faithful-encoding relation
`RowEncodes env pre post a actor amt dir` pinning the row's columns to the actual kernel fields of
an abstract record transition, and proves the HEADLINE biconditional + the END-TO-END composition
with `transferVm_faithful`:

    the EMITTED gates accept the row  ⟺  the encoded kernel transition is the correct
    protocol transfer of the actor's ledger column.

## What the row PINS vs what it does NOT (the boundary)

The EffectVM transfer row carries ONE cell's balance as a single `bal_lo` limb (the ACTOR cell),
the actor's nonce, the transfer `amount`/`direction`, and the frozen frame. `recKExecAsset` /
`recTransferBal` move a 2-CELL, ASSET-INDEXED ledger (`bal : CellId → AssetId → ℤ`): debit
`src` column `a`, credit `dst` column `a`. So the row faithfully encodes **the actor cell's own
asset-`a` column move** (`direction = 1` ⟹ actor is `src`, debited; `direction = 0` ⟹ actor is
`dst`, credited), and the bridge pins EXACTLY that.

  * PINS (the bridge proves these, both directions): the actor's `bal actor a` entry moves by
    `actorDelta amt dir = amt·(1 - 2·dir)`, i.e. the actor's side of `recTransferBal` (debit if
    src, credit if dst); `dir` is a bit. Via the END-TO-END composition the EMITTED GATES enforce
    exactly this.
  * ALSO PINNED at the row (carried as encoding conditions because the row has these
    columns): the actor's nonce ticks by one; the actor's `bal_hi` + cap_root + reserved + 8
    fields are frozen — the honest shape of a transfer encoding.
  * DOES NOT PIN (out of the row's witness — these live in the abstract layer / turn root):
      - the COUNTERPARTY cell's column (the row carries only the actor's limb, not `dst`/`src`'s);
      - the ASSET INDEX `a` distinguishing `bal · a` from `bal · b` (the row's `bal_lo` is a bare
        limb; which asset column it is comes from the encoding choice, not a row gate);
      - the AUTHORIZATION / availability / liveness GUARD of `recKExecAsset` (`authorizedB`,
        `0 ≤ amt ≤ bal src a`, `src ∈ accounts`) — the row has no cap-graph columns;
      - the cap-graph, nullifier set, escrow store contents (frozen `cap_root` HASH only).

So this is an HONEST PARTIAL bridge with a precise boundary: it pins the actor's single-column
ledger move (the part the row witnesses) + the honest frame-freeze/nonce-tick, and is
explicit that the counterparty/asset-index/guard are NOT row-level. This respects worklist finding
#2 (no overclaiming set-membership/uniqueness) — transfer is a pure balance-delta, so the part the
row DOES carry bridges cleanly and TOTALLY (both directions) to the abstract actor-column move.
-/
import Dregg2.Circuit.Emit.EffectVmEmitTransfer
import Dregg2.Exec.RecordKernel

namespace Dregg2.Circuit.Emit.EffectVmEmitBridge

open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransfer
open Dregg2.Exec (RecordKernelState Turn CellId AssetId recKExecAsset recTransferBal)

set_option linter.unusedVariables false

/-! ## §1 — The abstract actor-column move.

The actor's side of `recTransferBal`: cell `actor`'s asset-`a` column moves by the signed amount.
`direction = 1` ⟹ actor is the debited `src` (`- amt`); `direction = 0` ⟹ actor is the credited
`dst` (`+ amt`). This is the EXACT projection of `recTransferBal` onto the actor's `(actor, a)`
entry (proved by `recTransferBal_src`/`_dst`). -/

/-- **`actorDelta amt dir`** — the signed amount applied to the actor's column: `amt·(1 - 2·dir)`.
`dir = 1` ⟹ `-amt` (debit); `dir = 0` ⟹ `+amt` (credit). -/
def actorDelta (amt dir : ℤ) : ℤ := amt * (1 - 2 * dir)

/-- Field-denotation glue for the bridge: under the DEPLOYED canonicality envelope (`0 ≤ · < p`,
the range-check invariant), a mod-`p` congruence between two canonical integers COLLAPSES to ℤ
equality — the residual lies in `(−p, p)`, so `p ∣ residual` forces it to 0. This is how the
mod-`p` `TransferRowIntent` clauses reach the ℤ-level kernel ledger statement. -/
theorem canon_modEq_eq {a b : ℤ} (ha : 0 ≤ a ∧ a < 2013265921) (hb : 0 ≤ b ∧ b < 2013265921)
    (h : a ≡ b [ZMOD 2013265921]) : a = b := by
  by_contra hne
  exact not_modEq_zero_of_canon (x := a - b) rfl ha hb hne ((gate_modEq_iff rfl).mpr h)

/-- **`AbstractTransferActorMove pre post a actor amt dir`** — the abstract kernel statement the
row claims to encode: cell `actor`'s asset-`a` ledger column in `post` is its `pre` value moved by
the signed amount, and `dir` is a bit. This is the actor-column projection of the abstract transfer
`recTransferBal` (NOT the whole 2-cell move — the row only witnesses the actor's column). -/
def AbstractTransferActorMove (pre post : RecordKernelState) (a : AssetId) (actor : CellId)
    (amt dir : ℤ) : Prop :=
  (dir = 0 ∨ dir = 1) ∧ post.bal actor a = pre.bal actor a + actorDelta amt dir

/-- `recTransferBal` projected onto the DEBITED source's column: `src`'s asset-`a` entry drops by
`amt` (and `src ≠ dst` so the credit branch misses it). This is `actorDelta amt 1`. -/
theorem recTransferBal_src (bal : CellId → AssetId → ℤ) (src dst : CellId)
    (a : AssetId) (amt : ℤ) (hne : src ≠ dst) :
    recTransferBal bal src dst a amt src a = bal src a + actorDelta amt 1 := by
  unfold recTransferBal actorDelta
  simp only [if_true]
  ring

/-- `recTransferBal` projected onto the CREDITED destination's column: `dst`'s asset-`a` entry
rises by `amt` (and `src ≠ dst` so the debit branch misses it). This is `actorDelta amt 0`. -/
theorem recTransferBal_dst (bal : CellId → AssetId → ℤ) (src dst : CellId)
    (a : AssetId) (amt : ℤ) (hne : src ≠ dst) :
    recTransferBal bal src dst a amt dst a = bal dst a + actorDelta amt 0 := by
  unfold recTransferBal actorDelta
  have hd : ¬ dst = src := fun h => hne h.symm
  simp only [if_true, if_neg hd]
  ring

/-! ## §2 — The faithful-encoding relation `RowEncodes`.

`RowEncodes env pre post a actor amt dir` says: the row `env` is the HONEST encoding of the
abstract transfer transition that moves cell `actor`'s asset-`a` column from `pre.bal actor a` to
`post.bal actor a`, with the row's `direction` = `dir` and `amount` = `amt`. It pins the row's
columns to the kernel fields the row carries.

The encoding is INJECTIVE on what it claims: distinct `(pre.bal actor a, post.bal actor a)` give
distinct row `bal_lo` columns, and tampering `post.bal actor a` away from the move breaks the
equivalence (the anti-ghost tooth, §4). It does NOT claim the row carries the counterparty/asset/
guard — those are not fields of `RowEncodes`. -/

/-- **`RowEncodes env pre post a actor amt dir`** — the row faithfully encodes the actor-column
transfer transition. The row's `bal_lo` carries the integer ledger value `bal actor a` (pre and
post), `amount`/`direction` carry the move magnitude/sign, the actor's nonce ticks, and
`bal_hi`/frame are frozen (the honest shape of a transfer encoding). -/
structure RowEncodes (env : VmRowEnv) (pre post : RecordKernelState) (a : AssetId) (actor : CellId)
    (amt dir : ℤ) : Prop where
  /-- The row is a genuine transfer row (`s_transfer = 1`, `s_noop = 0`). -/
  isRow   : IsTransferRow env
  /-- The row's pre `bal_lo` IS the actor's asset-`a` ledger value before. -/
  preBal  : env.loc (sbCol state.BALANCE_LO) = pre.bal actor a
  /-- The row's post `bal_lo` IS the actor's asset-`a` ledger value after. -/
  postBal : env.loc (saCol state.BALANCE_LO) = post.bal actor a
  /-- The row's `amount` param IS the move amount. -/
  amount  : env.loc (prmCol param.AMOUNT) = amt
  /-- The row's `direction` param IS `dir`. -/
  dirBit  : env.loc (prmCol param.DIRECTION) = dir
  /-- `bal_hi` is frozen: the move stays in the lo limb (the integer value = the lo limb). -/
  hiFix   : env.loc (saCol state.BALANCE_HI) = env.loc (sbCol state.BALANCE_HI)
  /-- The actor's nonce ticks by one (the honest transfer nonce bump). -/
  nonce   : env.loc (saCol state.NONCE) = env.loc (sbCol state.NONCE) + 1
  /-- The actor's `cap_root` is frozen. -/
  capFix  : env.loc (saCol state.CAP_ROOT) = env.loc (sbCol state.CAP_ROOT)
  /-- The actor's `reserved` flag-word is frozen. -/
  resFix  : env.loc (saCol state.RESERVED) = env.loc (sbCol state.RESERVED)
  /-- The actor's 8 content fields are frozen. -/
  fldFix  : ∀ i < 8, env.loc (saCol (state.FIELD_BASE + i)) = env.loc (sbCol (state.FIELD_BASE + i))

/-! ## §3 — THE BRIDGE: row-intent ⟺ abstract actor-column move.

The headline. On a faithful encoding, the row-level `TransferRowIntent` holds IFF the abstract
actor-column move `AbstractTransferActorMove` holds. The row-intent's balance/direction clauses
translate, through the encoding's column pins, EXACTLY into the abstract ledger statement; the
hi/nonce/frame clauses are CARRIED by the encoding (they are the honest transfer shape), so the
biconditional is clean in BOTH directions. -/

/-- **`bridge_abstract_to_rowIntent` — the UNCONDITIONAL direction.** An honest encoding of a
genuine abstract actor-column move satisfies the FIELD-level `TransferRowIntent`: every ℤ equality
the encoding + abstract move pin lifts to a mod-`p` congruence (`eqToModEq`) — no canonicality
needed to go FROM kernel truth INTO the field. -/
theorem bridge_abstract_to_rowIntent
    (env : VmRowEnv) (pre post : RecordKernelState) (a : AssetId) (actor : CellId) (amt dir : ℤ)
    (henc : RowEncodes env pre post a actor amt dir)
    (habs : AbstractTransferActorMove pre post a actor amt dir) :
    TransferRowIntent env := by
  obtain ⟨_isRow, hpre, hpost, hamt, hdir, hhi, hnon, hcap, hres, hfld⟩ := henc
  obtain ⟨hbit, hmove⟩ := habs
  simp only [actorDelta] at hmove
  unfold TransferRowIntent
  refine ⟨?_, ?_, eqToModEq hhi, eqToModEq hnon, eqToModEq hcap, eqToModEq hres,
    fun i hi => eqToModEq (hfld i hi)⟩
  · rw [hdir]
    rcases hbit with h | h
    · exact Or.inl (eqToModEq h)
    · exact Or.inr (eqToModEq h)
  · rw [hpost, hpre, hamt, hdir]
    exact eqToModEq (by linarith [hmove])

/-- **`bridge_rowIntent_iff_abstract` — THE BRIDGE.** On a row that faithfully encodes the
actor-column transfer transition, the EMITTED row-intent `TransferRowIntent env` holds iff the
ABSTRACT actor-column move `AbstractTransferActorMove pre post a actor amt dir` holds. The two
proof layers MEET at the encoding: the row's `bal_lo`/`direction`/`amount` columns ARE the actor's
ledger value / direction / amount, so the row's balance-move clause IS the abstract ledger move.

FIELD-FAITHFUL: `TransferRowIntent` is now mod-`p` congruences, so the FORWARD direction (field
gates → ℤ kernel move) needs the DEPLOYED canonicality envelope — the direction bit, the post
ledger value, and the intended moved value each lie in `[0, p)` (the range-check invariant + the
no-overflow move). Under it a field congruence between canonical values collapses to ℤ equality
(`canon_modEq_eq`), so NO wrap-around forgery survives. The backward direction stays unconditional
(`bridge_abstract_to_rowIntent`). -/
theorem bridge_rowIntent_iff_abstract
    (env : VmRowEnv) (pre post : RecordKernelState) (a : AssetId) (actor : CellId) (amt dir : ℤ)
    (henc : RowEncodes env pre post a actor amt dir)
    (hcanonDir : 0 ≤ dir ∧ dir < 2013265921)
    (hcanonPost : 0 ≤ post.bal actor a ∧ post.bal actor a < 2013265921)
    (hcanonMove : 0 ≤ pre.bal actor a + actorDelta amt dir
      ∧ pre.bal actor a + actorDelta amt dir < 2013265921) :
    TransferRowIntent env ↔ AbstractTransferActorMove pre post a actor amt dir := by
  simp only [actorDelta] at hcanonMove
  constructor
  · obtain ⟨_isRow, hpre, hpost, hamt, hdir, hhi, hnon, hcap, hres, hfld⟩ := henc
    unfold TransferRowIntent AbstractTransferActorMove actorDelta
    rintro ⟨hbit, hmove, _, _, _, _, _⟩
    rw [hdir] at hbit
    rw [hpost, hpre, hamt, hdir] at hmove
    refine ⟨?_, canon_modEq_eq hcanonPost hcanonMove hmove⟩
    rcases hbit with h0 | h1
    · exact Or.inl (canon_modEq_eq hcanonDir (by norm_num) h0)
    · exact Or.inr (canon_modEq_eq hcanonDir (by norm_num) h1)
  · exact bridge_abstract_to_rowIntent env pre post a actor amt dir henc

/-! ## §4 — END-TO-END: the EMITTED GATES accept the row ⟺ the correct protocol transfer.

Compose the bridge with `EffectVmEmitTransfer.transferVm_faithful`
(emitted gates ⟺ `TransferRowIntent`). The result is the load-bearing statement of the whole
campaign: on a faithfully-encoded transfer row, the EMITTED descriptor's per-row gates accept the
row IFF the encoded kernel transition is the correct protocol transfer of the actor's ledger
column. THAT is "the emitted circuit enforces the protocol effect." -/

/-- **`emittedGates_iff_protocolTransfer` — THE END-TO-END THEOREM.** On a row that faithfully
encodes the actor-column transfer transition (`RowEncodes`), the EMITTED descriptor's per-row gates
(`transferRowGates`, the term-for-term mirror of the running prover's transfer polynomials) ALL
hold IFF the abstract kernel statement `AbstractTransferActorMove pre post a actor amt dir` holds —
i.e. the actor's `bal actor a` column moves by exactly `recTransferBal`'s signed delta. The two
proof layers (row-faithfulness + abstract-encoding) are now BRIDGED for transfer. FIELD-FAITHFUL:
the gates→kernel direction carries the deployed canonicality envelope (see
`bridge_rowIntent_iff_abstract`); kernel→gates stays unconditional. -/
theorem emittedGates_iff_protocolTransfer
    (env : VmRowEnv) (pre post : RecordKernelState) (a : AssetId) (actor : CellId) (amt dir : ℤ)
    (henc : RowEncodes env pre post a actor amt dir)
    (hcanonDir : 0 ≤ dir ∧ dir < 2013265921)
    (hcanonPost : 0 ≤ post.bal actor a ∧ post.bal actor a < 2013265921)
    (hcanonMove : 0 ≤ pre.bal actor a + actorDelta amt dir
      ∧ pre.bal actor a + actorDelta amt dir < 2013265921) :
    (∀ c ∈ transferRowGates, c.holdsVm env false false)
      ↔ AbstractTransferActorMove pre post a actor amt dir := by
  rw [transferVm_faithful env henc.isRow]
  exact bridge_rowIntent_iff_abstract env pre post a actor amt dir henc
    hcanonDir hcanonPost hcanonMove

/-- **`emittedGates_realize_recTransferBal_src` — the SOURCE specialization.** When the actor is the
DEBITED `src` of an abstract transfer `recKExecAsset`-style move (so `dir = 1`, `src ≠ dst`, and
`post.bal src a = recTransferBal pre.bal src dst a amt src a`), the emitted gates accept the row IFF
the row carries it. The abstract `recTransferBal`-on-`src` IS `actorDelta amt 1`, so the emitted
circuit enforces the EXACT source debit. -/
theorem emittedGates_realize_recTransferBal_src
    (env : VmRowEnv) (pre post : RecordKernelState) (a : AssetId) (src dst : CellId) (amt : ℤ)
    (hne : src ≠ dst)
    (hmoved : post.bal src a = recTransferBal pre.bal src dst a amt src a)
    (henc : RowEncodes env pre post a src amt 1) :
    (∀ c ∈ transferRowGates, c.holdsVm env false false) := by
  refine (transferVm_faithful env henc.isRow).mpr
    (bridge_abstract_to_rowIntent env pre post a src amt 1 henc ⟨Or.inr rfl, ?_⟩)
  rw [hmoved, recTransferBal_src pre.bal src dst a amt hne]

/-! ## §5 — ANTI-GHOST: tampering the actor's post-ledger entry breaks acceptance.

Two teeth. (a) If the encoded `post.bal actor a` is NOT the correct signed move, then the emitted
gates REJECT the row (`gBalLo` UNSAT) — a forged post-ledger cannot pass. (b) A concrete tampered
witness: a debit-30 transfer whose post-ledger is forged to a wrong value has no satisfying gate set.

This is the conservation-≠-correctness anti-ghost: the row pins the WHOLE actor-column transition
it claims; you cannot credit/debit a different amount than the move and still satisfy the gate. -/

/-- **Anti-ghost (general).** On a faithful encoding, if the actor's post-ledger entry is NOT the
signed move (`post.bal actor a ≠ pre.bal actor a + actorDelta amt dir`), the emitted per-row gates
have NO satisfying assignment for the row — the encoded forgery is UNSAT. FIELD-FAITHFUL: the tooth
rejects a field-`≢` output, so it needs the DEPLOYED canonicality envelope on the post ledger value
and the intended moved value (both in `[0, p)`): a canonical forgery differs from the intended
value by less than `p`, so it cannot pass the field gate by wrap-around. No direction envelope is
needed — the forgery is stated against the raw signed delta. -/
theorem antiGhost_wrong_postLedger
    (env : VmRowEnv) (pre post : RecordKernelState) (a : AssetId) (actor : CellId) (amt dir : ℤ)
    (henc : RowEncodes env pre post a actor amt dir)
    (hcanonPost : 0 ≤ post.bal actor a ∧ post.bal actor a < 2013265921)
    (hcanonMove : 0 ≤ pre.bal actor a + actorDelta amt dir
      ∧ pre.bal actor a + actorDelta amt dir < 2013265921)
    (hforge : post.bal actor a ≠ pre.bal actor a + actorDelta amt dir) :
    ¬ (∀ c ∈ transferRowGates, c.holdsVm env false false) := by
  intro hgates
  simp only [actorDelta] at hcanonMove hforge
  have hintent := (transferVm_faithful env henc.isRow).mp hgates
  obtain ⟨-, hmove, -, -, -, -, -⟩ := hintent
  rw [henc.postBal, henc.preBal, henc.amount, henc.dirBit] at hmove
  exact hforge (canon_modEq_eq hcanonPost hcanonMove hmove)

/-- A concrete FORGED-LEDGER witness: `pre`/`post` record states whose ledgers put the actor cell
(`actor = 0`, asset `0`) at `100 → 70`, encoded by `goodRow` (debit 30, `dir = 1`); then a tampered
`postBad` whose actor entry is forged to `999 ≠ 70`. The encoding of `postBad` by `goodRow` is then
NON-faithful exactly at the post-ledger pin, and `goodRow`'s gates accept ONLY the genuine `70`. -/
def preWit : RecordKernelState :=
  { accounts := ∅, cell := fun _ => default, caps := default
  , bal := fun c a => if c = 0 ∧ a = 0 then 100 else 0 }

def postWit : RecordKernelState :=
  { accounts := ∅, cell := fun _ => default, caps := default
  , bal := fun c a => if c = 0 ∧ a = 0 then 70 else 0 }

def postBad : RecordKernelState :=
  { accounts := ∅, cell := fun _ => default, caps := default
  , bal := fun c a => if c = 0 ∧ a = 0 then 999 else 0 }

/-- `goodRow` faithfully encodes the GENUINE transfer transition `preWit → postWit` of the actor
cell `0`'s asset-`0` column (`100 → 70`, debit 30, `dir = 1`). So the bridge applies and the gates
accept it. (Witnesses TRUE.) -/
theorem goodRow_encodes_genuine : RowEncodes goodRow preWit postWit 0 0 30 1 := by
  have unfoldCols : ∀ (off : Nat),
      (sbCol off = 54 + off) ∧ (saCol off = 76 + off) ∧ (prmCol off = 68 + off) := by
    intro off
    refine ⟨?_, ?_, ?_⟩ <;>
      · simp only [sbCol, saCol, prmCol, STATE_BEFORE_BASE, STATE_AFTER_BASE, PARAM_BASE,
          NUM_EFFECTS, STATE_SIZE, NUM_PARAMS]
  refine ⟨goodRow_isTransferRow, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- sb bal_lo (col 54) = 100 = preWit.bal 0 0
    show goodRow.loc (sbCol state.BALANCE_LO) = preWit.bal 0 0
    rw [(unfoldCols state.BALANCE_LO).1]; rfl
  · -- sa bal_lo (col 76) = 70 = postWit.bal 0 0
    show goodRow.loc (saCol state.BALANCE_LO) = postWit.bal 0 0
    rw [(unfoldCols state.BALANCE_LO).2.1]; rfl
  · -- amount param (col 68) = 30
    show goodRow.loc (prmCol param.AMOUNT) = 30
    rw [(unfoldCols param.AMOUNT).2.2]; rfl
  · -- direction param (col 69) = 1
    show goodRow.loc (prmCol param.DIRECTION) = 1
    rw [(unfoldCols param.DIRECTION).2.2]; rfl
  · -- bal_hi frozen: sa bal_hi (77) = sb bal_hi (55); both miss every named col ⟹ 0 = 0
    show goodRow.loc (saCol state.BALANCE_HI) = goodRow.loc (sbCol state.BALANCE_HI)
    rw [(unfoldCols state.BALANCE_HI).2.1, (unfoldCols state.BALANCE_HI).1]; rfl
  · -- nonce: sa nonce (78) = sb nonce (56) + 1, i.e. 6 = 5 + 1
    show goodRow.loc (saCol state.NONCE) = goodRow.loc (sbCol state.NONCE) + 1
    rw [(unfoldCols state.NONCE).2.1, (unfoldCols state.NONCE).1]; rfl
  · -- cap_root frozen: sa cap_root (87) = sb cap_root (65); both 0
    show goodRow.loc (saCol state.CAP_ROOT) = goodRow.loc (sbCol state.CAP_ROOT)
    rw [(unfoldCols state.CAP_ROOT).2.1, (unfoldCols state.CAP_ROOT).1]; rfl
  · -- reserved frozen: sa reserved (89) = sb reserved (67); both 0
    show goodRow.loc (saCol state.RESERVED) = goodRow.loc (sbCol state.RESERVED)
    rw [(unfoldCols state.RESERVED).2.1, (unfoldCols state.RESERVED).1]; rfl
  · -- 8 fields frozen: sa field[i] (79+i) = sb field[i] (57+i); both miss every named col ⟹ 0
    intro i hi
    show goodRow.loc (saCol (state.FIELD_BASE + i)) = goodRow.loc (sbCol (state.FIELD_BASE + i))
    rw [(unfoldCols (state.FIELD_BASE + i)).2.1, (unfoldCols (state.FIELD_BASE + i)).1]
    show (if (76 + (state.FIELD_BASE + i)) = sel.TRANSFER then (1 : ℤ) else _) = _
    simp only [goodRow, sel.TRANSFER, sbCol, saCol, prmCol, STATE_BEFORE_BASE, STATE_AFTER_BASE,
      PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO, state.NONCE,
      state.FIELD_BASE, param.AMOUNT, param.DIRECTION]
    have e1 : ¬ (76 + (3 + i) = 1) := by omega
    have e2 : ¬ (76 + (3 + i) = 54) := by omega
    have e3 : ¬ (76 + (3 + i) = 76) := by omega
    have e4 : ¬ (76 + (3 + i) = 56) := by omega
    have e5 : ¬ (76 + (3 + i) = 78) := by omega
    have e6 : ¬ (76 + (3 + i) = 68) := by omega
    have e7 : ¬ (76 + (3 + i) = 69) := by omega
    have f1 : ¬ (54 + (3 + i) = 1) := by omega
    have f3 : ¬ (54 + (3 + i) = 76) := by omega
    have f4 : ¬ (54 + (3 + i) = 56) := by omega
    have f5 : ¬ (54 + (3 + i) = 78) := by omega
    have f6 : ¬ (54 + (3 + i) = 68) := by omega
    have f7 : ¬ (54 + (3 + i) = 69) := by omega
    have f2 : ¬ (54 + (3 + i) = 54) := by omega
    simp only [e1, e2, e3, e4, e5, e6, e7, f1, f2, f3, f4, f5, f6, f7, ↓reduceIte]

/-- **NON-VACUITY (witness TRUE).** The genuine transition `preWit → postWit` satisfies the abstract
move (the bridge's RHS is inhabited), so `goodRow`'s gates accept it. -/
theorem goodRow_abstract_holds : AbstractTransferActorMove preWit postWit 0 0 30 1 := by
  refine ⟨Or.inr rfl, ?_⟩
  unfold actorDelta preWit postWit
  norm_num

/-- **NON-VACUITY (witness FALSE / concrete anti-ghost).** If we instead claim `goodRow` encodes the
FORGED transition `preWit → postBad` (actor entry `100 → 999`), the post-ledger pin `postBad.bal 0 0
= 999` does NOT match `goodRow`'s `sa bal_lo = 70`, so `goodRow` does NOT faithfully encode it — the
encoding REFUSES the forgery. (The forged ledger is unreachable by the genuine row.) -/
theorem goodRow_refuses_forged_ledger :
    ¬ RowEncodes goodRow preWit postBad 0 0 30 1 := by
  intro henc
  have h := henc.postBal
  simp only [goodRow, postBad, sbCol, saCol, prmCol, sel.TRANSFER, STATE_BEFORE_BASE,
    STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO,
    state.NONCE, param.AMOUNT, param.DIRECTION] at h
  -- h : 70 = 999, contradiction.
  norm_num at h

/-! ## §6 — Axiom-hygiene pins (the honesty tripwire). -/

#assert_axioms actorDelta
#assert_axioms recTransferBal_src
#assert_axioms recTransferBal_dst
#assert_axioms canon_modEq_eq
#assert_axioms bridge_abstract_to_rowIntent
#assert_axioms bridge_rowIntent_iff_abstract
#assert_axioms emittedGates_iff_protocolTransfer
#assert_axioms emittedGates_realize_recTransferBal_src
#assert_axioms antiGhost_wrong_postLedger
#assert_axioms goodRow_encodes_genuine
#assert_axioms goodRow_abstract_holds
#assert_axioms goodRow_refuses_forged_ledger

end Dregg2.Circuit.Emit.EffectVmEmitBridge
