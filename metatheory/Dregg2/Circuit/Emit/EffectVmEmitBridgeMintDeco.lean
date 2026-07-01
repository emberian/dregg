/-
# Dregg2.Circuit.Emit.EffectVmEmitBridgeMintDeco — the PAYMENT-FACT PI weld (G1, staged additively).

The deployed `bridgeMintVmDescriptor` pins the ledger credit + the post-state commitment, but leaves the
payment facts (the `mint_hash` commitment at `prmCol 0`, the minted `value` at `prmCol 1`) in the WITNESS,
bound by NO constraint (the FLAG in `EffectVmEmitBridgeMint` §BOUNDARY: "does NOT internalize the bridge
proof in-circuit"). So a pure light client, reading only the public inputs, sees the balance move but not
WHICH payment backs it — the G1 gap (`BridgeBackingAttack.deployed_admits_unbacked_bridge`).

This module closes that gap the way `CapOpenTurnPins` closes the turn-identity gap: **additively**, as a
NEW gated descriptor (`decoBridgeMintVmDescriptor`, its own AIR name ⇒ its own VK — a gated VK epoch, the
deployed descriptor UNTOUCHED). Two appended `.piBinding .first` welds publish the payment commitment and
the minted value to two NEW public-input slots, so a `satisfiedVm` witness FORCES those columns to equal
the light client's PIs on the first row. The DECO relation (`Crypto/Deco.lean`) then certifies the
published commitment opens to a Stripe-authenticated payment (the weld in `Verify/StripeLightClient.lean`).

What is PROVED:
  * `decoBridgeMint_to_base` — a `satisfiedVm` witness of the weld is a `satisfiedVm` witness of the
    deployed base (the pins only ADD constraints; the hash-site/range legs are identical). So every
    deployed keystone lifts verbatim.
  * `decoBridgeMint_full_sound` — the deployed `bridgeMintDescriptor_full_sound` (ledger credit +
    committed post-state) lifts through the weld UNCHANGED.
  * `decoBridgeMint_publishes` — the FIRST row pins `mint_hash`→`PI[piCount]`, `value`→`PI[piCount+1]`:
    the payment commitment + minted value are now PUBLIC INPUTS (they reach the recursive aggregate root).
  * `decoBridgeMint_published_value_is_minted` — the published value PI IS the amount the ledger credits.
  * `decoBridgeMint_rejects_mismatched_commit` — a first row whose `mint_hash` ≠ `PI[piCount]` is UNSAT
    (the weld's tooth): a proof whose committed payment differs from the published one is rejected.

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} + the named carriers of the deployed keystones.
Imports read-only; the deployed `bridgeMintVmDescriptor` is not edited.
-/
import Dregg2.Circuit.Emit.EffectVmEmitBridgeMint

namespace Dregg2.Circuit.Emit.EffectVmEmitBridgeMintDeco

open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitBridgeMint
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound (CellState)

set_option autoImplicit false

/-! ## §1 — the two payment-fact columns + their NEW public-input slots.

The bridge-mint trace lays `param0 = mint_hash` (the Poseidon2 commitment to the payment attestation) and
`param1 = value_lo` (the minted amount). Both already sit in the trace; the weld only PUBLISHES them —
so `traceWidth` is unchanged and no existing column collides. -/

/-- The payment-commitment column (`prmCol 0`, the `mint_hash` the trace-generator lays). -/
def paymentCommitCol : Nat := prmCol 0
/-- The minted-value column (`prmCol 1`, the `value_lo` the credit gate reads). -/
def paymentValueCol : Nat := prmCol param.BRIDGE_MINT_VALUE_LO

/-- The NEW public-input slot for the payment commitment (past the deployed base's 42 PIs). -/
def PI_PAYMENT_COMMIT : Nat := bridgeMintVmDescriptor.piCount
/-- The NEW public-input slot for the minted value. -/
def PI_PAYMENT_VALUE : Nat := bridgeMintVmDescriptor.piCount + 1

/-- The two payment-fact PI pins: weld `mint_hash`→`PI[piCount]`, `value`→`PI[piCount+1]`, on the FIRST
row (`when_first_row()`, the deployed mechanism the commit pins already use). -/
def bridgeMintPaymentPins : List VmConstraint :=
  [ .piBinding .first paymentCommitCol PI_PAYMENT_COMMIT
  , .piBinding .first paymentValueCol PI_PAYMENT_VALUE ]

/-! ## §2 — `decoBridgeMintVmDescriptor`: the deployed descriptor PLUS the payment-fact weld. -/

/-- **`decoBridgeMintVmDescriptor`** — `bridgeMintVmDescriptor` with two NEW PI slots and the two payment
pins appended. A distinct AIR name ⇒ a distinct VK (the gated epoch); every deployed constraint is
preserved (still references the same columns), so every deployed bridge-mint keystone lifts verbatim. -/
def decoBridgeMintVmDescriptor : EffectVmDescriptor :=
  { bridgeMintVmDescriptor with
    name := "dregg-effectvm-bridgemint-deco-v1"
    piCount := bridgeMintVmDescriptor.piCount + 2
    constraints := bridgeMintVmDescriptor.constraints ++ bridgeMintPaymentPins }

/-- The deployed base's constraints are a PREFIX of the weld's. -/
theorem decoBridgeMint_base_prefix (c : VmConstraint)
    (hc : c ∈ bridgeMintVmDescriptor.constraints) :
    c ∈ decoBridgeMintVmDescriptor.constraints :=
  List.mem_append_left _ hc

/-- **`decoBridgeMint_to_base`** — a `satisfiedVm` witness of the weld is a `satisfiedVm` witness of the
deployed base (any row window). The pins only ADD constraints; the hash sites and ranges are identical. -/
theorem decoBridgeMint_to_base (hash : List ℤ → ℤ) (env : VmRowEnv) (isFirst isLast : Bool)
    (hsat : satisfiedVm hash decoBridgeMintVmDescriptor env isFirst isLast) :
    satisfiedVm hash bridgeMintVmDescriptor env isFirst isLast := by
  obtain ⟨hc, hs, hr⟩ := hsat
  refine ⟨fun c hcmem => hc c ?_, hs, hr⟩
  show c ∈ bridgeMintVmDescriptor.constraints ++ bridgeMintPaymentPins
  exact List.mem_append_left _ hcmem

/-- **`decoBridgeMint_full_sound`** — the deployed soundness (ledger credit + committed post-state) lifts
through the weld UNCHANGED: satisfying the weld (both boundary settings) under `RowEncodes` forces
`CellBridgeMintSpec` AND publishes `post.commit = PI[NEW_COMMIT]`. -/
theorem decoBridgeMint_full_sound (hash : List ℤ → ℤ) (env : VmRowEnv) (hrow : IsBridgeMintRow env)
    (pre post : CellState) (value : ℤ) (henc : RowEncodes env pre value post)
    (hgatesat : satisfiedVm hash decoBridgeMintVmDescriptor env true false)
    (hsat : satisfiedVm hash decoBridgeMintVmDescriptor env true true) :
    CellBridgeMintSpec pre value post ∧ post.commit = env.pub pi.NEW_COMMIT :=
  bridgeMintDescriptor_full_sound hash env hrow pre post value henc
    (decoBridgeMint_to_base hash env true false hgatesat)
    (decoBridgeMint_to_base hash env true true hsat)

/-! ## §3 — `decoBridgeMint_publishes`: the FIRST row pins the payment facts to the new PIs. -/

/-- **`decoBridgeMint_publishes`** — on the FIRST row of a `satisfiedVm` witness of the weld, the
`mint_hash` column equals `PI[piCount]` and the `value` column equals `PI[piCount+1]`: the payment
commitment and minted value are now PUBLIC INPUTS (they flow into the recursive aggregate root). -/
theorem decoBridgeMint_publishes (hash : List ℤ → ℤ) (env : VmRowEnv) (isLast : Bool)
    (hsat : satisfiedVm hash decoBridgeMintVmDescriptor env true isLast) :
    env.loc paymentCommitCol = env.pub PI_PAYMENT_COMMIT
    ∧ env.loc paymentValueCol = env.pub PI_PAYMENT_VALUE := by
  obtain ⟨hc, _, _⟩ := hsat
  have hmemC : (VmConstraint.piBinding .first paymentCommitCol PI_PAYMENT_COMMIT)
      ∈ decoBridgeMintVmDescriptor.constraints := by
    show _ ∈ bridgeMintVmDescriptor.constraints ++ bridgeMintPaymentPins
    apply List.mem_append_right; simp [bridgeMintPaymentPins]
  have hmemV : (VmConstraint.piBinding .first paymentValueCol PI_PAYMENT_VALUE)
      ∈ decoBridgeMintVmDescriptor.constraints := by
    show _ ∈ bridgeMintVmDescriptor.constraints ++ bridgeMintPaymentPins
    apply List.mem_append_right; simp [bridgeMintPaymentPins]
  have hC := hc _ hmemC
  have hV := hc _ hmemV
  simp only [holdsVm_piFirst_true] at hC hV
  exact ⟨hC, hV⟩

/-- **`decoBridgeMint_published_value_is_minted`** — the published value PI IS the amount the ledger
credits: from the weld's publish + the deployed credit soundness, `PI[piCount+1]` equals `value`, and
`CellBridgeMintSpec pre value post` (so the ledger really rose by that published value). -/
theorem decoBridgeMint_published_value_is_minted (hash : List ℤ → ℤ) (env : VmRowEnv)
    (hrow : IsBridgeMintRow env) (pre post : CellState) (value : ℤ)
    (henc : RowEncodes env pre value post)
    (hgatesat : satisfiedVm hash decoBridgeMintVmDescriptor env true false)
    (hsat : satisfiedVm hash decoBridgeMintVmDescriptor env true true) :
    env.pub PI_PAYMENT_VALUE = env.loc paymentValueCol ∧ CellBridgeMintSpec pre value post := by
  refine ⟨(decoBridgeMint_publishes hash env false hgatesat).2.symm, ?_⟩
  exact (decoBridgeMint_full_sound hash env hrow pre post value henc hgatesat hsat).1

/-! ## §4 — the NEGATIVE tooth: a mismatched payment commitment ⟹ UNSAT. -/

/-- **`decoBridgeMint_rejects_mismatched_commit`** — a FIRST row whose `mint_hash` column differs from the
published `PI[piCount]` is not a satisfying witness: the appended `.piBinding .first` REJECTS it. With the
verifier anchoring `PI[piCount]` to the DECO proof's committed transcript, a mint whose committed payment
differs from the published one is UNSAT — the light-client-relevant tooth. -/
theorem decoBridgeMint_rejects_mismatched_commit (hash : List ℤ → ℤ) (env : VmRowEnv) (isLast : Bool)
    (hbad : env.loc paymentCommitCol ≠ env.pub PI_PAYMENT_COMMIT) :
    ¬ satisfiedVm hash decoBridgeMintVmDescriptor env true isLast := by
  intro hsat
  exact hbad (decoBridgeMint_publishes hash env isLast hsat).1

/-! ## §5 — Axiom hygiene. -/

#assert_axioms decoBridgeMint_to_base
#assert_axioms decoBridgeMint_full_sound
#assert_axioms decoBridgeMint_publishes
#assert_axioms decoBridgeMint_published_value_is_minted
#assert_axioms decoBridgeMint_rejects_mismatched_commit

end Dregg2.Circuit.Emit.EffectVmEmitBridgeMintDeco
