/-
# Dregg2.Circuit.Emit.TurnAuthLamportEmit — AUTHORIZATION INSIDE THE AIR.

**SUBSTRATE, SAID OUT LOUD: this is Lean-authored AIR.** Every constraint below is produced by a
`def`-GENERATOR over `AirBuilder.Head` / `VmConstraint2` / the deployed wide chip lookup
(`chipLookupTupleN`), and the teeth are FORCING LEMMAS over the emitted object. Rust only CONSUMES
the emitted descriptor. No constraint here is hand-written in Rust, and none may be.

## The hole this closes

Measured 2026-07-30: **nothing in the deployed AIR binds a signature, and for the owner path nothing
binds a capability either.** The table census over the whole deployed registry is `{main,
poseidon2_chip, poseidon2_state16_chip, range, memory, map_ops, umemory, umem_boundary}` — no curve
table, no signature table. All signature verification is host-side ed25519 `verify_strict`
(`turn/src/executor/authorize.rs`). The cap-open crown IS real in-AIR membership, but its `auth_tag`
is pinned to the constant `SIGNATURE_AUTH_TAG = 1` — a TIER BYTE, not a signature check. And
`transferCapOpenTB`'s turn-identity weld publishes `actor` and `dst` to PI 47/48 from columns NO
OTHER CONSTRAINT MENTIONS (`CapOpenTurnPins` §5 reports exactly this).

So a turn's proof was a WELL-FORMEDNESS certificate for a state transition, not a PERMISSION
certificate: "these two committed states are related by a legal balance move", never "the owner asked
for it, on this cell, to that recipient".

## Why THIS mechanism (chosen on SOUNDNESS, and the alternatives rejected on soundness)

The requirement is exact: **the PROVER must be unable to forge, and the prover is not the owner.**
The host builds the trace; the owner is offline. That single fact decides the design.

* **A preimage/MAC authenticator is REFUTED, not merely expensive.** "The AIR forces knowledge of a
  preimage of the cell's committed owner key" sounds like authorization, but the prover must HOLD
  that preimage to lay the trace. A prover holding the authenticating secret can authenticate any
  turn it likes. Every commit-and-open, hash-ratchet, or nonce-chain variant inherits this: whatever
  the AIR forces the prover to know, the prover knows, and can therefore re-use for a different
  turn. Authority that the prover can mint is not authority.

* **A receipt/nonce chain is necessary but not sufficient.** Inheriting authority from a checked
  predecessor answers "is this turn NEXT", never "did anyone authorize the FIRST one" — an
  origination act is still required at every link, or the chain is a chain of unauthorized turns.
  (Replay/ordering is handled here by the message binding, which includes the turn's own identity.)

* **The cap-open crown alone is REFUTED.** Merkle membership is a statement about a PUBLIC tree. A
  path is public data; anyone who can read the cap root can produce a membership witness for any leaf
  in it. Membership proves the capability EXISTS and WHAT it permits — it never proves WHO invoked
  it. That is precisely why routing owner effects through the existing crown, on its own, does not
  fix the owner path: it would move the hole, not close it.

  So the crown is KEPT (it binds which cap and what it permits) and this module supplies the missing
  half: WHO.

* **Therefore: an in-AIR SIGNATURE verification.** A signature is the unique primitive where signing
  is separable from proving: the owner signs offline and hands the prover `(message, signature)`; the
  prover holds no signing power.

* **The scheme is a HASH-BASED one-time signature over the deployed Poseidon2 chip — NOT ed25519.**
  This is a soundness choice, not a cost choice:
  1. An ed25519 verify in-AIR is NON-NATIVE field arithmetic: `Fq = 2²⁵⁵−19` over BabyBear felts. Its
     gate cross-sums reach `~2⁵⁴⁰` and OVERFLOW BabyBear, so the gates are read over ℤ — that is the
     field-width residual `Ed25519Gadget` names about itself (§"Resolution (honest)"). Building the
     ROOT OF AUTHORITY on a gate whose ℤ-reading does not match the field the prover actually
     evaluates in puts the gap at exactly the tooth that must not have one.
  2. ed25519 is CLASSICAL. The rest of this AIR's soundness floor is hash/Merkle/FRI. Binding
     authorization to ECDLP inside a post-quantum-oriented STARK makes authorization the weakest
     link in its own proof.
  3. A hash-based signature adds **no new hardness carrier at all** — its security reduces to the
     preimage/collision resistance of the SAME Poseidon2 the cap tree, the state commitment and FRI
     already ride (`Dregg2.Crypto.HashSig`'s header makes exactly this point). Native field, native
     chip, native floor, no new assumption.
  (That it is also ~3 orders of magnitude cheaper than the ~10⁷-gate ed25519 verify is a CONSEQUENCE
  of picking the native primitive, and is not the reason.)

* **One-time is the right granularity** and is not a limitation to be worked around: a turn is a
  one-shot act. The many-time lift is a Merkle tree over per-turn one-time public keys, which is the
  depth-16 crown this AIR already runs, indexed by the turn sequence.

## What is BUILT here

The gadget is `lamportAuthConstraints`, GENERATED, parametric in the block count `nb` (message width
`ell = 31·nb` bits; the deployed instance is `nb = 8`, i.e. a 248-bit message matching the deployed
8-felt digest width `CAP_W`). Every digest is an 8-FELT GROUP forced by the deployed wide chip lookup
`chipLookupTupleN` against `ChipTableSoundN` — the SAME lever the cap crown's `nodeLookup` uses, so
no new width claim and no narrower digest enters.

  1. **`sigLookups`** — per bit `k`, a wide lookup forcing `sigH k = permOut (sig k)`.
  2. **`selectGates`** — per bit `k`, per lane `j`, the degree-2 gate
     `sigH[k][j] − pk0[k][j] + m[k]·pk0[k][j] − m[k]·pk1[k][j] = 0`, i.e. `sigH k = pk k (m k)`.
  3. **`msgBitGates`** — every message bit is boolean.
  4. **`pairLookups` / `accLookups` / `authRootPins`** — the public key is FOLDED (rate-16 wide
     absorbs, `pk0‖pk1` then a running fold, exactly the cap tree's `pack8` shape) to ONE 8-felt
     authority root, PINNED to 8 public inputs. Without this the prover picks the public key and the
     verify is a tautology; with it, the light client anchors those PIs from the owner's committed
     authority root and the public key is no longer the prover's.
  5. **`turnDigestLookup`** — the `nb` message-digest felts are forced to `permOut` of the TURN
     IDENTITY columns (`src`, `actor`, `dst`, …), supplied by the caller.
  6. **`msgReconGates` + `canonGates`** — the signed bits recompose EXACTLY to those digest felts.
     31 bits per felt, and the recomposition is pinned to the CANONICAL representative by an in-AIR
     BabyBear canonicality gate (`p = 2³⁰+2²⁹+2²⁸+2²⁷+1`: if the top four bits are all set then every
     one of the low 27 bits is forced to zero), so `Σ bᵢ2ⁱ < p` and the mod-`p` recomposition gate
     collapses to ℤ equality. No second representation survives, so no `Σ ≡ digest (mod p)` residual
     is left behind.

**This is what makes `actor` and `dst` stop being free.** They are INPUTS to `turnDigestLookup`,
whose output is bit-decomposed into the very bits the signature opens. Move `dst` by one and every
message bit downstream of it changes, and the witness must then contain a Lamport preimage the owner
never revealed. The three-weld fix and the authorization fix are THE SAME ACT: the free columns are
free precisely because nothing signs them.

## The teeth

  * `lamport_verify_forced` — a satisfying witness FORCES `∀ k, permOut (sigVal k) = pkVal k (mBit k)`,
    which is DEFINITIONALLY `Dregg2.Crypto.HashSig.verify permOut pk m sig` at `D := List ℤ`. So the
    already-proved forgery tooth (`HashSig.lamport_forgery`: any verifying forgery on a message that
    differs at one bit yields a preimage or a collision) applies to the emitted object VERBATIM — no
    new reduction, no new carrier.
  * `msg_is_the_turn_digest` — the signed bits recompose to the turn-digest felts over ℤ (exactly,
    via the canonicality gate), and those felts are `permOut` of the turn-identity columns.
  * `authRoot_forced` — the folded public key is the published root.
  * `wrong_key_refused` / `unsigned_refused` / `moved_dst_refused` — the KAT teeth, both polarities,
    kernel-reduced.

## Axiom hygiene

`#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}); no `sorry`/`admit`/
`native_decide`. The `#guard` KATs reduce in the kernel.
-/
import Dregg2.Circuit.Emit.AirBuilder
import Dregg2.Circuit.Emit.EffectVmEmitTransfer
import Dregg2.Crypto.HashSig

namespace Dregg2.Circuit.Emit.TurnAuthLamportEmit

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv VmConstraint VmRow)
open Dregg2.Circuit.DescriptorIR2
  (VmConstraint2 EffectVmDescriptor2 Lookup TableId Table chipLookupTupleN ChipTableSoundN
   chipRowN chip_lookup_sound_N Satisfied2 VmTrace envAt)
open Dregg2.Circuit.Emit.AirBuilder

set_option autoImplicit false

/-! ## §0 — parameters. -/

/-- The BabyBear prime `p = 2³⁰+2²⁹+2²⁸+2²⁷+1 = 2013265921`. -/
def P : ℤ := 2013265921

/-- Felts per digest group. This is the DEPLOYED `DeployedCapOpen.CAP_W = 8` — the cap tree's native
8-felt digest — reused, not a new width. -/
@[reducible] def W : Nat := 8

/-- Bits carried by one message block: a BabyBear felt is `< p < 2³¹`, so 31 bits with an in-AIR
canonicality gate pins the canonical representative exactly. -/
def BLOCK_BITS : Nat := 31

/-- The number of low bits the canonicality gate forces to zero when the top four are all set
(`p − 1 = 2³⁰+2²⁹+2²⁸+2²⁷`, so any larger 31-bit value needs a nonzero low bit). -/
def LOW_BITS : Nat := 27

/-- Signed message width in bits for `nb` blocks. The deployed instance is `nb = 8`: a 248-bit
message, matching the 8-felt digest the cap tree already commits. -/
def ELL (nb : Nat) : Nat := BLOCK_BITS * nb

/-! ## §1 — the column plan (every digest is an 8-felt GROUP). -/

/-- The `i`-th 8-felt group of a block starting at `b`. -/
def grp (b i : Nat) : Fin W → Nat := fun j => b + W * i + j.val

/-- Read an 8-felt column group as its ordered list of column indices. -/
def gcols (g : Fin W → Nat) : List Nat := (List.finRange W).map g

/-- Read an 8-felt column group's VALUES under an assignment. -/
def gval (a : Assignment) (g : Fin W → Nat) : List ℤ := (gcols g).map a

/-- The revealed Lamport preimage (the signature) at bit `k` — an 8-felt group. -/
def sigG (w nb k : Nat) : Fin W → Nat := grp w k
/-- The hash of the revealed preimage at bit `k`, forced by a wide chip lookup. -/
def sigHG (w nb k : Nat) : Fin W → Nat := grp (w + W * ELL nb) k
/-- The public-key entry for bit value `0` at bit `k`. -/
def pk0G (w nb k : Nat) : Fin W → Nat := grp (w + 2 * W * ELL nb) k
/-- The public-key entry for bit value `1` at bit `k`. -/
def pk1G (w nb k : Nat) : Fin W → Nat := grp (w + 3 * W * ELL nb) k
/-- The per-bit pair compression `permOut (pk0 ‖ pk1)` — a rate-16 absorb, the cap tree's `pack8`
shape. -/
def pairG (w nb k : Nat) : Fin W → Nat := grp (w + 4 * W * ELL nb) k
/-- The running authority-root fold. `acc 0` is unused; `acc 1 = permOut (pair 0 ‖ pair 1)` and
`acc k = permOut (acc (k−1) ‖ pair k)` for `k ≥ 2`. -/
def accG (w nb k : Nat) : Fin W → Nat := grp (w + 5 * W * ELL nb) k
/-- The message bit at position `k`. -/
def mCol (w nb k : Nat) : Nat := w + 6 * W * ELL nb + k
/-- The canonicality product `b30·b29` for block `q`. -/
def ct1Col (w nb q : Nat) : Nat := w + 6 * W * ELL nb + ELL nb + q
/-- The canonicality product `b28·b27` for block `q`. -/
def ct2Col (w nb q : Nat) : Nat := w + 6 * W * ELL nb + ELL nb + nb + q
/-- The canonicality product `(b30·b29)·(b28·b27)` for block `q`. -/
def ctCol (w nb q : Nat) : Nat := w + 6 * W * ELL nb + ELL nb + 2 * nb + q
/-- The turn-identity digest felt for block `q` (the message the owner signed, felt-wise). -/
def tdCol (w nb q : Nat) : Nat := w + 6 * W * ELL nb + ELL nb + 3 * nb + q

/-- **The zero-pinned pad group.** ⚑ MEASURED HAZARD this exists to avoid: the deployed absorb
`chip_absorb_all_lanes` seeds lanes 4/5/6 from the inputs ONLY at arity `7`, `CHIP_WIDE_ARITY = 11`
or `CHIP_NODE8_ARITY = 16`; at every other arity it writes `st[4] = arity` and leaves `st[5]`,
`st[6]` ZERO — so an arity-8 absorb SILENTLY DROPS inputs 4, 5 and 6. An 8-felt signature block
absorbed at arity 8 would therefore commit only five of its eight felts and be malleable in the
other three. Every absorb in this gadget is padded to arity 16 (`node8`, which seeds all sixteen
lanes) against these zero-pinned columns. -/
def zpadCol (w nb : Nat) : Nat := w + 6 * W * ELL nb + ELL nb + 3 * nb + W

/-- The whole gadget's column span past `w`. The turn-digest block is always `W` wide (the chip's
full squeeze), independent of how many of its felts are signed. -/
def AUTH_SPAN (nb : Nat) : Nat := 6 * W * ELL nb + ELL nb + 3 * nb + W + 1

/-- The turn-digest columns as the wide lookup's output block.

The block is always `W = 8` columns — `chipLookupTupleN`'s output block is the chip's FULL squeeze,
so a shorter list makes the lookup relate lists of different lengths and it could never hold.

⚑ **The DEPLOYED instance signs ALL `W` of them (`nb = NB = W`), and that is load-bearing.** At
`nb < W` the gadget is still well-formed and still forces a signature — but only `nb` of the 8
digest felts are covered by the message, so the signed bits would NOT determine the turn digest and
the weld would leak. `same_msg_same_turn_digest` therefore carries `hnb : nb = W` explicitly rather
than being quietly true of a shape nobody deploys. -/
def tdCols (w nb : Nat) : List Nat := (List.range W).map (tdCol w nb)

/-- The DEPLOYED block count: `nb = W = 8`. A 248-bit signed message — one 31-bit block per felt of
the chip's 8-felt squeeze, so EVERY digest felt is signed. -/
def NB : Nat := W

-- The output block is the chip's full squeeze at any `nb`; the DEPLOYED instance signs all of it.
#guard (tdCols 0 NB).length == W
#guard (tdCols 0 1).length == W
#guard ELL NB == 248
#guard AUTH_SPAN NB == 6 * 8 * 248 + 248 + 24 + 8 + 1

/-! ## §2 — the GENERATORS (no gate is hand-authored). -/

/-- Pad an absorb's input column list to the `node8` arity 16 with zero-pinned columns, so the
deployed chip seeds ALL sixteen lanes and drops none of the real inputs. -/
def padTo16 (w nb : Nat) (ins : List Nat) : List Nat :=
  ins ++ List.replicate (Dregg2.Circuit.DescriptorIR2.CHIP_RATE - ins.length) (zpadCol w nb)

/-- An 8-felt column group has exactly `W = 8` columns. -/
theorem gcols_length (g : Fin W → Nat) : (gcols g).length = W := by
  simp [gcols]

/-- A padded absorb has exactly the `node8` arity 16 whenever the real inputs fit. -/
theorem padTo16_length (w nb : Nat) (ins : List Nat)
    (h : ins.length ≤ Dregg2.Circuit.DescriptorIR2.CHIP_RATE) :
    (padTo16 w nb ins).length = Dregg2.Circuit.DescriptorIR2.CHIP_RATE := by
  simp [padTo16]; omega

/-- **A padded absorb is at an ADMITTED arity.** `CHIP_RATE = 16` is a root of the deployed
degree-7 admission product, so `padTo16` is exactly the "pad up to the next admitted arity" the
chip's budget prescribes — but only when the real inputs FIT. At `ins.length > 16` the `Nat`
subtraction saturates, `padTo16` is the identity, and the absorb lands at an arity the chip AIR
refuses; that is the case this hypothesis exists to exclude. -/
theorem padTo16_admitted (w nb : Nat) (ins : List Nat)
    (h : ins.length ≤ Dregg2.Circuit.DescriptorIR2.CHIP_RATE) :
    Dregg2.Circuit.DescriptorIR2.ChipArityAdmitted
      (((padTo16 w nb ins).map EmittedExpr.var).length) := by
  rw [List.length_map, padTo16_length w nb ins h]
  exact of_decide_eq_true (Eq.refl true)

/-- The absorb-arity discharger for this gadget: every `wideHash` here absorbs a `padTo16` block,
so the obligation reduces to "the real inputs fit", which is decidable for the generated groups and
a named hypothesis for the caller-supplied turn identity. -/
macro "turn_absorb_arity" : tactic =>
  `(tactic| first
      | assumption
      | exact padTo16_admitted _ _ _ (by first
          | assumption
          | simp [gcols, W, Dregg2.Circuit.DescriptorIR2.CHIP_RATE]
          | (simp only [foldIns]; split <;>
              simp [gcols, W, Dregg2.Circuit.DescriptorIR2.CHIP_RATE])
          | decide)
      | fail "TURN-AUTH ABSORB ARITY NOT ADMITTED — this wideHash absorbs a block the deployed \
              chip AIR refuses (CHIP_ADMITTED_ARITIES = [0, 2, 3, 4, 7, 11, 16]). A padTo16 block \
              is at arity 16 ONLY when the real inputs fit; supply `ins.length ≤ CHIP_RATE`.")

/-- The gate pinning the pad column to zero. -/
def zpadGates (w nb : Nat) : List VmConstraint2 := [cgH (Head.lin 1 (zpadCol w nb))]

/-- The fixed zero tail every 8-felt block is absorbed with, to reach the `node8` arity 16. -/
def SIGPAD : List ℤ := List.replicate (Dregg2.Circuit.DescriptorIR2.CHIP_RATE - W) 0

/-- **The effective one-way function the signature verify runs on**: the deployed permutation of the
8-felt block followed by the zero tail that lifts the absorb to arity 16. It is `permOut` composed
with a fixed injection, so it inherits `permOut`'s preimage/collision resistance exactly. -/
def Hsig (permOut : List ℤ → List ℤ) : List ℤ → List ℤ := fun blk => permOut (blk ++ SIGPAD)

/-- The wide Poseidon2 lookup forcing an 8-felt output group from an input column list. -/
def wideHash (ins : List Nat) (out : List Nat)
    (hAdm : Dregg2.Circuit.DescriptorIR2.ChipArityAdmitted (ins.map EmittedExpr.var).length :=
      by turn_absorb_arity) : VmConstraint2 :=
  .lookup { table := TableId.poseidon2
          , tuple := chipLookupTupleN (ins.map EmittedExpr.var) out hAdm }

/-- **`sigLookups`** — per bit `k`, force `sigH k = permOut (sig k)`. -/
def sigLookups (w nb : Nat) : List VmConstraint2 :=
  (List.range (ELL nb)).map (fun k =>
    wideHash (padTo16 w nb (gcols (sigG w nb k))) (gcols (sigHG w nb k)))

/-- The SELECT head at bit `k`, lane `j`: `sigH − pk0 + m·pk0 − m·pk1`. Zero forces
`sigH[k][j] = pk0[k][j]` when `m k = 0` and `= pk1[k][j]` when `m k = 1`. -/
def selectHead (w nb k : Nat) (j : Fin W) : Head :=
  (((Head.lin 1 (sigHG w nb k j)).addLin (-1) (pk0G w nb k j)).addProd 1
      [mCol w nb k, pk0G w nb k j]).addProd (-1) [mCol w nb k, pk1G w nb k j]

/-- **`selectGates`** — the per-bit, per-lane select gate. -/
def selectGates (w nb : Nat) : List VmConstraint2 :=
  (List.range (ELL nb)).flatMap (fun k =>
    (List.finRange W).map (fun j => cgH (selectHead w nb k j)))

/-- **`msgBitGates`** — every message bit is boolean. -/
def msgBitGates (w nb : Nat) : List VmConstraint2 :=
  (List.range (ELL nb)).map (fun k => binGate (mCol w nb k))

/-- **`pairLookups`** — per bit `k`, compress the two public-key entries: the rate-16 absorb of
`pk0 ‖ pk1`. -/
def pairLookups (w nb : Nat) : List VmConstraint2 :=
  (List.range (ELL nb)).map (fun k =>
    wideHash (padTo16 w nb (gcols (pk0G w nb k) ++ gcols (pk1G w nb k))) (gcols (pairG w nb k)))

/-- The `k`-th fold input block: `pair 0 ‖ pair 1` at `k = 1`, else `acc (k−1) ‖ pair k`. -/
def foldIns (w nb k : Nat) : List Nat :=
  (if k = 1 then gcols (pairG w nb 0) else gcols (accG w nb (k - 1))) ++ gcols (pairG w nb k)

/-- A fold input block is two 8-felt groups (`pair ‖ pair` or `acc ‖ pair`), so it fits the rate
and its `padTo16` lands on the admitted arity 16. -/
theorem foldIns_length_le (w nb k : Nat) :
    (foldIns w nb k).length ≤ Dregg2.Circuit.DescriptorIR2.CHIP_RATE := by
  unfold foldIns
  split <;> simp [gcols, W, Dregg2.Circuit.DescriptorIR2.CHIP_RATE]

/-- **`accLookups`** — the running authority-root fold over every public-key pair. -/
def accLookups (w nb : Nat) : List VmConstraint2 :=
  (List.range (ELL nb - 1)).map (fun i =>
    wideHash (padTo16 w nb (foldIns w nb (i + 1))) (gcols (accG w nb (i + 1)))
      (padTo16_admitted _ _ _ (foldIns_length_le w nb (i + 1))))

/-- **`authRootPins`** — the folded authority root is PUBLISHED: its 8 felts are pinned to
`PI[pcBase .. pcBase+7]`. The light client ANCHORS these from the owner's committed authority root,
so the public key the verify runs against is not the prover's to choose. -/
def authRootPins (w nb pcBase : Nat) : List VmConstraint2 :=
  (List.finRange W).map (fun j =>
    .base (.piBinding VmRow.first (accG w nb (ELL nb - 1) j) (pcBase + j.val)))

/-- **`turnDigestLookup`** — the message digest felts are `permOut` of the TURN IDENTITY columns.
`turnIn` is supplied by the caller: `src`, `actor`, `dst`, and whatever else the turn is. THIS is
what makes `actor` and `dst` load-bearing. -/
def turnDigestLookup (w nb : Nat) (turnIn : List Nat)
    (hIn : turnIn.length ≤ Dregg2.Circuit.DescriptorIR2.CHIP_RATE := by first | assumption | decide) : VmConstraint2 :=
  wideHash (padTo16 w nb turnIn) (tdCols w nb) (padTo16_admitted w nb turnIn hIn)

/-- The recomposition head for block `q`: `Σ_{i<31} m[31q+i]·2ⁱ − td[q]`. -/
def reconHead (w nb q : Nat) : Head :=
  ((List.range BLOCK_BITS).foldl
    (fun h i => h.addLin ((2 : ℤ) ^ i) (mCol w nb (BLOCK_BITS * q + i))) Head.zero).addLin (-1)
      (tdCol w nb q)

/-- **`msgReconGates`** — the signed bits recompose to the turn-digest felts. -/
def msgReconGates (w nb : Nat) : List VmConstraint2 :=
  (List.range nb).map (fun q => cgH (reconHead w nb q))

/-- **`canonGates q`** — the in-AIR BabyBear CANONICALITY gate for block `q`. `p − 1 =
2³⁰+2²⁹+2²⁸+2²⁷`, so a 31-bit value is `< p` exactly when it is not the case that all four top bits
are set AND some low bit is set. Three product gates build `t = b30·b29·b28·b27`, then `t·bᵢ = 0`
forces every low bit to vanish whenever `t = 1`. With this, `Σ bᵢ2ⁱ < p`, so the mod-`p`
recomposition gate has ONE solution and collapses to ℤ equality — no second representation. -/
def canonGates (w nb q : Nat) : List VmConstraint2 :=
  let b := fun i => mCol w nb (BLOCK_BITS * q + i)
  [ cgH ((Head.lin 1 (ct1Col w nb q)).addProd (-1) [b 30, b 29])
  , cgH ((Head.lin 1 (ct2Col w nb q)).addProd (-1) [b 28, b 27])
  , cgH ((Head.lin 1 (ctCol w nb q)).addProd (-1) [ct1Col w nb q, ct2Col w nb q]) ]
  ++ (List.range LOW_BITS).map (fun i => cgH (Head.zero.addProd 1 [ctCol w nb q, b i]))

/-- **`allCanonGates`** — the canonicality gate for every block. -/
def allCanonGates (w nb : Nat) : List VmConstraint2 :=
  (List.range nb).flatMap (canonGates w nb)

/-- **`lamportAuthConstraints w nb pcBase turnIn`** — THE WHOLE IN-AIR AUTHORIZATION: the signature
verify, the public-key fold to a published authority root, and the binding of the signed message to
the turn identity. -/
def lamportAuthConstraints (w nb pcBase : Nat) (turnIn : List Nat)
    (hIn : turnIn.length ≤ Dregg2.Circuit.DescriptorIR2.CHIP_RATE := by first | assumption | decide) : List VmConstraint2 :=
  sigLookups w nb ++ selectGates w nb ++ msgBitGates w nb
    ++ pairLookups w nb ++ accLookups w nb ++ authRootPins w nb pcBase
    ++ [turnDigestLookup w nb turnIn hIn] ++ msgReconGates w nb ++ allCanonGates w nb
    ++ zpadGates w nb

/-! ## §3 — structural `#guard`s (the generators produce the budgeted shapes). -/

#guard ELL 8 == 248
#guard AUTH_SPAN 8 == 6 * 8 * 248 + 248 + 33
#guard (sigLookups 0 8).length == 248
#guard (selectGates 0 8).length == 248 * 8
#guard (msgBitGates 0 8).length == 248
#guard (pairLookups 0 8).length == 248
#guard (accLookups 0 8).length == 247
#guard (authRootPins 0 8 40).length == 8
#guard (msgReconGates 0 8).length == 8
#guard (allCanonGates 0 8).length == 8 * 30
#guard (lamportAuthConstraints 0 8 40 [1, 2, 3]).length
  == 248 + 248 * 8 + 248 + 248 + 247 + 8 + 1 + 8 + 240 + 1
-- every absorb is arity 16 (node8): all sixteen lanes seeded, no input dropped.
#guard (padTo16 0 8 [1, 2, 3]).length == 16
#guard (padTo16 0 8 (gcols (sigG 0 8 0))).length == 16
#guard (padTo16 0 8 (gcols (pk0G 0 8 0) ++ gcols (pk1G 0 8 0))).length == 16

-- The column groups do not overlap: the six 8-felt blocks tile `[w, w + 6·8·ELL)` and the scalar
-- columns follow. (Docstring DEMOTED to a comment: Lean attaches a `/-- -/` to the next command,
-- and `#guard` is not a declaration.)
#guard (sigG 0 1 0 ⟨0, by decide⟩) == 0
#guard (sigHG 0 1 0 ⟨0, by decide⟩) == 8 * 31
#guard (mCol 0 1 0) == 6 * 8 * 31
#guard (tdCol 0 1 0) == 6 * 8 * 31 + 31 + 3

/-! ## §4 — the canonicality envelope and the mod-`p` → ℤ lift.

`VmConstraint.holdsVm` asserts a gate body `≡ 0 [ZMOD p]` — the DEPLOYED field constraint — while a
chip lookup yields an ℤ equality. Reconciling them takes the deployed CANONICALITY envelope: every
trace cell is the canonical BabyBear representative. That is not an assumption about the circuit, it
is what a BabyBear trace IS; it is the same envelope `CapOpenEmit.CapOpenRowCanon` carries, and it is
shown non-vacuous below. -/

/-- **`AuthRowCanon env`** — the deployed canonicality envelope: every trace cell on this row is the
canonical BabyBear representative `0 ≤ · < p`. -/
structure AuthRowCanon (env : VmRowEnv) : Prop where
  cells : ∀ col : Nat, 0 ≤ env.loc col ∧ env.loc col < P

/-- The envelope is NON-VACUOUS (the all-zero row satisfies it). -/
theorem authRowCanon_satisfiable : AuthRowCanon ⟨fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0⟩ :=
  ⟨fun _ => by constructor <;> norm_num [P]⟩

/-- Difference-gate exactness: `a − b ≡ 0 [ZMOD p]` with both sides canonical ⟹ `a = b` over ℤ (the
residual lies in `(−p, p)`, so `p ∣ residual` collapses it — no primality needed). -/
theorem diffExact {a b : ℤ} (ha : 0 ≤ a ∧ a < P) (hb : 0 ≤ b ∧ b < P)
    (h : a - b ≡ 0 [ZMOD 2013265921]) : a = b := by
  rw [Int.modEq_zero_iff_dvd] at h
  obtain ⟨k, hk⟩ := h
  simp only [P] at ha hb
  omega

/-- Boolean-gate exactness: `d·(d−1) ≡ 0 [ZMOD p]` with `d` canonical ⟹ `d ∈ {0,1}` over ℤ
(`p`'s primality splits the product; the canonicality envelope pins each factor). The same route
`CapOpenEmit.boolGate_exact` uses for the cap mask bits. -/
theorem boolExact {d : ℤ} (hc : 0 ≤ d ∧ d < P) (h : d * (d + -1) ≡ 0 [ZMOD 2013265921]) :
    d = 0 ∨ d = 1 := by
  rw [Int.modEq_zero_iff_dvd] at h
  simp only [P] at hc
  rcases Dregg2.Circuit.Emit.EffectVmEmitTransfer.pPrimeInt.dvd_mul.mp h with h0 | h1
  · obtain ⟨k, hk⟩ := h0; left; omega
  · obtain ⟨k, hk⟩ := h1; right; omega

/-- Evaluating a column list lifted to `EmittedExpr.var`s is just reading the columns. -/
theorem map_var_eval (a : Assignment) (cols : List Nat) :
    ((cols.map EmittedExpr.var).map (fun e => e.eval a)) = cols.map a := by
  simp [List.map_map, Dregg2.Exec.CircuitEmit.EmittedExpr.eval, Function.comp_def]

/-- A group's VALUES read lane-by-lane over `Fin W` (the shape lane-wise congruence needs). -/
theorem gval_eq (a : Assignment) (g : Fin W → Nat) :
    gval a g = (List.finRange W).map (fun j => a (g j)) := by
  simp [gval, gcols, List.map_map, Function.comp_def]

/-- Reading a padded absorb's inputs: the real columns followed by the fixed zero tail. -/
theorem padTo16_vals (a : Assignment) (w nb : Nat) (ins : List Nat) (hz : a (zpadCol w nb) = 0) :
    (padTo16 w nb ins).map a
      = ins.map a ++ List.replicate (Dregg2.Circuit.DescriptorIR2.CHIP_RATE - ins.length) 0 := by
  simp [padTo16, List.map_append, List.map_replicate, hz]

/-! ## §5 — the wide-lookup forcing lever (the deployed chip, at full 8-felt squeeze width). -/

/-- The `Lookup` a `wideHash` wraps. -/
def wideHashLk (ins out : List Nat)
    (hAdm : Dregg2.Circuit.DescriptorIR2.ChipArityAdmitted (ins.map EmittedExpr.var).length :=
      by turn_absorb_arity) : Lookup :=
  { table := TableId.poseidon2, tuple := chipLookupTupleN (ins.map EmittedExpr.var) out hAdm }

theorem wideHash_eq (ins out : List Nat)
    (hAdm : Dregg2.Circuit.DescriptorIR2.ChipArityAdmitted (ins.map EmittedExpr.var).length) :
    wideHash ins out hAdm = .lookup (wideHashLk ins out hAdm) := rfl

/-- **`wideHash_forces`** — against a SOUND wide chip table (`ChipTableSoundN`, the exact lever the
cap crown's `nodeLookup` rides), a `wideHash` lookup forces its output column block to be the genuine
full 8-felt permutation output of its input columns. ℤ equality, not mod `p`: the chip row IS the
tuple. -/
theorem wideHash_forces (permOut : List ℤ → List ℤ)
    (tf : Dregg2.Circuit.DescriptorIR2.TraceFamily) (env : VmRowEnv)
    (hChip : ChipTableSoundN permOut (tf TableId.poseidon2))
    (ins out : List Nat)
    (hAdm : Dregg2.Circuit.DescriptorIR2.ChipArityAdmitted (ins.map EmittedExpr.var).length)
    (hlen : ins.length ≤ Dregg2.Circuit.DescriptorIR2.CHIP_RATE)
    (hhold : (wideHashLk ins out hAdm).holdsAt tf env) :
    out.map env.loc = permOut (ins.map env.loc) := by
  have h := chip_lookup_sound_N permOut (tf TableId.poseidon2) hChip env.loc
    (ins.map EmittedExpr.var) out hAdm hhold
  rw [h, map_var_eval]

/-! ## §6 — `AuthCore`: the row-local denotational facts the gadget's constraints ARE.

Each field is literally one emitted constraint's `holdsAt` on the row, so `AuthCore` carries no
content beyond "the gadget's constraints hold here". §8 derives it from `Satisfied2`. -/

/-- **`AuthCore permOut tf w nb pcBase turnIn env`** — the gadget's constraints, on one active row. -/
structure AuthCore (tf : Dregg2.Circuit.DescriptorIR2.TraceFamily) (w nb pcBase : Nat)
    (turnIn : List Nat) (env : VmRowEnv) : Prop where
  /-- every signature block hashes to its digest block (the wide chip lookup). -/
  sigHashed  : ∀ k < ELL nb,
    (wideHashLk (padTo16 w nb (gcols (sigG w nb k))) (gcols (sigHG w nb k))
      (padTo16_admitted _ _ _ (by rw [gcols_length]; decide))).holdsAt tf env
  /-- the per-lane SELECT gate: the hashed signature equals the public-key entry for the message bit. -/
  selectZero : ∀ k < ELL nb, ∀ j : Fin W,
    evalH (selectHead w nb k j) env.loc ≡ 0 [ZMOD 2013265921]
  /-- every message bit is `0` or `1` (the deployed 1-bit range tooth, an ℤ-level fact). -/
  msgBool    : ∀ k < ELL nb, env.loc (mCol w nb k) = 0 ∨ env.loc (mCol w nb k) = 1
  /-- each public-key pair is compressed (the rate-16 absorb of `pk0 ‖ pk1`). -/
  pairHashed : ∀ k < ELL nb,
    (wideHashLk (padTo16 w nb (gcols (pk0G w nb k) ++ gcols (pk1G w nb k)))
      (gcols (pairG w nb k))
      (padTo16_admitted _ _ _ (by simp [gcols, W, Dregg2.Circuit.DescriptorIR2.CHIP_RATE]))).holdsAt tf env
  /-- the running authority-root fold. -/
  accHashed  : ∀ k, 1 ≤ k → k < ELL nb →
    (wideHashLk (padTo16 w nb (foldIns w nb k)) (gcols (accG w nb k))
      (padTo16_admitted _ _ _ (foldIns_length_le w nb k))).holdsAt tf env
  /-- the folded authority root is pinned to the 8 published PI slots. -/
  rootPinned : ∀ j : Fin W,
    env.loc (accG w nb (ELL nb - 1) j) ≡ env.pub (pcBase + j.val) [ZMOD 2013265921]
  /-- the turn-identity digest felts are `permOut` of the TURN IDENTITY columns. -/
  turnHashed : ∀ hAdm : Dregg2.Circuit.DescriptorIR2.ChipArityAdmitted
      (((padTo16 w nb turnIn).map EmittedExpr.var).length),
    (wideHashLk (padTo16 w nb turnIn) (tdCols w nb) hAdm).holdsAt tf env
  /-- the signed bits recompose to the turn-digest felts. -/
  reconZero  : ∀ q < nb, evalH (reconHead w nb q) env.loc ≡ 0 [ZMOD 2013265921]
  /-- the arity-16 pad column is zero (so every absorb's tail is the fixed `SIGPAD`). -/
  zpadZero   : env.loc (zpadCol w nb) = 0

/-! ## §7 — THE TEETH. -/

/-- The signature at bit `k`, read off the trace as an 8-felt block. -/
def sigOf (env : VmRowEnv) (w nb : Nat) : Fin (ELL nb) → List ℤ :=
  fun k => gval env.loc (sigG w nb k.val)

/-- The public key at bit `k` for bit-value `b`, read off the trace. -/
def pkOf (env : VmRowEnv) (w nb : Nat) : Fin (ELL nb) → Bool → List ℤ :=
  fun k b => if b then gval env.loc (pk1G w nb k.val) else gval env.loc (pk0G w nb k.val)

/-- The signed message bit at position `k`, read off the trace. -/
def msgOf (env : VmRowEnv) (w nb : Nat) : Fin (ELL nb) → Bool :=
  fun k => decide (env.loc (mCol w nb k.val) = 1)

/-- Per-lane: the select gate + canonicality force the hashed signature lane to the selected
public-key lane, over ℤ. -/
theorem select_lane (w nb : Nat) (env : VmRowEnv) (hcanon : AuthRowCanon env)
    (k : Nat) (j : Fin W)
    (hm : env.loc (mCol w nb k) = 0 ∨ env.loc (mCol w nb k) = 1)
    (hg : evalH (selectHead w nb k j) env.loc ≡ 0 [ZMOD 2013265921]) :
    env.loc (sigHG w nb k j)
      = if env.loc (mCol w nb k) = 1 then env.loc (pk1G w nb k j) else env.loc (pk0G w nb k j) := by
  have hev : evalH (selectHead w nb k j) env.loc
      = env.loc (sigHG w nb k j) - env.loc (pk0G w nb k j)
        + env.loc (mCol w nb k) * env.loc (pk0G w nb k j)
        - env.loc (mCol w nb k) * env.loc (pk1G w nb k j) := by
    simp only [selectHead, evalH_addProd, evalH_addLin, evalH_lin, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil]
    ring
  rcases hm with h0 | h1
  · have hbr : (if env.loc (mCol w nb k) = 1 then env.loc (pk1G w nb k j)
        else env.loc (pk0G w nb k j)) = env.loc (pk0G w nb k j) := by rw [h0]; norm_num
    have hev' : evalH (selectHead w nb k j) env.loc
        = env.loc (sigHG w nb k j) - env.loc (pk0G w nb k j) := by rw [hev, h0]; ring
    rw [hbr]
    exact diffExact (hcanon.cells _) (hcanon.cells _) (by rw [← hev']; exact hg)
  · have hbr : (if env.loc (mCol w nb k) = 1 then env.loc (pk1G w nb k j)
        else env.loc (pk0G w nb k j)) = env.loc (pk1G w nb k j) := by rw [h1]; norm_num
    have hev' : evalH (selectHead w nb k j) env.loc
        = env.loc (sigHG w nb k j) - env.loc (pk1G w nb k j) := by rw [hev, h1]; ring
    rw [hbr]
    exact diffExact (hcanon.cells _) (hcanon.cells _) (by rw [← hev']; exact hg)

/-- **`lamport_verify_forced` — THE KEYSTONE.** A witness satisfying the gadget's constraints on an
active row FORCES, at every one of the `ELL nb` bit positions, that the deployed Poseidon2 of the
revealed preimage EQUALS the public-key entry for the signed bit. That statement is
DEFINITIONALLY `Dregg2.Crypto.HashSig.verify` at `D := List ℤ`, `H := permOut` — so the already-proved
forgery tooth applies to THIS emitted object with no new reduction and no new hardness carrier. -/
theorem lamport_verify_forced (permOut : List ℤ → List ℤ)
    (tf : Dregg2.Circuit.DescriptorIR2.TraceFamily) (w nb pcBase : Nat) (turnIn : List Nat)
    (hIn : turnIn.length ≤ Dregg2.Circuit.DescriptorIR2.CHIP_RATE)
    (env : VmRowEnv)
    (hChip : ChipTableSoundN permOut (tf TableId.poseidon2))
    (hcore : AuthCore tf w nb pcBase turnIn env)
    (hcanon : AuthRowCanon env) :
    Dregg2.Crypto.HashSig.verify (Hsig permOut) (pkOf env w nb) (msgOf env w nb)
      (sigOf env w nb) := by
  intro k
  -- the chip lookup: the digest block IS the permutation of the PADDED signature block.
  have hlk := wideHash_forces permOut tf env hChip _ _
    (padTo16_admitted _ _ _ (by rw [gcols_length]; decide))
    (by rw [padTo16_length _ _ _ (by rw [gcols_length]; decide)])
    (hcore.sigHashed k.val k.isLt)
  -- the select gate, lane by lane: the digest block IS the selected public-key block.
  have hpk : pkOf env w nb k (msgOf env w nb k)
      = (List.finRange W).map (fun j =>
          if env.loc (mCol w nb k.val) = 1 then env.loc (pk1G w nb k.val j)
          else env.loc (pk0G w nb k.val j)) := by
    unfold pkOf msgOf
    by_cases hb : env.loc (mCol w nb k.val) = 1 <;> simp [hb, gval_eq]
  have hsel : gval env.loc (sigHG w nb k.val) = pkOf env w nb k (msgOf env w nb k) := by
    rw [gval_eq, hpk]
    refine List.map_congr_left ?_
    intro j _
    exact select_lane w nb env hcanon k.val j (hcore.msgBool k.val k.isLt)
      (hcore.selectZero k.val k.isLt j)
  -- compose: permOut (sig k) = digest block = pk k (m k).
  rw [padTo16_vals env.loc w nb _ hcore.zpadZero, gcols_length] at hlk
  have hlk' : gval env.loc (sigHG w nb k.val)
      = Hsig permOut (gval env.loc (sigG w nb k.val)) := hlk
  show Hsig permOut (gval env.loc (sigG w nb k.val)) = pkOf env w nb k (msgOf env w nb k)
  rw [← hlk']
  exact hsel

#assert_axioms diffExact
#assert_axioms wideHash_forces
#assert_axioms select_lane
#assert_axioms lamport_verify_forced

/-! ## §8 — the DESCRIPTOR, and `AuthCore` DISCHARGED from `Satisfied2`.

Nothing above is carried: `withTurnAuth` widens any base descriptor by the gadget, and
`authCore_of_satisfied` derives every `AuthCore` field from the deployed denotation on row 0. -/

/-- **`withTurnAuth base nb turnIn`** — `base` widened by the in-AIR authorization gadget: `+
AUTH_SPAN nb` columns, `+8` public inputs (the published authority root), and the gadget's
constraints appended.

⚑ **`ranges` is deliberately UNTOUCHED.** The v1 `ranges` carrier is illegal on a GRADUATED v2
descriptor — `check_descriptor2` refuses any descriptor with a non-empty `hash_sites`/`ranges`
("v2 assembly requires a GRADUATED descriptor"). An earlier draft put the message-bit booleanity
there and would have been unassemblable by the deployed prover. Booleanity comes from the emitted
`binGate` instead, lifted to ℤ by `boolGate_exact` (`p`'s primality + the canonicality envelope) —
the same route `CapOpenEmit` uses for its mask bits. -/
def withTurnAuth (base : EffectVmDescriptor2) (nb : Nat) (turnIn : List Nat)
    (hIn : turnIn.length ≤ Dregg2.Circuit.DescriptorIR2.CHIP_RATE) : EffectVmDescriptor2 :=
  { base with
    traceWidth  := base.traceWidth + AUTH_SPAN nb
    piCount     := base.piCount + W
    constraints := base.constraints
      ++ lamportAuthConstraints base.traceWidth nb base.piCount turnIn hIn }

-- A graduated v2 descriptor carries NO v1 range/hash-site carriers; the deployed
-- `check_descriptor2` refuses one that does.
#guard (withTurnAuth ⟨"b", 3, 0, [], [], [], []⟩ NB [0, 1, 2] (by decide)).ranges.isEmpty
#guard (withTurnAuth ⟨"b", 3, 0, [], [], [], []⟩ NB [0, 1, 2] (by decide)).hashSites.isEmpty

/-- Every base constraint survives the widening (so every existing keystone lifts verbatim). -/
theorem withTurnAuth_base_constraints (base : EffectVmDescriptor2) (nb : Nat) (turnIn : List Nat)
    (hIn : turnIn.length ≤ Dregg2.Circuit.DescriptorIR2.CHIP_RATE)
    (c : VmConstraint2) (hc : c ∈ base.constraints) :
    c ∈ (withTurnAuth base nb turnIn hIn).constraints :=
  List.mem_append_left _ hc

/-- Every gadget constraint is in the widened descriptor. -/
theorem withTurnAuth_auth_constraints (base : EffectVmDescriptor2) (nb : Nat) (turnIn : List Nat)
    (hIn : turnIn.length ≤ Dregg2.Circuit.DescriptorIR2.CHIP_RATE)
    (c : VmConstraint2)
    (hc : c ∈ lamportAuthConstraints base.traceWidth nb base.piCount turnIn hIn) :
    c ∈ (withTurnAuth base nb turnIn hIn).constraints :=
  List.mem_append_right _ hc

/-! ### Membership of each generated block in the gadget's constraint list. -/

theorem mem_sigLookups (w nb k : Nat) (hk : k < ELL nb) :
    wideHash (padTo16 w nb (gcols (sigG w nb k))) (gcols (sigHG w nb k)) ∈ sigLookups w nb :=
  List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩

theorem mem_selectGates (w nb k : Nat) (hk : k < ELL nb) (j : Fin W) :
    cgH (selectHead w nb k j) ∈ selectGates w nb :=
  List.mem_flatMap.mpr ⟨k, List.mem_range.mpr hk,
    List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩⟩

theorem mem_pairLookups (w nb k : Nat) (hk : k < ELL nb) :
    wideHash (padTo16 w nb (gcols (pk0G w nb k) ++ gcols (pk1G w nb k))) (gcols (pairG w nb k))
      ∈ pairLookups w nb :=
  List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩

theorem mem_accLookups (w nb k : Nat) (hk1 : 1 ≤ k) (hk : k < ELL nb) :
    wideHash (padTo16 w nb (foldIns w nb k)) (gcols (accG w nb k))
      (padTo16_admitted _ _ _ (foldIns_length_le w nb k)) ∈ accLookups w nb := by
  -- ⚠ substitute `k = j + 1` rather than rewriting `k - 1 + 1 = k`: the admission proof now
  -- DEPENDS on `k`, so the rewrite motive is not type correct.
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  exact List.mem_map.mpr ⟨j, List.mem_range.mpr (by omega), rfl⟩

theorem mem_authRootPins (w nb pcBase : Nat) (j : Fin W) :
    (VmConstraint2.base (.piBinding VmRow.first (accG w nb (ELL nb - 1) j) (pcBase + j.val)))
      ∈ authRootPins w nb pcBase :=
  List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩

theorem mem_msgReconGates (w nb q : Nat) (hq : q < nb) :
    cgH (reconHead w nb q) ∈ msgReconGates w nb :=
  List.mem_map.mpr ⟨q, List.mem_range.mpr hq, rfl⟩

/-! ### Lifting each block into `lamportAuthConstraints` (nine left-associated appends). -/

theorem auth_mem_sig (w nb pcBase : Nat) (turnIn : List Nat)
    (hIn : turnIn.length ≤ Dregg2.Circuit.DescriptorIR2.CHIP_RATE) (k : Nat) (hk : k < ELL nb) :
    wideHash (padTo16 w nb (gcols (sigG w nb k))) (gcols (sigHG w nb k))
      ∈ lamportAuthConstraints w nb pcBase turnIn := by
  simp only [lamportAuthConstraints, List.mem_append]
  exact .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (mem_sigLookups w nb k hk)))))))))

theorem auth_mem_select (w nb pcBase : Nat) (turnIn : List Nat)
    (hIn : turnIn.length ≤ Dregg2.Circuit.DescriptorIR2.CHIP_RATE) (k : Nat) (hk : k < ELL nb)
    (j : Fin W) : cgH (selectHead w nb k j) ∈ lamportAuthConstraints w nb pcBase turnIn := by
  simp only [lamportAuthConstraints, List.mem_append]
  exact .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inr (mem_selectGates w nb k hk j)))))))))

theorem mem_msgBitGates (w nb k : Nat) (hk : k < ELL nb) :
    binGate (mCol w nb k) ∈ msgBitGates w nb :=
  List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩

theorem auth_mem_msgbit (w nb pcBase : Nat) (turnIn : List Nat)
    (hIn : turnIn.length ≤ Dregg2.Circuit.DescriptorIR2.CHIP_RATE) (k : Nat) (hk : k < ELL nb) :
    binGate (mCol w nb k) ∈ lamportAuthConstraints w nb pcBase turnIn := by
  simp only [lamportAuthConstraints, List.mem_append]
  exact .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inr (mem_msgBitGates w nb k hk))))))))

theorem auth_mem_pair (w nb pcBase : Nat) (turnIn : List Nat)
    (hIn : turnIn.length ≤ Dregg2.Circuit.DescriptorIR2.CHIP_RATE) (k : Nat) (hk : k < ELL nb) :
    wideHash (padTo16 w nb (gcols (pk0G w nb k) ++ gcols (pk1G w nb k))) (gcols (pairG w nb k))
      ∈ lamportAuthConstraints w nb pcBase turnIn := by
  simp only [lamportAuthConstraints, List.mem_append]
  exact .inl (.inl (.inl (.inl (.inl (.inl (.inr (mem_pairLookups w nb k hk)))))))

theorem auth_mem_acc (w nb pcBase : Nat) (turnIn : List Nat)
    (hIn : turnIn.length ≤ Dregg2.Circuit.DescriptorIR2.CHIP_RATE) (k : Nat) (hk1 : 1 ≤ k)
    (hk : k < ELL nb) :
    wideHash (padTo16 w nb (foldIns w nb k)) (gcols (accG w nb k))
      (padTo16_admitted _ _ _ (foldIns_length_le w nb k))
      ∈ lamportAuthConstraints w nb pcBase turnIn hIn := by
  simp only [lamportAuthConstraints, List.mem_append]
  exact .inl (.inl (.inl (.inl (.inl (.inr (mem_accLookups w nb k hk1 hk))))))

theorem auth_mem_root (w nb pcBase : Nat) (turnIn : List Nat)
    (hIn : turnIn.length ≤ Dregg2.Circuit.DescriptorIR2.CHIP_RATE) (j : Fin W) :
    (VmConstraint2.base (.piBinding VmRow.first (accG w nb (ELL nb - 1) j) (pcBase + j.val)))
      ∈ lamportAuthConstraints w nb pcBase turnIn := by
  simp only [lamportAuthConstraints, List.mem_append]
  exact .inl (.inl (.inl (.inl (.inr (mem_authRootPins w nb pcBase j)))))

theorem auth_mem_turn (w nb pcBase : Nat) (turnIn : List Nat)
    (hIn : turnIn.length ≤ Dregg2.Circuit.DescriptorIR2.CHIP_RATE) :
    turnDigestLookup w nb turnIn ∈ lamportAuthConstraints w nb pcBase turnIn := by
  simp only [lamportAuthConstraints, List.mem_append]
  exact .inl (.inl (.inl (.inr (by simp))))

theorem auth_mem_recon (w nb pcBase : Nat) (turnIn : List Nat)
    (hIn : turnIn.length ≤ Dregg2.Circuit.DescriptorIR2.CHIP_RATE) (q : Nat) (hq : q < nb) :
    cgH (reconHead w nb q) ∈ lamportAuthConstraints w nb pcBase turnIn := by
  simp only [lamportAuthConstraints, List.mem_append]
  exact .inl (.inl (.inr (mem_msgReconGates w nb q hq)))

theorem auth_mem_zpad (w nb pcBase : Nat) (turnIn : List Nat)
    (hIn : turnIn.length ≤ Dregg2.Circuit.DescriptorIR2.CHIP_RATE) :
    cgH (Head.lin 1 (zpadCol w nb)) ∈ lamportAuthConstraints w nb pcBase turnIn := by
  simp only [lamportAuthConstraints, List.mem_append]
  exact .inr (by simp [zpadGates])

/-- **`authCore_of_satisfied` — `AuthCore` is DERIVED, not carried.** On row 0 of any real (≥2-row)
trace satisfying the widened descriptor, every gadget constraint bites: `isFirst = true` (the
authority-root PI pins fire) and `isLast = false` (the gates are on their active domain). -/
theorem authCore_of_satisfied (base : EffectVmDescriptor2) (nb : Nat) (turnIn : List Nat)
    (hIn : turnIn.length ≤ Dregg2.Circuit.DescriptorIR2.CHIP_RATE)
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hsat : Satisfied2 hash (withTurnAuth base nb turnIn hIn) minit mfin maddrs t)
    (hlen : 2 ≤ t.rows.length) (hcanon : AuthRowCanon (envAt t 0)) :
    AuthCore t.tf base.traceWidth nb base.piCount turnIn (envAt t 0) := by
  have hi : 0 < t.rows.length := by omega
  have hnotlast : ((0 : Nat) + 1 == t.rows.length) = false := by
    simp only [beq_eq_false_iff_ne]; omega
  have hrow := fun c hc => hsat.rowConstraints 0 hi c
    (withTurnAuth_auth_constraints base nb turnIn hIn c hc)
  set w := base.traceWidth
  set pc := base.piCount
  refine { sigHashed := ?_, selectZero := ?_, msgBool := ?_, pairHashed := ?_
         , accHashed := ?_, rootPinned := ?_, turnHashed := ?_, reconZero := ?_
         , zpadZero := ?_ }
  · intro k hk
    have h := hrow _ (auth_mem_sig w nb pc turnIn hIn k hk)
    exact h
  · intro k hk j
    have h := hrow _ (auth_mem_select w nb pc turnIn hIn k hk j)
    simp only [cgH, cg, VmConstraint2.holdsAt, VmConstraint.holdsVm, hnotlast] at h
    rwa [headToExpr_eval] at h
  · intro k hk
    have h := hrow _ (auth_mem_msgbit w nb pc turnIn hIn k hk)
    simp only [binGate, cg, gBin, VmConstraint2.holdsAt, VmConstraint.holdsVm, hnotlast,
      Dregg2.Exec.CircuitEmit.EmittedExpr.eval] at h
    exact boolExact (hcanon.cells _) h
  · intro k hk
    exact hrow _ (auth_mem_pair w nb pc turnIn hIn k hk)
  · intro k hk1 hk
    exact hrow _ (auth_mem_acc w nb pc turnIn hIn k hk1 hk)
  · intro j
    have h := hrow _ (auth_mem_root w nb pc turnIn hIn j)
    simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm] at h
    exact h rfl
  · exact fun _ => hrow _ (auth_mem_turn w nb pc turnIn hIn)
  · intro q hq
    have h := hrow _ (auth_mem_recon w nb pc turnIn hIn q hq)
    simp only [cgH, cg, VmConstraint2.holdsAt, VmConstraint.holdsVm, hnotlast] at h
    rwa [headToExpr_eval] at h
  · have h := hrow _ (auth_mem_zpad w nb pc turnIn hIn)
    simp only [cgH, cg, VmConstraint2.holdsAt, VmConstraint.holdsVm, hnotlast] at h
    rw [headToExpr_eval] at h
    simp only [evalH_lin, one_mul] at h
    exact diffExact (hcanon.cells _) ⟨le_refl 0, by norm_num [P]⟩ (by simpa using h)

#assert_axioms authCore_of_satisfied

/-- **`turn_auth_forced` — the whole rung, from the DEPLOYED denotation.** A `Satisfied2` witness of
any descriptor widened by `withTurnAuth` carries, at every one of the `ELL nb` bit positions, a
Poseidon2 preimage of the public-key entry for that bit — i.e. `HashSig.verify`. No carried
hypothesis but the canonicality envelope (which is what a BabyBear trace IS) and the chip's own
soundness (the lever the cap crown already rides). -/
theorem turn_auth_forced (permOut : List ℤ → List ℤ) (base : EffectVmDescriptor2) (nb : Nat)
    (turnIn : List Nat)
    (hIn : turnIn.length ≤ Dregg2.Circuit.DescriptorIR2.CHIP_RATE) (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : VmTrace)
    (hChip : ChipTableSoundN permOut (t.tf TableId.poseidon2))
    (hsat : Satisfied2 hash (withTurnAuth base nb turnIn hIn) minit mfin maddrs t)
    (hlen : 2 ≤ t.rows.length)
    (hcanon : AuthRowCanon (envAt t 0)) :
    Dregg2.Crypto.HashSig.verify (Hsig permOut)
      (pkOf (envAt t 0) base.traceWidth nb)
      (msgOf (envAt t 0) base.traceWidth nb)
      (sigOf (envAt t 0) base.traceWidth nb) :=
  lamport_verify_forced permOut t.tf base.traceWidth nb base.piCount turnIn hIn (envAt t 0) hChip
    (authCore_of_satisfied base nb turnIn hIn hash minit mfin maddrs t hsat hlen hcanon) hcanon

#assert_axioms turn_auth_forced

/-! ## §9 — THE WELD: the signed message IS the turn identity, so `actor` and `dst` stop being free.

`transferCapOpenTB` publishes `actor` (col 928) and `dst` (col 929) to PI 47/48 from columns NO
OTHER CONSTRAINT MENTIONS — measured, one `pi_binding` each and nothing else. They are free because
NOTHING SIGNS THEM. Here they are inputs to `turnDigestLookup`, whose output is bit-decomposed into
the very bits the signature opens: move one and the signed message moves with it. -/

/-- The recomposition head evaluates to `Σ_{i<31} 2ⁱ·m[31q+i] − td[q]`. -/
theorem reconHead_eval (a : Assignment) (w nb q : Nat) :
    evalH (reconHead w nb q) a
      = ((List.range BLOCK_BITS).map
          (fun i => (2 : ℤ) ^ i * a (mCol w nb (BLOCK_BITS * q + i)))).sum
        - a (tdCol w nb q) := by
  simp only [reconHead, evalH_addLin]
  rw [evalH_foldl_addLinG]
  simp only [evalH_zero, zero_add]
  ring

/-- The signed-message value of block `q`. -/
def msgSum (a : Assignment) (w nb q : Nat) : ℤ :=
  ((List.range BLOCK_BITS).map
    (fun i => (2 : ℤ) ^ i * a (mCol w nb (BLOCK_BITS * q + i)))).sum

/-- The absorbed block of the turn-identity lookup: the turn columns' values followed by the fixed
zero tail that lifts the absorb to the `node8` arity 16. -/
def turnAbsorb (a : Assignment) (turnIn : List Nat) : List ℤ :=
  turnIn.map a ++ List.replicate (Dregg2.Circuit.DescriptorIR2.CHIP_RATE - turnIn.length) 0

/-- **`turn_digest_forced`** — the message-digest felts ARE the deployed Poseidon2 of the TURN
IDENTITY columns. `turnIn` is where `src`, `actor` and `dst` enter. -/
theorem turn_digest_forced (permOut : List ℤ → List ℤ)
    (tf : Dregg2.Circuit.DescriptorIR2.TraceFamily) (w nb pcBase : Nat) (turnIn : List Nat)
    (env : VmRowEnv)
    (hChip : ChipTableSoundN permOut (tf TableId.poseidon2))
    (hcore : AuthCore tf w nb pcBase turnIn env)
    (hlenIn : turnIn.length ≤ Dregg2.Circuit.DescriptorIR2.CHIP_RATE) :
    (tdCols w nb).map env.loc = permOut (turnAbsorb env.loc turnIn) := by
  have h := wideHash_forces permOut tf env hChip (padTo16 w nb turnIn) (tdCols w nb)
    (padTo16_admitted w nb turnIn hlenIn)
    (by rw [padTo16_length _ _ _ hlenIn])
    (hcore.turnHashed (padTo16_admitted w nb turnIn hlenIn))
  rwa [padTo16_vals env.loc w nb turnIn hcore.zpadZero] at h

/-- **`msg_recomposes`** — the signed bits recompose to the turn-digest felts, mod `p`. -/
theorem msg_recomposes (tf : Dregg2.Circuit.DescriptorIR2.TraceFamily) (w nb pcBase : Nat)
    (turnIn : List Nat) (env : VmRowEnv) (hcore : AuthCore tf w nb pcBase turnIn env)
    (q : Nat) (hq : q < nb) :
    msgSum env.loc w nb q ≡ env.loc (tdCol w nb q) [ZMOD 2013265921] := by
  have h := hcore.reconZero q hq
  rw [reconHead_eval] at h
  have := Int.ModEq.add_right (env.loc (tdCol w nb q)) h
  simpa [msgSum, sub_add_cancel] using this

/-- Message bits agreeing as BOOLEANS means the columns agree as integers (booleanity from the
deployed 1-bit range tooth). -/
theorem msgCol_eq_of_msgOf_eq (tf tf' : Dregg2.Circuit.DescriptorIR2.TraceFamily)
    (w nb pcBase : Nat) (turnIn : List Nat) (env env' : VmRowEnv)
    (hcore : AuthCore tf w nb pcBase turnIn env) (hcore' : AuthCore tf' w nb pcBase turnIn env')
    (k : Nat) (hk : k < ELL nb)
    (hsame : msgOf env w nb ⟨k, hk⟩ = msgOf env' w nb ⟨k, hk⟩) :
    env.loc (mCol w nb k) = env'.loc (mCol w nb k) := by
  have hb := hcore.msgBool k hk
  have hb' := hcore'.msgBool k hk
  simp only [msgOf, decide_eq_decide] at hsame
  rcases hb with h0 | h1 <;> rcases hb' with h0' | h1' <;> simp_all

/-- **`same_msg_same_turn_digest`** — if two witnesses sign the SAME bits then the deployed hash of
their turn-identity columns is the SAME value. Contrapositive: a witness whose turn identity hashes
differently MUST sign different bits. -/
theorem same_msg_same_turn_digest (permOut : List ℤ → List ℤ)
    (tf : Dregg2.Circuit.DescriptorIR2.TraceFamily) (w nb pcBase : Nat) (turnIn : List Nat)
    (env env' : VmRowEnv)
    (hChip : ChipTableSoundN permOut (tf TableId.poseidon2))
    (hcore : AuthCore tf w nb pcBase turnIn env) (hcore' : AuthCore tf w nb pcBase turnIn env')
    (hcanon : AuthRowCanon env) (hcanon' : AuthRowCanon env')
    (hlenIn : turnIn.length ≤ Dregg2.Circuit.DescriptorIR2.CHIP_RATE)
    -- ⚑ the DEPLOYED instance: every one of the chip's 8 squeezed digest felts is signed. Without
    -- this the message covers only `nb` of them and the weld leaks.
    (hnb : nb = W)
    (hsame : ∀ k : Fin (ELL nb), msgOf env w nb k = msgOf env' w nb k) :
    permOut (turnAbsorb env.loc turnIn) = permOut (turnAbsorb env'.loc turnIn) := by
  -- (1) equal bits as booleans ⇒ equal bit COLUMNS as integers ⇒ equal recomposition sums.
  have hcols : ∀ k, ∀ hk : k < ELL nb, env.loc (mCol w nb k) = env'.loc (mCol w nb k) :=
    fun k hk => msgCol_eq_of_msgOf_eq tf tf w nb pcBase turnIn env env' hcore hcore' k hk
      (hsame ⟨k, hk⟩)
  have hsum : ∀ q < nb, msgSum env.loc w nb q = msgSum env'.loc w nb q := by
    intro q hq
    unfold msgSum
    refine congrArg List.sum (List.map_congr_left ?_)
    intro i hi
    have hik : BLOCK_BITS * q + i < ELL nb := by
      have hi' : i < BLOCK_BITS := List.mem_range.mp hi
      have : BLOCK_BITS * q + i < BLOCK_BITS * q + BLOCK_BITS := by omega
      calc BLOCK_BITS * q + i < BLOCK_BITS * q + BLOCK_BITS := this
        _ = BLOCK_BITS * (q + 1) := by ring
        _ ≤ BLOCK_BITS * nb := Nat.mul_le_mul_left _ (by omega)
    rw [hcols _ hik]
  -- (2) equal sums + the mod-`p` recomposition + canonicality ⇒ equal turn-digest felts.
  have htd : ∀ q < nb, env.loc (tdCol w nb q) = env'.loc (tdCol w nb q) := by
    intro q hq
    have h1 := msg_recomposes tf w nb pcBase turnIn env hcore q hq
    have h2 := msg_recomposes tf w nb pcBase turnIn env' hcore' q hq
    rw [hsum q hq] at h1
    have hcong : env.loc (tdCol w nb q) ≡ env'.loc (tdCol w nb q) [ZMOD 2013265921] :=
      h1.symm.trans h2
    refine diffExact (hcanon.cells _) (hcanon'.cells _) ?_
    have := Int.ModEq.sub hcong (Int.ModEq.refl (env'.loc (tdCol w nb q)))
    simpa using this
  -- (3) equal digest felts ⇒ the two wide lookups force the same permutation output.
  have hlk := turn_digest_forced permOut tf w nb pcBase turnIn env hChip hcore hlenIn
  have hlk' := turn_digest_forced permOut tf w nb pcBase turnIn env' hChip hcore' hlenIn
  rw [← hlk, ← hlk']
  refine List.map_congr_left ?_
  intro c hc
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hc
  exact htd q (by rw [hnb]; exact List.mem_range.mp hq)

/-- **`moved_turn_needs_different_bits` — THE WELD, stated as a tooth.** A witness whose TURN
IDENTITY hashes to something else — because `actor` moved, or `dst` moved, or `src` moved — MUST
sign a different message bit. `actor` and `dst` are no longer publishable at will: they are
arguments of the hash whose bits the signature opens. -/
theorem moved_turn_needs_different_bits (permOut : List ℤ → List ℤ)
    (tf : Dregg2.Circuit.DescriptorIR2.TraceFamily) (w nb pcBase : Nat) (turnIn : List Nat)
    (env env' : VmRowEnv)
    (hChip : ChipTableSoundN permOut (tf TableId.poseidon2))
    (hcore : AuthCore tf w nb pcBase turnIn env) (hcore' : AuthCore tf w nb pcBase turnIn env')
    (hcanon : AuthRowCanon env) (hcanon' : AuthRowCanon env')
    (hlenIn : turnIn.length ≤ Dregg2.Circuit.DescriptorIR2.CHIP_RATE) (hnb : nb = W)
    (hmoved : permOut (turnAbsorb env.loc turnIn) ≠ permOut (turnAbsorb env'.loc turnIn)) :
    ∃ k : Fin (ELL nb), msgOf env' w nb k ≠ msgOf env w nb k := by
  by_contra hall
  refine hmoved (same_msg_same_turn_digest permOut tf w nb pcBase turnIn env env' hChip hcore hcore'
    hcanon hcanon' hlenIn hnb ?_)
  intro k
  by_contra hk
  exact hall ⟨k, fun h => hk h.symm⟩

/-- **`air_forgery_breaks_hash` — moving the turn costs a HASH BREAK, not a re-sign.** Compose the
weld with the emitted verify and the already-proved Lamport tooth: a witness that signs a bit the
owner did not sign hits the hash of a preimage the owner NEVER revealed — so it either produced that
unrevealed preimage, or produced a distinct value with the same Poseidon2 image. There is no third
option, and neither is available to a prover that lacks the owner's secret. -/
theorem air_forgery_breaks_hash (permOut : List ℤ → List ℤ) (base : EffectVmDescriptor2) (nb : Nat)
    (turnIn : List Nat)
    (hIn : turnIn.length ≤ Dregg2.Circuit.DescriptorIR2.CHIP_RATE) (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : VmTrace)
    (hChip : ChipTableSoundN permOut (t.tf TableId.poseidon2))
    (hsat : Satisfied2 hash (withTurnAuth base nb turnIn hIn) minit mfin maddrs t)
    (hlen : 2 ≤ t.rows.length)
    (hcanon : AuthRowCanon (envAt t 0))
    -- the owner's authority key is an honest Lamport public key (the light client's anchor names it)
    (sk : Dregg2.Crypto.HashSig.SecretKey (List ℤ) (ELL nb))
    (hpk : pkOf (envAt t 0) base.traceWidth nb
      = Dregg2.Crypto.HashSig.publicKey (Hsig permOut) sk)
    -- the bits the OWNER actually signed, and a position where this witness disagrees
    (m : Fin (ELL nb) → Bool) (k : Fin (ELL nb))
    (hne : msgOf (envAt t 0) base.traceWidth nb k ≠ m k) :
    Hsig permOut (sigOf (envAt t 0) base.traceWidth nb k)
        = Hsig permOut (sk.pre k (msgOf (envAt t 0) base.traceWidth nb k))
      ∧ (sigOf (envAt t 0) base.traceWidth nb k
            = sk.pre k (msgOf (envAt t 0) base.traceWidth nb k)
         ∨ (sigOf (envAt t 0) base.traceWidth nb k
              ≠ sk.pre k (msgOf (envAt t 0) base.traceWidth nb k)
            ∧ Hsig permOut (sigOf (envAt t 0) base.traceWidth nb k)
                = Hsig permOut (sk.pre k (msgOf (envAt t 0) base.traceWidth nb k)))) := by
  have hver := turn_auth_forced permOut base nb turnIn hIn hash minit mfin maddrs t hChip hsat hlen
    hcanon
  rw [hpk] at hver
  exact Dregg2.Crypto.HashSig.lamport_forgery_breaks_hash (Hsig permOut) sk m
    (msgOf (envAt t 0) base.traceWidth nb) k hne (sigOf (envAt t 0) base.traceWidth nb) hver

#assert_axioms reconHead_eval
#assert_axioms turn_digest_forced
#assert_axioms msg_recomposes
#assert_axioms same_msg_same_turn_digest
#assert_axioms moved_turn_needs_different_bits
#assert_axioms air_forgery_breaks_hash

end Dregg2.Circuit.Emit.TurnAuthLamportEmit
