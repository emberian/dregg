/-
# `Dregg2.Circuit.Emit.LightClientMinaLinkAir` — the Mina exhibited SEGMENT, multi-row, compiled.

⚑ SUBSTRATE, SAID OUT LOUD (House Law #1): this is a Lean-authored AIR. `minaLinkDesc` is
`EffectLower.lowerAir` applied to the `EffectAir` source `minaLinkAir` (§3). There is **no
hand-written `VmConstraint2` in this file.** Rust only reads the emitted bytes.

## What this rung is, and — first — what it is NOT

`LightClientMinaAir` publishes three carriers. `CANON_OK` stopped being a witness on 2026-08-03.
`LINK_OK` and `PICKLES_OK` did not. This file takes the FIRST HALF of `LINK_OK` and no more, and the
split is the whole point of the file, so it is stated before the construction:

`LightClientMina.chainLinked` (`Bridge/LightClientMina.lean:202`) is three conjuncts per block:

    (i)   h.parent  =  prev                       -- the running state hash IS this block's parent
    (ii)  h.height  =  ph + 1                     -- height contiguity
    (iii) prev'     :=  blockHash L h             -- and the running value is Poseidon(stateRow h)

⚑ **(i) and (ii) are equality and addition. (iii) is Mina's Poseidon over Pasta `Fp`.** This file
derives (i) and (ii) — over nine-lane `Fp` columns, multi-row, one row per exhibited block — and
derives the SEGMENT LENGTH besides.

⚑⚑ **AND SINCE 2026-08-06 IT DERIVES (iii) TOO — by RECURSION, not by a bigger circuit.** Every row
carries a `proofBind` whose commitment is `salt ‖ PARENT ‖ BODYHASH ‖ OWNHASH`, fifty-four
`Faithful9` lanes, against the pinned fingerprint of `dregg-pasta-fp-absorb::v1`. `OWNHASH` is
CO-COMMITTED with its row and DERIVED in the sibling `fp-absorb` sub-proof, at the recursion
boundary every `proofBind` in this tree stands at (`seam_derives_the_own_hash`, §6).

⚠ **CLOSURE KIND, CORRECTED 2026-08-08. This read "`OWNHASH` is the IMAGE of its row", which is an
in-AIR functional relation and is not the mechanism.** The bind declares `bound := none`, and
`circuit/src/descriptor_ir2.rs`'s `proofBind` arm emits polynomials over `commit` only under
`if let Some(b) = &p.bound` — so the fifty-four lanes appear in NO emitted constraint. What derives
the hash is the sibling STARK a consumer verifies, and `seam_derives_the_own_hash` takes
`StateHashEngine` as a NAMED HYPOTHESIS rather than discharging it. Connectivity here is
co-occurrence plus a consumer refusal. The predicate `linkShapeAccepts` keeps its name because what a
ROW-LOCAL predicate can see of a seam is still only its shape.

## ⚑ Why (iii) was called a wall, and what re-deriving the price found — 2026-08-06

This header used to read: *"a Pasta multiplication at BabyBear is ~10³ constraints; one
Poseidon-over-Pasta permutation is ~500 of them, so ~5·10⁵ BabyBear constraints per block hash, and
a Samasika-depth segment is ~1.5·10⁸ for the linkage hash alone."* Both factors were wrong, in the
same direction, and the second by 26×.

⚑ **THE PERMUTATION COUNT IS 1 PER BLOCK.** `Bridge/MinaStateHashDerive.lean:31` reads the daemon
(`protocol_state.ml:45-55`):

    state_hash = Poseidon_Fp( salt "MinaProtoState" )[ previous_state_hash ; state_body_hash ]

TWO field elements at rate 2 is ONE block and ONE permutation, and the salt is a CONSTANT permuted
at emit time. The `~26 permutations a block` the standing estimate carried is the *transcript*
chain's link count (27 in phase 1, 46 in phase 2), not the state hash. The deep hash is
`state_body_hash` — and it is not part of the LINKAGE: it enters as a witnessed nonet whose
attestation is `PICKLES_OPENING_WITNESSED` (⚑ `PICKLES_WITNESSED` until 2026-08-06), exactly as
before.

⚑ **AND THE CIRCUIT DID NOT NEED BUILDING.** `dregg-pasta-fp-absorb::v1` is emitted, fingerprinted
and PROVES: 2 048 rows × 469 columns, 858 constraints, whose 660 ROM immediates are `fp_kimchi`'s
own `static_params()` checked on the emitted bytes. It computes `perm(state + [x₀,x₁,0])`, its
incoming state is a PUBLIC INPUT rather than a descriptor constant, and
`MinaWrapVerifierSpongeFp.the_absorb_program_permutes_gen` carries **no hypothesis on that state** —
so a *salted* sponge is the same descriptor with different public inputs, which is what
`MinaPhase1Chain` already does for 27 links. Re-derived segment cost at that family's measured
leaf/fold times (9.5 s a leaf, 11.5 s a fold node): 290 leaves + 289 folds ≈ **1 h 41 min** against
the inherited **44 h**. ⚠ An extrapolation from a same-shaped descriptor, not a measured 290-leaf
run, and labelled as one.

⚑ **NOTHING NON-NATIVE IS AUTHORED HERE.** The Pasta cone whose emitted form is unsound
(`pastaLimbRange` emitted nowhere, the RCB carry columns not boolean-pinned) is untouched:
`minaLinkDesc` still contains no multiplication of two distinct witness columns anywhere
(`minaLink_products_are_only_the_real_bit`, §3b). The multiply lives in the BOUND SUB-PROOF, whose
program identity is pinned lane by lane.

## ⚑ What `dregg-turn-chain-binding-v2` actually contributed — the transfer, measured

`EffectVmEmitTurnChainBinding` is a multi-row binding descriptor with a per-row leaf and a recursion
tree, and its shape transfers ALMOST WHOLE. Site by site
(`Dregg2/Circuit/Emit/EffectVmEmitTurnChainBinding.lean`):

    turn-chain site                          this file                              Pasta mul?
    ───────────────────────────────────────────────────────────────────────────────────────────
    rootContinuity     (:100)   new_root[i]=old_root[i+1]   OWNHASH[i]=PARENT[i+1] ×9   NO
    firstOldRootBind   (:106)   old_root[0]=pi              PARENT[0]=PI_ANCHOR    ×9   NO
    lastNewRootBind    (:110)   new_root[last]=pi           OWNHASH[last]=PI_TIP   ×9   NO
    firstIdxZero       (:137)   idx[0]=0                    HEIGHT[0]=ANCHOR_H+1        NO
    idxIncrement       (:141)   idx[i+1]=idx[i]+1           HEIGHT[i+1]=HEIGHT[i]+1     NO
    isRealBoolean      (:150)   is_real ∈ {0,1}             same                        NO
    realMonotone       (:158)   real rows are a prefix      same                        NO
    firstRealCount     (:166)   real_count[0]=is_real[0]    same                        NO
    realCountAccum     (:171)   real_count accumulates      same                        NO
    lastRealCountBind  (:180)   real_count[last]=pi         REAL_COUNT[last]=PI_SEG_LEN NO
    perRowHash         (:129)   acc=Poseidon2(acc,…)        ⚠ NOT TRANSFERRED — see below
    ───────────────────────────────────────────────────────────────────────────────────────────

⚑ **The finding, and it corrects the survey that opened this lane.** The survey said "swap 'turn' for
'Mina block' and it is an emit-and-wire job." That is RIGHT about the chaining and it buys less than
it sounds, because **`dregg-turn-chain-binding-v2` never computes the values it chains.** Its
`old_root`/`new_root` are field elements chained by EQUALITY (`rootContinuity` is `loc c1 − nxt c0`,
one subtraction); its one hash site is a *native BabyBear* Poseidon2 accumulator over the row
(`acc_out = Poseidon2([acc_in, old_root, new_root, idx])`), which digests the chain but does not
produce it. So turn-chain-binding transfers COMPLETELY for the equality/counting half and contributes
**nothing at all** to the hash half — it has no hash half to contribute. The blocker was never that
the descriptor was single-row; single-row was the blocker for (i)/(ii), and this file removes it.
(iii) was never in the donor.

`perRowHash` is deliberately not transferred: a native accumulator here would digest the chain into
one felt, which is a *convenience* for a recursion seam and not a binding, and this file has no
recursion seam to feed yet. Adding it would be a column that computes something nobody reads.

## ⚑ THE TOOTH THIS ACTUALLY CLOSES: `SEG_LEN` stops being a free felt

`LightClientMinaAir`'s §"THE TOOTH" says the published `blockchain_length` is DERIVED, not witnessed:

    G1   BLOCK_LEN = ANCHOR_H + SEG_LEN

and concludes *"a prover that exhibits `n` blocks above the pinned anchor can publish exactly
`anchorH + n`."* ⚠ **That conclusion does not hold of that descriptor, and the reason is structural:
`SEG_LEN` is column 0, a free witness, and the descriptor is SINGLE-ROW — it has no exhibited
blocks.** The only thing constraining `SEG_LEN` there is `segSlackC` (`SEG_SLACK + 1 = SEG_LEN`) with
`SEG_SLACK` ranged into `[0, 2^24)`, so `SEG_LEN` is free in `[1, 2^24]` and `BLOCK_LEN` with it.
`minaLcAir_no_forgery` is honest about this in the only place it can be — `hsl : a SEG_LEN =
u.blocks.length` is a HYPOTHESIS, discharged by the witness generator, not by a gate. The docblock's
sentence is stronger than the theorem beneath it.

Here `SEG_LEN` is `REAL_COUNT` on the last row (`lastRealCountBind`'s analog), and `REAL_COUNT`
accumulates `IS_REAL` across rows that are `0/1`-pinned and monotone. A prover claiming a
290-deep segment must commit a trace carrying 290 real rows, each with nine canonical `PARENT` lanes
and nine canonical `OWNHASH` lanes that chain into its neighbour and a height that ticks.
`link_seg_len_counts_the_real_rows` is that as a theorem. **That is the depth evidence
`LightClientMina.mina_depth_is_witnessed` claims and the single-row descriptor could not deliver.**

## ⚑ THE COUPLING: the canonicality rung is what makes this linkage EXACT

An emitted gate forces its body `≡ 0 [ZMOD P]`, not `= 0`. So `OWNHASH[i] ≡ PARENT[i+1]` alone
admits a `+P` alias per lane — nine independent aliasing lanes, one addition each. The linkage is an
EXACT equality only because every lane is range-gated below `2^29 < P` by the same `.limbs` /
narrow-lookup gadget `LightClientMinaAir` §1a landed, which this file IMPORTS rather than copies
(`laneCanon`, `stateValue`, `mina_lane_canon_forces_canonical`). `link_lane_equality_is_exact` is the
statement; `linkAccepts_forces_exact_lane_chain` is where it is used. **Two rungs, one gadget.**

## Layout — one row per exhibited block

    col 0..8    PARENT[j]    the block's `previousStateHash`, nine base-`2^29` `Faithful9` lanes
    col 9..17   OWNHASH[j]   the block's OWN protocol-state hash, nine lanes.  ⚑ DERIVED — §6
    col 18      HEIGHT       `blockchainLength`
    col 19      IS_REAL      1 on an exhibited block, 0 on padding; real rows are a PREFIX
    col 20      REAL_COUNT   cumulative `IS_REAL`
    col 21      ANCHOR_H     the pinned anchor's height (read on the first row only)
    col 22..30  BODYHASH[j]  ⚑ the block's `state_body_hash`, nine lanes — the PREIMAGE
    col 31..39  HASH_VK[i]   ⚑ the attested state-hash program's nine fingerprint lanes

    PI 0..8     PI_ANCHOR[j] the operator-pinned weak-subjectivity anchor state hash
    PI 9..17    PI_TIP[j]    the verified head's state hash
    PI 18       PI_ANCHOR_H  the pinned anchor's height
    PI 19       PI_SEG_LEN   ⚑ the number of EXHIBITED blocks — now `REAL_COUNT` on the last row

Widths: lanes 0..7 at **29** bits (the last wrap-free width at BabyBear,
`RangeFieldContainment.wrap_free_iff_le_29`) and lane 8 at **22**, so `8·29 + 22 = 254` and
`2^254 < p_Pasta` exactly as in the sibling rung. Nothing here declares a width ≥ 30; the compiler
refuses one structurally (`LimbsLeg.mainRailOk`).

## Both polarities, on the emitted object

* ACCEPT — `honest_segment_accepted`: a three-block segment on the REAL devnet genesis anchor,
  chaining to a real tip, heights contiguous, `PI_SEG_LEN = 3`.
* REFUSE — `broken_link_refused`: the SAME segment with block 2's `PARENT` lane 0 bumped by one.
  Every canonicality lookup still passes (it is a canonical lane), every height still ticks, every
  carrier bit is whatever the prover likes — and the descriptor refuses it, because
  `OWNHASH[1] ≠ PARENT[2]`. ⚑ This is the forgery `LightClientMinaAir`'s witnessed `LINK_OK = 1`
  waves through, exhibited as a row pair rather than asserted.
  `broken_link_old_admits_new_rejects` states the pair.
* REFUSE — `short_segment_refused`: `PI_SEG_LEN` claimed 290 against three exhibited real rows.
  The free-depth liar.

## ⚑ WHAT THIS BREAKS (flag day, stated so it is findable)

**2026-08-06 — THE STATE-HASH SEAM. Say what re-emits, and what refuses rather than reinterprets.**

* `dregg-mina-lightclient-link::v1` **re-emits**: `trace_width` **22 → 40** (nine `BODYHASH`, nine
  `HASH_VK`), constraints **53 → 72** (eight body-lane lookups, one body top-lane lookup, nine
  program-lane lookups, one `proof_bind`), legs **39 → 43**. **`piCount` STAYS 20** and no PI slot
  moves — nothing new is published; a seam names columns, not public inputs. **Its VK rotates.**
* ⚠ A witness generator that leaves `HASH_VK 0..8` unfilled now produces an **UNSAT row**: the
  `vkPin` congruence is an emitted constraint, so a pre-flag-day 22-wide trace does not "verify
  weakly", it **fails to load** — `prove_vm_descriptor2` refuses a trace of the wrong width outright.
* `dregg-mina-lightclient-verify::v1` **re-emits and re-VKs**, because `LightClientMinaAir.LINK_VK_LANES`
  is the link descriptor's fingerprint and that moved. Same coupling `CHAINLINK_VK_LANES` already
  carries. **Every previously produced `MinaHeadProofWire` fails to verify.**
* `mina_head_predicate_vk()` is blake3 over the descriptor NAME, which did not move, so cell
  programs keep their pinned predicate vk and **nothing re-genesises.**
* `pasta-fp-absorb.json` is **unchanged** — it is the sub-program, not a new one — but it must join
  the by-name registry to be servable, and re-emitting it would move `ABSORB_VK_LANES` and cascade
  through both descriptors above. Three descriptors, one chain.

⚠ `circuit/descriptors/PROVENANCE.json` is already UNSTAMPED from the 2026-08-03 flag day and
`check-descriptor-drift.sh` is already RED; this adds a row to that ledger and the stamp remains the
operator's ceremony.

**2026-08-08 — THE FLAG DAY THIS RUNG DID *NOT* TAKE ON 08-07, TAKEN. `piCount` 20 → 37.**

`MinaStateBodyHashChain` derived `state_body_hash` on 08-07 and folded it, and nothing in this
descriptor related `BODYHASH` to that chain's root — because a `proofBind`'s `commit`/`vk` name
PUBLISHED values and these nine columns were read, joined and NOT PI-bound
(`LightClientAnchorConnectivity.minaLink_body_hash_is_joined_but_not_published`, whose third
conjunct is now REFUTED: `the_unpublished_body_hash_claim_is_now_refuted`). What landed:

* `BODYHASH 0..8` are **published** at PI slots 20..28, and the body-hash chain's **8-lane ordered
  transcript accumulator** at 29..36. `piCount` **20 → 37**. A recursion fold reads
  `air_public_targets`, so the weld to the chain's root is now REACHABLE — which is exactly what the
  unpublished shape forbade.
* ⚑ **THE SEAM BINDS THE ABSORBED STREAM, NOT `(salt, BODYHASH)`.** §2c's `bodyChainBindLeg`
  commits to `salt("MinaProtoStateBody") ‖ BODYHASH ‖ acc` — 27 constant lanes, 9 body-hash lanes,
  **8 accumulator lanes** — against `dregg-pasta-fp-chainlink::v1`'s fingerprint. The vacuity was
  named before it could be built: *"a bind of `(salt, BODYHASH)` alone would be VACUOUS … `perm` is
  a permutation, so 25 links from a fixed head with free absorbed inputs reach every field element.
  Naming the stream is the whole content."* `minaLink_body_chain_seam_binds_the_stream` pins the 44.

**WHAT RE-EMITS, WHAT RE-VKs, AND WHAT NOW REFUSES RATHER THAN REINTERPRETS:**

* `dregg-mina-lightclient-link::v1` **re-emits**: `trace_width` **40 → 57** (eight `BODY_ACC`, nine
  `CHAIN_VK`), `piCount` **20 → 37**, constraints **72 → 99** (nine program-lane lookups, one
  `proof_bind`, seventeen pins), legs **43 → 62**. **Its VK rotates.**
* ⚠ **THE OLD SHAPE FAILS TO LOAD, IT DOES NOT VERIFY WEAKLY.** `prove_vm_descriptor2` refuses a
  trace whose row width is not the descriptor's (`"base row width {} must equal descriptor
  trace_width {}"`) and refuses a public-input vector of the wrong length (`"public input count {}
  != descriptor public_input_count {}"`). A pre-flag-day 40-wide trace with 20 PIs hits BOTH. There
  is no path on which it is reinterpreted.
* `dregg-mina-lightclient-verify::v1` **re-emits and re-VKs**, because `LightClientMinaAir.
  LINK_VK_LANES` is this descriptor's fingerprint and that moved. **Every previously produced
  `MinaHeadProofWire` fails to verify.**
* `mina_head_predicate_vk()` is blake3 over the descriptor NAME, which did not move, so cell
  programs keep their pinned predicate vk and **nothing re-genesises.**
* `pasta-fp-chainlink.json` is **unchanged** — it is the bound sub-program, not a new one — and
  `FP_CHAINLINK_VK_LANES` is its fingerprint transcribed. Re-emitting IT would move that literal and
  cascade through both descriptors above. Four descriptors, one chain.
* ⚠ **RUST CONSUMERS THAT MUST MOVE WITH IT**, named so the break is findable rather than absent:
  `circuit-prove/tests/mina_link_segment_multirow.rs` (builds 40-wide rows and 20-PI vectors),
  `circuit/tests/mina_statehash_seam_proves.rs` (`proofBindsOf` is now TWO seams, not one),
  `circuit/tests/mina_transcript_carrier_binding.rs` (`LEAN_SEGMENT_VK_LANES` is the moved
  fingerprint) and `turn/src/executor/mina_head_verifier.rs`'s `MINA_LINK_DESCRIPTOR` path.

⚠ `circuit/descriptors/PROVENANCE.json` is already UNSTAMPED from the 2026-08-03 flag day and
`check-descriptor-drift.sh` is already RED; this adds rows to that ledger and the stamp remains the
operator's ceremony.

⚠ **AND WHAT PUBLICATION DOES *NOT* BUY, said in the same breath.** It buys the weld's
REACHABILITY. Until a fold `cb.connect`s these seventeen slots to the chain root's claim lanes, what
relates this nonet to that chain's root is still an EXECUTOR comparison — and the accumulator's own
tie to *this block's* preimage stays a comparison against `packToFields (bodyI decoded)`, a hash the
node computes from bytes it already holds.

## Scope — do NOT overclaim

⚠ This does **not** make the Mina light client's linkage verified. What a STARK over this descriptor
proves is: *there exists a sequence of `PI_SEG_LEN` canonical-`Fp` `(parent, bodyHash, ownHash)`
triples, running from `PI_ANCHOR` to `PI_TIP`, with contiguous heights, each recursion-bound to a
sub-proof of the pinned Poseidon-over-Pasta program.*

⚑ **CAN A PROVER STILL CHOOSE THE CHAIN'S HASHES? NO — and here is exactly what changed.** Before
today a prover picked every `OWNHASH` and therefore picked the TIP outright. Now the anchor is
pinned, each `OWNHASH` is `Poseidon_salt(PARENT, BODYHASH)`, and `PARENT[i+1] = OWNHASH[i]`, so the
whole chain — the tip included — is a FORWARD computation from the pinned anchor and the body
hashes. To publish a tip of its choosing a prover must invert Poseidon; to open one tip to two
histories it must collide it.

⚠ **WHAT THIS DESCRIPTOR CAN STILL CHOOSE IS `BODYHASH`**, and the residual moved on 2026-08-07
rather than closing. `state_body_hash`'s own preimage IS derived now — `MinaStateBodyHashChain`, 25
links of the deployed `dregg-pasta-fp-chainlink::v1` from the pinned `MinaProtoStateBody` salt over
the block's packed `Body.to_input`, proved and folded — so **the value a prover chooses moved from
one felt to that felt's 2 381-bit preimage.** Say it in those words: relocated, not eliminated.
⚠ **And the tie to THESE columns is not a constraint.** A `proofBind` can only name published
values and `BODYHASH` is not PI-bound here (`LightClientAnchorConnectivity.
minaLink_body_hash_is_joined_but_not_published`), so what relates this nonet to that chain's root is
an EXECUTOR comparison. The flag day that would make it in-circuit is named in §"WHAT THIS BREAKS".
Nothing here says a body hash is a real Mina block body either; that is
`PICKLES_OPENING_WITNESSED` (⚑ renamed and narrowed 2026-08-06), still a witness.
⚠ Three further limits, none of them repealed: the seam's off-row half is the FRI/recursion
obligation this whole stack carries; the limb re-encoding between this descriptor's `Faithful9`
lanes and the absorb descriptor's 32 eight-bit limbs is an EXECUTOR check, not a constraint; and
fork choice is still not here (`LightClientMinaGate`'s unchanged scope note).
-/
import Dregg2.Circuit.Emit.LightClientMinaAir
import Dregg2.Circuit.Emit.EffectLowerCertified
import Dregg2.Circuit.GateExpr
import Dregg2.Bridge.MinaStateHashDerive

set_option autoImplicit false
set_option maxHeartbeats 1600000
-- ⚑ 2026-08-10: a ported `bound` carries two STRING names, and `String` reduces as a `List Char`,
-- so every `rfl` over a descriptor carrying one costs the welder path's length in whnf steps.
set_option maxRecDepth 16000

namespace Dregg2.Circuit.Emit.LightClientMinaLinkAir

open Dregg2.Circuit (Assignment Expr Constraint)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow VmRowEnv)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.EffectAirIR (EffectAir AirLeg LookupLeg PiPinLeg LimbsLeg WindowLeg)
open Dregg2.Circuit.TableAirIR (RowSel)
open Dregg2.Circuit.LimbTally (limbValue LimbsInRange)
open Dregg2.Circuit.Emit.PastaField (pN)
open Dregg2.Circuit.Emit.LightClientMinaAir
  (MINA_LANE_BITS MINA_TOP_LANE_BITS minaRangeTid minaLaneTable minaTopLaneTable STATE_LIMBS
   laneCanon stateValue mina_lane_canon_forces_canonical laneCanon_value_bounds)
open Dregg2.Bridge.LightClientMina

/-! ## §1 — the column layout (ONE ROW PER EXHIBITED BLOCK) and the PI slots. -/

/-- **`PARENT j`** — lane `j` of this block's `previousStateHash`. Columns 0..8. -/
def PARENT (j : Nat) : Nat := j

/-- **`OWNHASH j`** — lane `j` of this block's OWN protocol-state hash. Columns 9..17.
⚑ **DERIVED since 2026-08-06.** The state-hash seam (§2b) makes this nonet the IMAGE of the row:
`Poseidon_{MinaProtoState}(PARENT, BODYHASH)`, bound to a verifying sub-proof of
`dregg-pasta-fp-absorb::v1`. It was a free witness until then and `LinkHashResidual` was the name of
that hole; the `Prop` survives as a CONCLUSION (`linkHashResidual_of_seam`). -/
def OWNHASH (j : Nat) : Nat := STATE_LIMBS + j

/-- **`HEIGHT`** — this block's `blockchainLength`. -/
def HEIGHT : Nat := 2 * STATE_LIMBS

/-- **`IS_REAL`** — 1 on an exhibited block, 0 on padding. Boolean-pinned on EVERY row and monotone
across transitions, so the real rows are a PREFIX. -/
def IS_REAL : Nat := 2 * STATE_LIMBS + 1

/-- **`REAL_COUNT`** — the cumulative count of real rows. ⚑ Its LAST-row value is `PI_SEG_LEN`, which
is what stops the segment length being a free felt. -/
def REAL_COUNT : Nat := 2 * STATE_LIMBS + 2

/-- **`ANCHOR_H`** — the pinned anchor's blockchain length. Read on the FIRST row only (the
first-row height gate and the first-row PI pin); unconstrained elsewhere, deliberately. -/
def ANCHOR_H : Nat := 2 * STATE_LIMBS + 3

/-- ⚑ **`BODYHASH j`** — lane `j` of this block's `state_body_hash`. Columns 22..30. ⚑ **THE
PREIMAGE THE ROW DID NOT HAVE.** `OWNHASH` could not be the image of its row while the row carried
no preimage: Mina's identity is
`state_hash = Poseidon_Fp(salt "MinaProtoState")[previous_state_hash ; state_body_hash]`
(`Bridge/MinaStateHashDerive.lean:31`, `:392`), and the second argument was in no column. It is one
now.

⚑ **AND SINCE 2026-08-07 IT IS DERIVED — OFF THIS DESCRIPTOR, AND SAY WHICH.**
`Circuit/Emit/MinaStateBodyHashChain` computes it as a **25-link chain** of the deployed
`dregg-pasta-fp-chainlink::v1`, from the pinned `MinaProtoStateBody` salt over the block's own packed
`Body.to_input` preimage. ⚠ **The tie to THIS column is EXECUTOR-side, not a constraint**: nothing
below relates `BODYHASH` to that chain's root, because a `proofBind` can only name PUBLIC INPUTS and
these nine columns are not published. That is the flag day this rung leaves and §"WHAT THIS BREAKS"
names it. What makes it a real block BODY — as opposed to a preimage somebody chose — is
`PICKLES_OPENING_WITNESSED` (⚑ `PICKLES_WITNESSED` until 2026-08-06, `PICKLES_OK` until 08-05), and
that is unchanged. -/
def BODYHASH (j : Nat) : Nat := 2 * STATE_LIMBS + 4 + j

/-- ⚑ **`HASH_VK i`** — lane `i` of the attested state-hash program's fingerprint. Columns 31..39,
range-gated and forced by the seam's `vkPin` to the nine `Faithful9` lanes of
`dregg-pasta-fp-absorb::v1`. The same shape `LightClientMinaAir.LINK_VK` carries one rung up. -/
def HASH_VK (i : Nat) : Nat := 3 * STATE_LIMBS + 4 + i

/-- ⚑ **`BODY_ACC i`** — lane `i` of the body-hash chain's ORDERED TRANSCRIPT ACCUMULATOR, the
8-lane `seg_poseidon_commit` fold `MinaStateBodyHashChain`'s 25-leaf recursion publishes as its root
claim's `transcript_acc`. Columns 40..47, published at PI 29..36.

⚑⚑ **THIS IS THE COLUMN THAT KEEPS THE BODY-CHAIN SEAM FROM BEING VACUOUS**, and it was named
before it was built: *"A BIND OF `(salt, BODYHASH)` ALONE WOULD BE VACUOUS … `perm` is a
permutation, so 25 links from a fixed head with free absorbed inputs reach every field element.
Naming the stream is the whole content."* The accumulator IS the stream, ordered — so the seam's
commitment is `salt ‖ BODYHASH ‖ acc(absorbed)` and not `(salt, BODYHASH)`.

⚠ **NOT RANGE-GATED, and that is not an omission.** These are BabyBear Poseidon2 digest lanes, i.e.
arbitrary field elements; a 29-bit lookup would REFUSE an honest accumulator. They are joined by the
seam's `proof_bind`, which is what `pinsTied`/`decorativeAnchors` ask of a published column. -/
def BODY_ACC (i : Nat) : Nat := 4 * STATE_LIMBS + 4 + i

/-- ⚑ **`CHAIN_VK i`** — lane `i` of the body-hash chain program's fingerprint. Columns 48..56,
range-gated at 29 bits and forced by the body-chain seam's `vkPin` to the nine `Faithful9` lanes of
`dregg-pasta-fp-chainlink::v1`. Same shape, same gadget, same coupling as `HASH_VK`. -/
def CHAIN_VK (i : Nat) : Nat := 4 * STATE_LIMBS + 12 + i

/-- Main-trace width: three nine-lane hashes (parent, own, body) + height + the two real-row
columns + the anchor height + the nine attested-program lanes + the body chain's 8-lane accumulator
+ its nine program lanes. -/
def MINA_LINK_WIDTH : Nat := 4 * STATE_LIMBS + 21

/-- PI slot of anchor-state lane `j` (slots 0..8). -/
def PI_ANCHOR (j : Nat) : Nat := j
/-- PI slot of tip-state lane `j` (slots 9..17). -/
def PI_TIP (j : Nat) : Nat := STATE_LIMBS + j
/-- PI slot 18: the pinned anchor's height. -/
def PI_ANCHOR_H : Nat := 2 * STATE_LIMBS
/-- ⚑ PI slot 19: the number of EXHIBITED blocks, as counted by the trace. -/
def PI_SEG_LEN : Nat := 2 * STATE_LIMBS + 1
/-- ⚑ PI slots 20..28: the block's `state_body_hash`, PUBLISHED. -/
def PI_BODYHASH (j : Nat) : Nat := 2 * STATE_LIMBS + 2 + j
/-- ⚑ PI slots 29..36: the body-hash chain's ordered transcript accumulator, PUBLISHED. -/
def PI_BODY_ACC (i : Nat) : Nat := 3 * STATE_LIMBS + 2 + i
/-- ⚑⚑⚑ PI slots 37..45: the FIRST row's OWN state hash, PUBLISHED — **2026-08-10**.

**WHY THIS BLOCK EXISTS, and it is the whole content of the `state-hash-preimage` port's cover.**

`stateHashBindLeg` commits `salt ‖ PARENT ‖ BODYHASH ‖ OWNHASH` on EVERY row against
`dregg-pasta-fp-absorb::v1`. On ROW 0 three of those four blocks were already grounded outside the
prover's choice:

* `salt` — 27 descriptor CONSTANTS;
* `PARENT` — `firstOldRootBind` pins those columns to `PI_ANCHOR`, and the consumer refuses
  `PI_ANCHOR` against the cell-program-pinned weak-subjectivity anchor
  (`mina_head_verifier::check_segment_binding`, refusal 14);
* `BODYHASH` — pinned to `PI_BODYHASH` and welded to the 25-leaf body-hash chain root
  (`check_body_chain_binding`, refusal 16d).

**`OWNHASH` was the ONE unpublished block of the row-0 commit vector — 9 lanes of 54.** A
`proofBind`'s commitment may only name PUBLISHED values for a fold to reach, and a consumer can
only compare what a proof publishes, so with row 0's `OWNHASH` unpublished there was NO object
anywhere — AIR, seam or host — that could relate it to anything. That is why the port's cover did
not exist rather than merely being unwritten.

⚑ And publishing the FIRST row's is what makes the comparison bite. `PI_TIP` is the LAST row's
`OWNHASH`, and a cover against it would be ∃-image vacuity: the absorbed pair at that row is
unpublished, so a prover picks any pair, computes its image, and publishes THAT as the tip. At row
0 both absorbed elements are grounded, so `OWNHASH₀` is a DETERMINED value and the comparison has
no freedom left to satisfy.

⚠ **WHAT IT DOES NOT BUY.** Rows `1 …` keep `LinkHashResidual`: their `OWNHASH` is still a free
witness. What this closes is the FIRST link — and by `laneContinuity`, `OWNHASH₀ = PARENT₁`, so the
chain's second element is derived from the pinned anchor. Closing the rest needs one absorb
instance per row and a per-row accumulator this AIR does not compute; that is the next rung and it
is UNDONE WORK, not a theorem of the model. -/
def PI_HEAD_OWN (j : Nat) : Nat := 3 * STATE_LIMBS + 10 + j
/-- Number of public inputs. ⚑ **20 → 37 on 2026-08-08**, the flag day §"WHAT THIS BREAKS" costed;
⚑⚑ **37 → 46 on 2026-08-10**, the `state-hash-preimage` cover's publication (see
[`PI_HEAD_OWN`]). -/
def MINA_LINK_PI_COUNT : Nat := 3 * STATE_LIMBS + 19

/-- The eight LOW lane columns of the block's parent hash. -/
def parentLowLanes : List Nat :=
  [PARENT 0, PARENT 1, PARENT 2, PARENT 3, PARENT 4, PARENT 5, PARENT 6, PARENT 7]

/-- The eight LOW lane columns of the block's own state hash. -/
def ownHashLowLanes : List Nat :=
  [OWNHASH 0, OWNHASH 1, OWNHASH 2, OWNHASH 3, OWNHASH 4, OWNHASH 5, OWNHASH 6, OWNHASH 7]

/-- The `Fp` element a row's PARENT nonet denotes. -/
def parentValue (a : Assignment) : ℤ := stateValue a parentLowLanes (PARENT 8)

/-- The `Fp` element a row's OWNHASH nonet denotes. -/
def ownHashValue (a : Assignment) : ℤ := stateValue a ownHashLowLanes (OWNHASH 8)

/-- The eight LOW lane columns of the block's body hash. -/
def bodyHashLowLanes : List Nat :=
  [BODYHASH 0, BODYHASH 1, BODYHASH 2, BODYHASH 3, BODYHASH 4, BODYHASH 5, BODYHASH 6, BODYHASH 7]

/-- The `Fp` element a row's BODYHASH nonet denotes. -/
def bodyHashValue (a : Assignment) : ℤ := stateValue a bodyHashLowLanes (BODYHASH 8)

/-- The nine `HASH_VK` columns, as a limb vector. -/
def hashVkLanes : List Nat :=
  [HASH_VK 0, HASH_VK 1, HASH_VK 2, HASH_VK 3, HASH_VK 4, HASH_VK 5, HASH_VK 6, HASH_VK 7,
   HASH_VK 8]

/-- The nine `CHAIN_VK` columns, as a limb vector. -/
def chainVkLanes : List Nat :=
  [CHAIN_VK 0, CHAIN_VK 1, CHAIN_VK 2, CHAIN_VK 3, CHAIN_VK 4, CHAIN_VK 5, CHAIN_VK 6, CHAIN_VK 7,
   CHAIN_VK 8]

/-! ## §2 — the SOURCE legs, in the framework's own algebra.

⚑ Every inter-row law is a `WindowLeg` at `.transition` — the ONE `RowSel` where `nxt` is the genuine
successor rather than the wrap row (`EffectAirIR.WindowLeg.mainRailOk`). The two first-row fixes are
`.first` and read only `loc`; the boolean pin is `.all`. Nothing below is a `VmConstraint2`. -/

open WindowExpr (loc nxt)

/-- **Lane continuity** — `OWNHASH[i] = PARENT[i+1]`, one leg per lane. This is
`EffectVmEmitTurnChainBinding.rootContinuity` at nine lanes instead of one felt. -/
def laneContinuity (j : Nat) : AirLeg :=
  .window ⟨RowSel.transition,
    .add (loc (OWNHASH j)) (.mul (.const (-1)) (nxt (PARENT j)))⟩

/-- **Height contiguity** — `HEIGHT[i+1] = HEIGHT[i] + 1` (`idxIncrement`). -/
def heightIncrement : AirLeg :=
  .window ⟨RowSel.transition,
    .add (nxt HEIGHT) (.add (.mul (.const (-1)) (loc HEIGHT)) (.const (-1)))⟩

/-- **The first block sits one above the pinned anchor** — `HEIGHT[0] = ANCHOR_H + 1`
(`firstIdxZero`'s analog; row-local, so `.first` is expressible). -/
def firstHeight : AirLeg :=
  .window ⟨RowSel.first,
    .add (loc HEIGHT) (.add (.mul (.const (-1)) (loc ANCHOR_H)) (.const (-1)))⟩

/-- **`IS_REAL` is boolean on EVERY row.** ⚑ `.all`, not `.transition`: a transition-scoped boolean
pin is vacuous on the last row, which is where a padding row would hide. -/
def isRealBoolean : AirLeg :=
  .window ⟨RowSel.all, Dregg2.Circuit.GateExpr.render Dregg2.Circuit.GateExpr.toWindow
    (Dregg2.Circuit.GateExpr.gBool (.leaf (.loc IS_REAL)))⟩

theorem isRealBoolean_eq :
    isRealBoolean = .window ⟨RowSel.all, .mul (loc IS_REAL) (.add (loc IS_REAL) (.const (-1)))⟩ :=
  rfl

/-- **Real rows are a PREFIX** — forbid a `0 → 1` transition (`realMonotone`). -/
def realMonotone : AirLeg :=
  .window ⟨RowSel.transition,
    .mul (nxt IS_REAL) (.add (.const 1) (.mul (.const (-1)) (loc IS_REAL)))⟩

/-- **Seed the counter** — `REAL_COUNT[0] = IS_REAL[0]` (`firstRealCount`). -/
def firstRealCount : AirLeg :=
  .window ⟨RowSel.first, .add (loc REAL_COUNT) (.mul (.const (-1)) (loc IS_REAL))⟩

/-- **Accumulate** — `REAL_COUNT[i+1] = REAL_COUNT[i] + IS_REAL[i+1]` (`realCountAccum`). -/
def realCountAccum : AirLeg :=
  .window ⟨RowSel.transition,
    .add (nxt REAL_COUNT)
      (.add (.mul (.const (-1)) (loc REAL_COUNT)) (.mul (.const (-1)) (nxt IS_REAL)))⟩

/-- The eight low lanes of a nonet, as ONE `.limbs` leg at 29 bits — the same gadget the sibling
rung uses, not a second copy. -/
def lowLanesLeg (cols : List Nat) : AirLeg :=
  .limbs { cols := cols, bits := MINA_LANE_BITS, table := minaRangeTid MINA_LANE_BITS }

/-- The top lane, on the NARROW 22-bit table — the leg that separates "well-formed 32-byte nonet"
from "canonical Pasta field element". -/
def topLaneLeg (col : Nat) : AirLeg :=
  .lookup { table := minaRangeTid MINA_TOP_LANE_BITS, tuple := [Expr.var col] }

/-- The nine FIRST-row anchor pins (`firstOldRootBind` at nine lanes). -/
def anchorPins : List AirLeg :=
  [ .pin ⟨VmRow.first, PARENT 0, PI_ANCHOR 0⟩
  , .pin ⟨VmRow.first, PARENT 1, PI_ANCHOR 1⟩
  , .pin ⟨VmRow.first, PARENT 2, PI_ANCHOR 2⟩
  , .pin ⟨VmRow.first, PARENT 3, PI_ANCHOR 3⟩
  , .pin ⟨VmRow.first, PARENT 4, PI_ANCHOR 4⟩
  , .pin ⟨VmRow.first, PARENT 5, PI_ANCHOR 5⟩
  , .pin ⟨VmRow.first, PARENT 6, PI_ANCHOR 6⟩
  , .pin ⟨VmRow.first, PARENT 7, PI_ANCHOR 7⟩
  , .pin ⟨VmRow.first, PARENT 8, PI_ANCHOR 8⟩ ]

/-- The nine LAST-row tip pins (`lastNewRootBind` at nine lanes). -/
def tipPins : List AirLeg :=
  [ .pin ⟨VmRow.last, OWNHASH 0, PI_TIP 0⟩
  , .pin ⟨VmRow.last, OWNHASH 1, PI_TIP 1⟩
  , .pin ⟨VmRow.last, OWNHASH 2, PI_TIP 2⟩
  , .pin ⟨VmRow.last, OWNHASH 3, PI_TIP 3⟩
  , .pin ⟨VmRow.last, OWNHASH 4, PI_TIP 4⟩
  , .pin ⟨VmRow.last, OWNHASH 5, PI_TIP 5⟩
  , .pin ⟨VmRow.last, OWNHASH 6, PI_TIP 6⟩
  , .pin ⟨VmRow.last, OWNHASH 7, PI_TIP 7⟩
  , .pin ⟨VmRow.last, OWNHASH 8, PI_TIP 8⟩ ]

/-! ## §2b — ⚑⚑⚑ THE STATE-HASH SEAM: `OWNHASH` STOPS BEING A FREE WITNESS.

## What was here this morning, and why the price was wrong by 26×

The file's own header called Mina's linkage hash a WALL and priced it: *"~500 Pasta multiplications
per permutation, ≈5·10⁵ BabyBear constraints per block hash, ~1.5·10⁸ for a Samasika-depth
segment."* Both halves of that estimate were re-derived here and both moved.

⚑ **THE PERMUTATION COUNT: 1 PER BLOCK, NOT 26.** `Bridge/MinaStateHashDerive.lean:31` reads the
daemon (`protocol_state.ml:45-55`) and says what a Mina block's identity IS:

    state_hash = Poseidon_Fp( salt "MinaProtoState" )[ previous_state_hash ; state_body_hash ]

**Two field elements at rate 2 is ONE block and ONE permutation.** The salt is
`Random_oracle.update ~state:[0,0,0] [|prefix_to_field s|]` — a CONSTANT, permuted at emit time, not
in circuit. The `~26 permutations/block` the standing estimate carried is the *transcript* chain's
link count (phase-1 is 27 links, phase-2 is 46); it is not the state hash. The deep hash is
`state_body_hash`, over ~38 field elements — and that one is **not part of the linkage**: it enters
here as a witnessed nonet and what attests it is `PICKLES_OK`, exactly as before.

⚑ **AND THE CIRCUIT DOES NOT NEED BUILDING — IT IS EMITTED AND IT PROVES.**
`dregg-pasta-fp-absorb::v1` (`MinaWrapVerifierSpongeFp.fpAbsorbDesc`) is a 2 048-row, 469-column,
858-constraint instance of the Pasta program VM whose 660 ROM immediates are `fp_kimchi`'s own
`static_params()`, checked on the emitted bytes (`circuit/tests/pasta_fp_sponge_proves.rs` §9). It
computes `perm(state + [x₀, x₁, 0])` and — the fact that makes it usable here —
`the_absorb_program_permutes_gen` has **no hypothesis on the incoming state**, which is not a
descriptor constant but PUBLIC INPUT slots `[0, 3·SK)`. So a *salted* sponge is the SAME descriptor
with different public inputs; `MinaPhase1Chain` already threads 27 links of non-zero state through
it. Nothing new is authored, and in particular **no non-native Pasta multiply is authored here**
(`minaLink_products_are_only_the_real_bit` still holds, §3b).

Re-derived segment cost, at the measured leaf/fold times of that same descriptor family (9.5 s a
leaf, 11.5 s a fold node, `mina_phase2_chain_fold`): a Samasika-depth `k = 290` segment is 290
leaves + 289 fold nodes ≈ **1 h 41 min**, against the inherited **44 h**. ⚠ That is an
extrapolation from a same-shaped descriptor's measured times, not a fresh wall-clock measurement of
290 leaves, and it is labelled as one.

## The leg, and why the commitment has FOUR nonets in it

`ProofBind`'s `commit` is the only vector naming off-row evidence, so the only way a `proofBind` can
join a column is for that column to BE part of the commitment. The sentence that has to be true is
`OWNHASH = Poseidon_{salt}(PARENT, BODYHASH)`, and it names SIX `Fp` elements — the salt's three
sponge lanes and the row's three nonets. All six are in the commit vector, elementwise, nine
`Faithful9` lanes each — **54 lanes, `8·29 + 22 = 254` bits an element, no digest, therefore no
birthday bound.**

⚑ **THE SALT LANES ARE `.const`, AND THEY ARE THE LOAD-BEARING PART.** With a free incoming state
the seam would be VACUOUS and not weakly so: `perm` is a permutation, so for any target `out` a
prover picks `state := perm⁻¹(T) − [x₀,x₁,0]` for any `T` with `T[0] = out` and the sub-proof is
honest. Pinning the three state lanes as descriptor CONSTANTS is what makes the bound sub-proof a
*Mina* state hash rather than a generic two-input Poseidon.

⚑ **THE GUARD IS `1`, NOT `IS_REAL`, AND THAT CLOSES A HOLE THIS FILE DID NOT KNOW IT HAD.**
`Satisfied2Custom.proofBound` quantifies over EVERY row, so a guard column would let a prover switch
the seam off — and the natural choice, `IS_REAL`, switches it off exactly where the tip lives: the
`.last` tip pin reads the LAST row whether or not that row is real, `laneContinuity` is
unconditional, so `[real, real, real, pad]` chains into a padding row whose `OWNHASH` is free and
IS `PI_TIP`. An unconditional guard makes every row of the trace a state-hash step and the tip the
image of the chain regardless of `IS_REAL`. -/

/-- ⚑ **THE `MinaProtoState` SALT, AS 27 `Faithful9` LANES.** The three-lane sponge state
`Random_oracle.salt "MinaProtoState"` — `Bridge/MinaStateHashDerive.saltProtoState`, itself pinned
to openmina's OWN regression constants (`poseidon/tests/test_hash_params.rs:28-51`), which is what
exercises the 20-byte `'*'` padding, the little-endian prefix read, the Kimchi constants and the
absorb schedule in one line. Decomposed here base `2^29`, low lane first, nine lanes per element.

⚠ These are the `commit` vector's CONSTANT head. A wrong lane here does not fail loudly — it names
a different salt, i.e. a different chain's hash function — so `mina_link_salt_lanes_are_the_salt`
recomposes all three and compares against `saltProtoState` itself rather than against a comment. -/
def MINA_PROTO_STATE_SALT_LANES : List ℤ :=
  [ 116766262, 149354484, 292986828, 413194933, 280149768, 225329418, 86819885, 115568088, 756181
  , 484328300, 122810986, 211984088, 66952329, 462241909, 111193962, 66311195, 117199812, 1110329
  , 340957929, 274801759, 113970126, 217898572, 2899587, 228371615, 197690145, 523247988, 2877414 ]

/-- ⚑ **THE STATE-HASH PROGRAM'S IDENTITY, AS NINE LANES.** The `Faithful9` key lanes of
`effect_vm_descriptor2_semantic_fingerprint(dregg-pasta-fp-absorb::v1)`. Lean cannot compute blake3,
so this literal is a TRANSCRIPTION, and a transcription is only a gate if something recomputes it:
`circuit/tests/mina_statehash_seam_proves.rs` recomputes it from that descriptor's own bytes.

⚠ **FLAG DAY COUPLING:** re-emitting `pasta-fp-absorb.json` moves this literal and therefore
re-emits and re-VKs `dregg-mina-lightclient-link::v1`, which in turn moves
`LightClientMinaAir.LINK_VK_LANES` and re-VKs the head. Three descriptors, one chain.

⚑⚑ **AND THAT COUPLING WAS BROKEN — THE PARAGRAPH ABOVE DESCRIBED A DISCIPLINE NOBODY RAN.**
`067f63780` re-emitted `pasta-fp-absorb.json` and this literal did not follow, so from that commit
until 2026-08-08 the state-hash seam named **a program no descriptor in this tree had** — the exact
wraplink defect `LightClientMinaAir.CHAINLINK_VK_LANES`'s own docblock records, repeated one rung
down. `circuit/tests/mina_statehash_seam_proves.rs::the_seam_pins_the_real_absorb_program` was RED
at HEAD on precisely this comparison and stayed red; the gate worked and the repair did not follow
it.

⚠ The nine digits below are **RECOMPUTED FROM THE EMITTED BYTES**, never transcribed from a
docblock or copied to make a check agree:

    cargo run -p dregg-circuit --example conj_fingerprint -- \
      circuit/descriptors/by-name/pasta-fp-absorb.json
    → fp=d6ffe0dc44ed069d679b303924ee546ca521e43516dd7a62411ebf37735c9570
      lanes=[484507606, 137849382, 203872743, 165431410, 35280581, 243997426, 419793387,
             241629155, 7378268]

Second source, independently: `MinaWrapClosingAir.ABSORB_VK_LANES` carries the same nine, and
`circuit/tests/mina_wrap_closing_air_proves.rs::the_weld_pins_the_real_absorb_program_and_names_its_pi_vector`
recomputes them from the same bytes.

⚑ **RE-MEASURED 2026-08-11 AFTER THE CANONICAL-RECORD CHANGE.** `2ad7e48c8` changed the binary
record hashed for every descriptor even when its JSON did not move. The unchanged served
`pasta-fp-absorb.json` now fingerprints to
`5c0973624f0a1686966e8d1e0c16894279154bfb98c14edaf51d268c61e2fd18`, i.e. the nine lanes below.
That value was the bridge into the authorized emit. The emitted descriptor then materialised the
new round/state columns (`w=469→532`, `cons=858→953`, `pi=192` unchanged) and now fingerprints to
`0b55e61b97c113550b8a671a40ea22923dddd184cf22ae5cdfb036046a92b07a`. Both Lean consumers move in
this flag day; the all-pin resolver and the two Rust gates recompute the value rather than accepting
agreement between the copies. -/
def ABSORB_VK_LANES : List ℤ :=
  [468079883, 144575672, 434275029, 97812532, 500422946, 292012648, 58553016, 222332630, 8040594]

/-- The nine `Faithful9` lanes of a row's PARENT nonet, as commit expressions. -/
def parentCommitLanes : List Expr :=
  [ .var (PARENT 0), .var (PARENT 1), .var (PARENT 2), .var (PARENT 3), .var (PARENT 4)
  , .var (PARENT 5), .var (PARENT 6), .var (PARENT 7), .var (PARENT 8) ]

/-- The nine `Faithful9` lanes of a row's BODYHASH nonet, as commit expressions. -/
def bodyCommitLanes : List Expr :=
  [ .var (BODYHASH 0), .var (BODYHASH 1), .var (BODYHASH 2), .var (BODYHASH 3), .var (BODYHASH 4)
  , .var (BODYHASH 5), .var (BODYHASH 6), .var (BODYHASH 7), .var (BODYHASH 8) ]

/-- The nine `Faithful9` lanes of a row's OWNHASH nonet, as commit expressions. -/
def ownCommitLanes : List Expr :=
  [ .var (OWNHASH 0), .var (OWNHASH 1), .var (OWNHASH 2), .var (OWNHASH 3), .var (OWNHASH 4)
  , .var (OWNHASH 5), .var (OWNHASH 6), .var (OWNHASH 7), .var (OWNHASH 8) ]

/-- The nine attested-program columns, as vk expressions. -/
def hashVkCommitLanes : List Expr :=
  [ .var (HASH_VK 0), .var (HASH_VK 1), .var (HASH_VK 2), .var (HASH_VK 3), .var (HASH_VK 4)
  , .var (HASH_VK 5), .var (HASH_VK 6), .var (HASH_VK 7), .var (HASH_VK 8) ]

/-- ⚑⚑ **THE STATE-HASH BIND LEG.** Guard `1` — unconditional, every row. Commitment: the pinned
salt as constants, then the row's parent, its body hash and its own hash, nine lanes each. Attested
program: the nine `HASH_VK` columns, pinned to `dregg-pasta-fp-absorb::v1`'s fingerprint.

⚑ `bound := none` and it is the right choice for the same reason the head's segment seam gives:
`bound` forces `commit` to equal a row-local expression, and every `commit` lane here is already
either a descriptor CONSTANT or a `.var` on this row. A `bound` congruence could only compare each
to itself. -/
def seamCommitLanes : List Expr :=
  MINA_PROTO_STATE_SALT_LANES.map Expr.const
    ++ parentCommitLanes ++ bodyCommitLanes ++ ownCommitLanes

def stateHashBindLeg : AirLeg :=
  .bind { guard  := .const 1
        , commit := seamCommitLanes
        , vk     := hashVkCommitLanes
        , vkPin  := some ABSORB_VK_LANES
        -- ⚑⚑ 2026-08-10: this half is the link's `state-hash-preimage` PORT, and it names the
        -- welder it REQUIRES — which DOES NOT EXIST YET. `bodyHashWeld` covers the `BODYHASH`
        -- nonet (REFUSAL 16d); nothing anywhere compares `PARENT` or `OWNHASH`, and the executor's
        -- own docblock says `OWNHASH` is a free witness. Under the retired `bound := none` that
        -- fact was a paragraph; it is now a NAME the registry gate resolves and FAILS to resolve,
        -- counted by `scripts/check-proof-bind-port-covers.py`'s pinned literal. Writing the owed
        -- welder is what shrinks it.
        , bound  := .port ⟨"state-hash-preimage", "dregg_turn::executor::mina_head_verifier::check_state_hash_preimage_binding"⟩ }

/-! ### §2c — ⚑⚑⚑ THE BODY-CHAIN SEAM: `BODYHASH` STOPS BEING AN UNBOUND ARGUMENT.

**2026-08-08.** `MinaStateBodyHashChain` derived `state_body_hash` on 08-07 and folded it, and
`LightClientAnchorConnectivity.minaLink_body_hash_is_joined_but_not_published` named the exact reason
nothing here could reach it:

> *"`isPiBound = false` is now the SPECIFIC gap … a `proofBind`'s `commit`/`vk` name PUBLISHED values
> and a recursion fold reads `air_public_targets`, so **an unpublished `BODYHASH` cannot be
> `cb.connect`ed to the body-hash chain's root at all**."*

So the nonet is published (PI 20..28) and the chain's ordered accumulator with it (PI 29..36), and
this leg names both.

⚑⚑ **AND THE ACCUMULATOR IS NOT OPTIONAL — the vacuity was named before anything could be built.**
`(salt, BODYHASH)` alone commits to a hash from a pinned head over a FREE stream, and `perm` is a
permutation: 25 links from a fixed head reach every field element, so such a bind refuses nothing.
The commitment here is `salt ‖ BODYHASH ‖ acc`, where `acc` is the 8-lane ordered digest of the 49
absorbed packed elements the chain's fold publishes as `transcript_acc`. **Naming the stream is the
whole content**, and it is what makes this a claim about a *body* rather than about a permutation.

⚠ **WHAT IS STILL OWED AFTER THIS, said plainly.** Publishing buys the weld's REACHABILITY, not the
weld. Until a fold `cb.connect`s these 17 PI slots to the chain root's claim lanes, the tie is an
EXECUTOR comparison — and the accumulator's own tie to *this* block's preimage stays a comparison
against `packToFields (bodyI decoded)`, a hash the node computes from bytes it already holds. -/

/-- ⚑ **THE `MinaProtoStateBody` SALT, AS 27 `Faithful9` LANES.** `Bridge.MinaStateHashDerive.
saltProtoStateBody`, itself pinned to openmina's OWN regression constants
(`poseidon/tests/test_hash_params.rs:28-51`). Decomposed base `2^29`, low lane first.

⚠ A LITERAL and not the computed expression, for a measured reason: `saltProtoStateBody` is a Kimchi
Poseidon permutation and reducing one under the kernel costs 47.6 GB / 68 min in this tree, so a
`rfl` shape pin over a computed salt would not elaborate. `mina_link_body_salt_lanes_are_the_body_
salt` recomposes all three elements and compares against `saltProtoStateBody` itself.

⚠ **AND IT IS THE OTHER SALT.** `MINA_PROTO_STATE_SALT_LANES` is `"MinaProtoState"`; this is
`"MinaProtoStateBody"`. Mina's whole domain separation between a state hash and a body hash rests on
the two being different, and a copy-paste here would name a different hash function with every gate
green — `the_two_seams_name_two_different_salts` is that as a theorem. -/
def MINA_PROTO_STATE_BODY_SALT_LANES : List ℤ :=
  [ 445790955, 89416348, 113760843, 414947883, 48810538, 69263919, 383158676, 95079572, 514152
  , 346036615, 382017676, 419187451, 491103726, 217437079, 153525551, 207452011, 442303419, 19441
  , 402493039, 345947338, 315114507, 422856893, 136538847, 195968706, 319895372, 227253601, 2739951 ]

/-- ⚑ **THE BODY-HASH CHAIN PROGRAM'S IDENTITY, AS NINE LANES.** The `Faithful9` key lanes of
`effect_vm_descriptor2_semantic_fingerprint(dregg-pasta-fp-chainlink::v1)` — the descriptor
`MinaStateBodyHashChain.bodyChainDesc` IS, by `rfl`.

⚠ **FLAG DAY COUPLING:** re-emitting `pasta-fp-chainlink.json` moves this literal and therefore
re-emits and re-VKs `dregg-mina-lightclient-link::v1`, which moves
`LightClientMinaAir.LINK_VK_LANES` and re-VKs the head.

⚑ **RE-MEASURED 2026-08-10 AFTER THE CANONICAL-RECORD CHANGE.** `2ad7e48c8` made `bound`
non-nullable in the binary fingerprint record, so every descriptor fingerprint moved even when its
JSON bytes did not. The unchanged served `pasta-fp-chainlink.json` now fingerprints to
`489dd5b7d14ba474912780b5c03af4f4d1076207fed8a46be8a4b4d5ebd10692`, i.e. the nine lanes below.
That value was the bridge into the authorized emit. The emitted descriptor then materialised the
new round/state columns (`w=469→532`, `cons=922→1017`, `pi=256` unchanged) and now fingerprints to
`9d2e069018f1036867a534484802cb743ba172e157b80684e88529c68542163f`.
`scripts/check-vk-pin-literals.sh` recomputes the whole term/bytes/BLAKE3/lane chain in pure Lean;
the seam registry reads this same definition rather than carrying a second measured literal. -/
def FP_CHAINLINK_VK_LANES : List ℤ :=
  [268840605, 2066628, 220813786, 369397904, 169064268, 472641721, 396496922, 280544560, 4134466]

/-- The eight `BODY_ACC` columns, as commit expressions. -/
def bodyAccCommitLanes : List Expr :=
  [ .var (BODY_ACC 0), .var (BODY_ACC 1), .var (BODY_ACC 2), .var (BODY_ACC 3)
  , .var (BODY_ACC 4), .var (BODY_ACC 5), .var (BODY_ACC 6), .var (BODY_ACC 7) ]

/-- The nine `CHAIN_VK` columns, as vk expressions. -/
def chainVkCommitLanes : List Expr :=
  [ .var (CHAIN_VK 0), .var (CHAIN_VK 1), .var (CHAIN_VK 2), .var (CHAIN_VK 3), .var (CHAIN_VK 4)
  , .var (CHAIN_VK 5), .var (CHAIN_VK 6), .var (CHAIN_VK 7), .var (CHAIN_VK 8) ]

/-- The body-chain seam's commitment: the pinned `MinaProtoStateBody` salt as constants, then this
row's body hash, then the chain's ordered absorbed-stream accumulator. 44 lanes. -/
def bodyChainCommitLanes : List Expr :=
  MINA_PROTO_STATE_BODY_SALT_LANES.map Expr.const ++ bodyCommitLanes ++ bodyAccCommitLanes

/-- ⚑⚑⚑ **THE BODY-CHAIN BIND LEG.** Guard `1` — unconditional, every row, for the same reason
§2b gives: `Satisfied2Custom.proofBound` quantifies over EVERY row, so a guard column would let a
prover switch the seam off exactly where the tip lives. -/
def bodyChainBindLeg : AirLeg :=
  .bind { guard  := .const 1
        , commit := bodyChainCommitLanes
        , vk     := chainVkCommitLanes
        , vkPin  := some FP_CHAINLINK_VK_LANES
        -- ⚑ 2026-08-10: the commit half is the link's `body-hash` PORT, covered by REFUSAL 16
        -- (`bodyHashWeld` / `bodyAccWeld`, `check_body_chain_binding`).
        , bound  := .port ⟨"body-hash", "dregg_turn::executor::mina_head_verifier::check_body_chain_binding"⟩ }

/-- ⚑ The nine `BODYHASH` PI pins (cols 22..30 → PI 20..28) — the publication that makes the weld
reachable at all. -/
def bodyHashPins : List AirLeg :=
  (List.range STATE_LIMBS).map fun j => .pin ⟨VmRow.first, BODYHASH j, PI_BODYHASH j⟩

/-- ⚑ The eight `BODY_ACC` PI pins (cols 40..47 → PI 29..36). -/
def bodyAccPins : List AirLeg :=
  (List.range 8).map fun i => .pin ⟨VmRow.first, BODY_ACC i, PI_BODY_ACC i⟩

/-- ⚑⚑⚑ The nine FIRST-ROW `OWNHASH` PI pins (cols 9..17 → PI 37..45) — the 2026-08-10 publication
that gives the `state-hash-preimage` port an output to land on. See [`PI_HEAD_OWN`].

⚠ `.first`, and the row selector is the whole point: `tipPins` pins the SAME columns on `.last`.
The two coincide only on a one-row segment, and a cover written against the `.last` block would be
∃-image vacuous — the reason is spelled out at [`PI_HEAD_OWN`]. -/
def headOwnPins : List AirLeg :=
  (List.range STATE_LIMBS).map fun j => .pin ⟨VmRow.first, OWNHASH j, PI_HEAD_OWN j⟩

/-! ## §3 — ⚑ THE SOURCE AIR, and the descriptor as the COMPILER'S OUTPUT. -/

/-- ⚑ **THE SOURCE.** Forty-three legs: fifteen windows (nine lane-continuity + six
counting/height), THREE `.limbs` + three narrow lookups for per-row canonicality of the parent, the
own hash and the BODY hash, one `.limbs` for the nine attested-program lanes, ⚑ ONE `.bind` — the
state-hash seam — and twenty PI pins. -/
def minaLinkAir : EffectAir :=
  { tables := [minaLaneTable, minaTopLaneTable]
  , legs   :=
      [ laneContinuity 0, laneContinuity 1, laneContinuity 2, laneContinuity 3
      , laneContinuity 4, laneContinuity 5, laneContinuity 6, laneContinuity 7
      , laneContinuity 8
      , heightIncrement
      , firstHeight
      , isRealBoolean
      , realMonotone
      , firstRealCount
      , realCountAccum
      , lowLanesLeg parentLowLanes
      , topLaneLeg (PARENT 8)
      , lowLanesLeg ownHashLowLanes
      , topLaneLeg (OWNHASH 8)
      , lowLanesLeg bodyHashLowLanes
      , topLaneLeg (BODYHASH 8)
      , lowLanesLeg hashVkLanes
      , stateHashBindLeg
      , lowLanesLeg chainVkLanes
      , bodyChainBindLeg ]
      ++ anchorPins ++ tipPins
      ++ [ .pin ⟨VmRow.first, ANCHOR_H, PI_ANCHOR_H⟩
         , .pin ⟨VmRow.last, REAL_COUNT, PI_SEG_LEN⟩ ]
      ++ bodyHashPins ++ bodyAccPins ++ headOwnPins }

/-- ⚑ **THE VOCABULARY WAS ADEQUATE, AND THE MULTI-ROW HALF IS WHERE IT MATTERED.** Every leg is
main-rail expressible — decided on the emitted predicate, not by eye — so no leg lowered to
`EffectLower.refuseConstraints`. In particular the nine `.transition` lane-continuity legs and the
two `.first` row-local fixes are exactly the `RowSel` capability `EffectAirIR` gained, which is what
made a MULTI-ROW compiled descriptor possible at all. -/
theorem minaLinkAir_mainRailOk : minaLinkAir.mainRailOk = true := by rfl

/-- Every declared PI pin indexes a slot the descriptor declares. -/
theorem minaLinkAir_pinsFit : minaLinkAir.pinsFit MINA_LINK_PI_COUNT = true := by rfl

/-- Seventy-one legs: 9 lane windows + 6 counting/height windows + 5 `.limbs` + 3 top lookups +
2 `.bind` + 46 pins. ⚑ 43 → 62 on the 2026-08-08 publication flag day; ⚑⚑ 62 → 71 on the
2026-08-10 `PI_HEAD_OWN` publication. -/
theorem minaLinkAir_leg_count : minaLinkAir.legs.length = 71 := by rfl

/-- ⚑ **THE SEAM IS NOT THE DECLARATIVE SHAPE, AND IT IS NOT NARROW.** `BindLeg.mainRailOk` refuses
a bind that pins neither its program nor its commitment, and refuses either vector below
`PROOF_BIND_MIN_LANES`. This decides both on the leg rather than describing them: 54 commit lanes
(SIX `Fp` elements at nine `Faithful9` lanes each — the salt's three sponge lanes and the row's
parent, body hash and own hash) against 9 attested program lanes. ⚠ The two numbers DIFFER, which
is exactly what the retired `vk.length == commit.length` conjunct forbade. -/
theorem minaLink_seam_shape :
    (match stateHashBindLeg with | .bind b => b.mainRailOk | _ => false) = true
      ∧ (match stateHashBindLeg with | .bind b => b.commit.length | _ => 0) = 54
      ∧ (match stateHashBindLeg with | .bind b => b.vk.length | _ => 0) = 9 := by
  refine ⟨by rfl, ?_, by rfl⟩
  simp [stateHashBindLeg, seamCommitLanes, MINA_PROTO_STATE_SALT_LANES, parentCommitLanes,
    bodyCommitLanes, ownCommitLanes]

/-- ⚑ **THE INTER-ROW LAWS ARE COUNTED BY SELECTOR.** Twelve `.transition` legs (nine lane equalities +
the height tick + the monotone pin + the counter accumulation — the laws that need a genuine
successor), two `.first` row-local fixes, and one `.all` boolean pin. A leg that silently re-scoped from `.transition` to
`.all` (which accepts STRICTLY MORE, `TableAirIR.transition_strictly_weaker`) moves this. -/
theorem minaLinkAir_window_selectors :
    minaLinkAir.windowCountSel RowSel.transition = 12
      ∧ minaLinkAir.windowCountSel RowSel.first = 2
      ∧ minaLinkAir.windowCountSel RowSel.all = 1
      ∧ minaLinkAir.windowCountSel RowSel.last = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rfl

set_option maxRecDepth 8000 in
/-- FOUR limbed quantities per row — the parent's low half, the own hash's, the BODY hash's and the
nine attested-program lanes — and thirty-three per-lane range lookups. ⚑ The `HASH_VK` vector is
limbed at 29 bits for a reason that is load-bearing rather than tidy: an emitted `vkPin` congruence
is `≡ 0 [ZMOD P]`, so without a width gate a `HASH_VK` column could sit at `pin + P` and attest a
program nobody pinned. Same coupling, same gadget, as `link_lane_equality_is_exact`. -/
theorem minaLinkAir_limbs_shape :
    minaLinkAir.limbsCount = 5 ∧ minaLinkAir.totalRangeLookups = 42
      ∧ minaLinkAir.maxLimbedCapacityBits = 261 := by
  refine ⟨?_, ?_, ?_⟩ <;> rfl

/-! ### ⚑⚑ THE TIE VERDICT WENT RED HERE ON 2026-08-08, AND THE RED IS KEPT, NOT SOFTENED.

`minaLinkTiedAir` stood here — `minaLinkAir` carrying `mainRailOk` and `pinsTied` in its type —
and its `pinsTied` was TRUE only because `AirLeg.readCols` scored the §2c seam's DECLARED commit
lanes as reads while `bound := none` emits no polynomial over them. Emission-faithful
(`EffectLowerCertified` §1a, same day), the verdict says what is true: **the eight `BODY_ACC`
columns are published and read by NOTHING in this AIR — not even a width lookup** (a BabyBear
digest lane fills its column; a 29-bit table would refuse honest witnesses, so there is no honest
lookup to add). Their forcing is the EXECUTOR weld `check_body_chain_binding` (REFUSAL 16,
censused as `MinaSeams.bodyAccWeld`) — a HOST refusal, which is exactly what `pinsTied` exists to
distinguish from an AIR derivation. So the `TiedAir` is DEMOTED to `lowerAirCertified` (identical
bytes, `rfl`; the refinement certificate survives; only the tie verdict is no longer claimed) and
the red is stated as the two named theorems below. `PinsTiedCensus` carries the classification. -/

/-- ⚑ **THE RED, STATED.** Went false when `readCols` became emission-faithful; goes true again
only if the body columns gain a real in-AIR reader. -/
theorem minaLinkAir_pinsTied_is_false : minaLinkAir.pinsTied = false := by decide

/-- ⚑ …and the untied set is EXACTLY the eight `BODY_ACC` columns (40..47) — the wound has a
literal, not a mood. `BODYHASH` stays tied (its nine columns carry `.limbs`/lookup canonicality
legs); every other published column is derived by a window, gate, or limbs leg. (Stated over
COLUMN indices: `AirLeg` deliberately carries no `DecidableEq`, so a leg-list equality is not
decidable — same constraint `MinaSeams`' S1 memberships note.) -/
theorem the_untied_pins_are_exactly_the_body_acc :
    (minaLinkAir.legs.filterMap fun l =>
      match l with
      | .pin p =>
          if minaLinkAir.legs.any (fun m => p.col ∈ m.readCols) then none else some p.col
      | _      => none)
      = [40, 41, 42, 43, 44, 45, 46, 47] := by decide

/-- **`minaLinkDesc` — COMPILER OUTPUT.** The exhibited Mina segment as a multi-row IR-v2 AIR.
⚑ Via `lowerAirCertified` since 2026-08-08 (see the section above): the tie verdict is red and
SAID to be red, not carried by a stale walker. -/
def minaLinkDesc : EffectVmDescriptor2 :=
  (Dregg2.Circuit.Emit.EffectLower.lowerAirCertified
    "dregg-mina-lightclient-link::v1" MINA_LINK_WIDTH MINA_LINK_PI_COUNT [] minaLinkAir
    minaLinkAir_mainRailOk).val

/-- ⚑ **THE CERTIFICATE, produced by the emit.** Every leg of the source is FORCED by the emitted
descriptor's constraints on any row window that satisfies them — `AirLeg.forces`, stated in the
SOURCE's vocabulary and never mentioning the lowering, so it is not `P → P`. Not re-derived here.

**Zero bytes move**: `lowerAirCertified … |>.val` is `lowerAir …` by `rfl`. -/
theorem minaLinkDesc_certified :
    Dregg2.Circuit.Emit.EffectLower.CertifiedRefines minaLinkDesc [] minaLinkAir :=
  (Dregg2.Circuit.Emit.EffectLower.lowerAirCertified
    "dregg-mina-lightclient-link::v1" MINA_LINK_WIDTH MINA_LINK_PI_COUNT [] minaLinkAir
    minaLinkAir_mainRailOk).property

/-- ⚑ **THE ZERO.** The certified lowering emits the term the bare lowering emitted, by `rfl` — so
the migration changed what this definition PROVES, not what it PRODUCES. No re-emit, no VK rotation.
Also the unfolding lemma for the cost/shape proofs below, which reason through `lowerAir`. -/
theorem minaLinkDesc_eq_lowerAir :
    minaLinkDesc = Dregg2.Circuit.Emit.EffectLower.lowerAir "dregg-mina-lightclient-link::v1" MINA_LINK_WIDTH MINA_LINK_PI_COUNT [] minaLinkAir := rfl

/-! ### §3a — the emission pins. `rfl` against the compiler's output, so a change in the leg
lowerings, the leg ORDER or `assemble` goes red here. -/

theorem minaLinkDesc_name : minaLinkDesc.name = "dregg-mina-lightclient-link::v1" := rfl
theorem minaLinkDesc_width : minaLinkDesc.traceWidth = MINA_LINK_WIDTH := rfl
theorem minaLinkDesc_piCount : minaLinkDesc.piCount = MINA_LINK_PI_COUNT := rfl
theorem minaLinkDesc_tables : minaLinkDesc.tables = [minaLaneTable, minaTopLaneTable] := rfl
theorem minaLinkDesc_hashSites : minaLinkDesc.hashSites = [] := rfl
theorem minaLinkDesc_ranges : minaLinkDesc.ranges = [] := rfl

/-- One hundred and eight constraints from seventy-one legs: one per leg except the five `.limbs`
legs, which lower to EIGHT (parent, own, body) and NINE (each attested program) lookups. A dropped
lane moves this and nothing else does. ⚑ 72 → 99 on the 2026-08-08 publication flag day; ⚑⚑
99 → 108 on the 2026-08-10 `PI_HEAD_OWN` publication. -/
theorem minaLinkDesc_constraint_count : minaLinkDesc.constraints.length = 108 := rfl

/-- ⚑⚑ **THE SEAM, AT ITS EMITTED POSITION, ON THE COMPILER'S OUTPUT.** Constraint 51 is the
`proofBind`: an unconditional guard, a commitment whose first 27 lanes are the pinned salt
CONSTANTS and whose remaining 27 are this row's parent, body hash and own hash, and nine attested
program columns pinned to the absorb descriptor's fingerprint. A leg that silently dropped the salt
head, or swapped a `.const` for a `.var`, moves this. -/
theorem minaLinkDesc_state_hash_seam :
    (minaLinkDesc.constraints.drop 51).take 1 =
      [ .proofBind
          { guard  := Dregg2.Exec.CircuitEmit.emitExpr (.const 1)
          , commit := seamCommitLanes.map Dregg2.Exec.CircuitEmit.emitExpr
          , vk     := hashVkCommitLanes.map Dregg2.Exec.CircuitEmit.emitExpr
          , vkPin  := some ABSORB_VK_LANES
          , bound  := .port ⟨"state-hash-preimage", "dregg_turn::executor::mina_head_verifier::check_state_hash_preimage_binding"⟩ } ] := rfl

/-- ⚑ **THE COMMITMENT NAMES ALL FOUR OBJECTS AND NOTHING ELSE.** Thirty-six lanes: 27 constants
then this row's three nonets, in that order. Stated separately from the byte pin above because it is
the property the derivation theorem consumes. -/
theorem minaLink_commit_is_salt_then_the_row :
    (match (minaLinkDesc.constraints.drop 51).head? with
     | some (.proofBind m) => m.commit
     | _ => []) =
      (MINA_PROTO_STATE_SALT_LANES.map Expr.const
        ++ parentCommitLanes ++ bodyCommitLanes ++ ownCommitLanes).map
          Dregg2.Exec.CircuitEmit.emitExpr := rfl

/-- ⚑ **AND IT IS THE ONLY ONE.** One seam, so `proofBind_bound`'s `∀ m ∈ proofBindsOf d` is about
this leg and no other, and the `proofBindDeclarative` census is zero. -/
theorem minaLink_has_two_pinned_seams :
    (Dregg2.Circuit.DescriptorIR2.proofBindsOf minaLinkDesc).length = 2
      ∧ Dregg2.Circuit.DescriptorIR2.proofBindDeclarative minaLinkDesc = 0 := by
  refine ⟨?_, ?_⟩ <;> rfl

/-- ⚑ **THE NINE LANE-CONTINUITY GATES, AT THEIR EMITTED POSITIONS, AS TRANSITION WINDOWS.** `rfl` on
a slice of the compiler's output. A lane that lost its gate, or a gate that drifted off
`on_transition`, moves this — and an `onTransition := false` here would be UNSATISFIABLE on the last
row rather than merely weaker, so the polarity is load-bearing in both directions. -/
theorem minaLinkDesc_lane_continuity_gates :
    minaLinkDesc.constraints.take 9 =
      (List.range 9).map (fun j =>
        VmConstraint2.windowGate
          ⟨.add (loc (OWNHASH j)) (.mul (.const (-1)) (nxt (PARENT j))), true⟩) := rfl

/-- ⚑ **THE SIXTEEN LANE LOOKUPS AND THE TWO TOP-LANE LOOKUPS.** Constraints 15..22 are the parent's
low lanes at 29 bits, 23 is the parent's TOP lane on the NARROW table, 24..31 the own-hash low lanes,
32 the own-hash top lane. A top-lane query that drifted onto the wide table moves this. -/
theorem minaLinkDesc_canon_lookups :
    (minaLinkDesc.constraints.drop 15).take 18 =
      [ .lookup ⟨minaRangeTid MINA_LANE_BITS, [.var (PARENT 0)]⟩
      , .lookup ⟨minaRangeTid MINA_LANE_BITS, [.var (PARENT 1)]⟩
      , .lookup ⟨minaRangeTid MINA_LANE_BITS, [.var (PARENT 2)]⟩
      , .lookup ⟨minaRangeTid MINA_LANE_BITS, [.var (PARENT 3)]⟩
      , .lookup ⟨minaRangeTid MINA_LANE_BITS, [.var (PARENT 4)]⟩
      , .lookup ⟨minaRangeTid MINA_LANE_BITS, [.var (PARENT 5)]⟩
      , .lookup ⟨minaRangeTid MINA_LANE_BITS, [.var (PARENT 6)]⟩
      , .lookup ⟨minaRangeTid MINA_LANE_BITS, [.var (PARENT 7)]⟩
      , .lookup ⟨minaRangeTid MINA_TOP_LANE_BITS, [.var (PARENT 8)]⟩
      , .lookup ⟨minaRangeTid MINA_LANE_BITS, [.var (OWNHASH 0)]⟩
      , .lookup ⟨minaRangeTid MINA_LANE_BITS, [.var (OWNHASH 1)]⟩
      , .lookup ⟨minaRangeTid MINA_LANE_BITS, [.var (OWNHASH 2)]⟩
      , .lookup ⟨minaRangeTid MINA_LANE_BITS, [.var (OWNHASH 3)]⟩
      , .lookup ⟨minaRangeTid MINA_LANE_BITS, [.var (OWNHASH 4)]⟩
      , .lookup ⟨minaRangeTid MINA_LANE_BITS, [.var (OWNHASH 5)]⟩
      , .lookup ⟨minaRangeTid MINA_LANE_BITS, [.var (OWNHASH 6)]⟩
      , .lookup ⟨minaRangeTid MINA_LANE_BITS, [.var (OWNHASH 7)]⟩
      , .lookup ⟨minaRangeTid MINA_TOP_LANE_BITS, [.var (OWNHASH 8)]⟩ ] := rfl

/-- ⚑ **THE TWENTY PI PINS, AND THE TWO THAT MATTER ARE `.last`.** Nine first-row anchor lanes, nine
LAST-row tip lanes, the first-row anchor height, and — the tooth — the LAST-row `REAL_COUNT` as
`PI_SEG_LEN`. A `.last` pin re-scoped to `.first` would read the first row's counter (always
`IS_REAL[0] ∈ {0,1}`) and the segment length would be free again. -/
theorem minaLinkDesc_pins :
    minaLinkDesc.constraints.drop 62 =
      [ .base (.piBinding VmRow.first (PARENT 0) (PI_ANCHOR 0))
      , .base (.piBinding VmRow.first (PARENT 1) (PI_ANCHOR 1))
      , .base (.piBinding VmRow.first (PARENT 2) (PI_ANCHOR 2))
      , .base (.piBinding VmRow.first (PARENT 3) (PI_ANCHOR 3))
      , .base (.piBinding VmRow.first (PARENT 4) (PI_ANCHOR 4))
      , .base (.piBinding VmRow.first (PARENT 5) (PI_ANCHOR 5))
      , .base (.piBinding VmRow.first (PARENT 6) (PI_ANCHOR 6))
      , .base (.piBinding VmRow.first (PARENT 7) (PI_ANCHOR 7))
      , .base (.piBinding VmRow.first (PARENT 8) (PI_ANCHOR 8))
      , .base (.piBinding VmRow.last (OWNHASH 0) (PI_TIP 0))
      , .base (.piBinding VmRow.last (OWNHASH 1) (PI_TIP 1))
      , .base (.piBinding VmRow.last (OWNHASH 2) (PI_TIP 2))
      , .base (.piBinding VmRow.last (OWNHASH 3) (PI_TIP 3))
      , .base (.piBinding VmRow.last (OWNHASH 4) (PI_TIP 4))
      , .base (.piBinding VmRow.last (OWNHASH 5) (PI_TIP 5))
      , .base (.piBinding VmRow.last (OWNHASH 6) (PI_TIP 6))
      , .base (.piBinding VmRow.last (OWNHASH 7) (PI_TIP 7))
      , .base (.piBinding VmRow.last (OWNHASH 8) (PI_TIP 8))
      , .base (.piBinding VmRow.first ANCHOR_H PI_ANCHOR_H)
      , .base (.piBinding VmRow.last REAL_COUNT PI_SEG_LEN)
      , .base (.piBinding VmRow.first (BODYHASH 0) (PI_BODYHASH 0))
      , .base (.piBinding VmRow.first (BODYHASH 1) (PI_BODYHASH 1))
      , .base (.piBinding VmRow.first (BODYHASH 2) (PI_BODYHASH 2))
      , .base (.piBinding VmRow.first (BODYHASH 3) (PI_BODYHASH 3))
      , .base (.piBinding VmRow.first (BODYHASH 4) (PI_BODYHASH 4))
      , .base (.piBinding VmRow.first (BODYHASH 5) (PI_BODYHASH 5))
      , .base (.piBinding VmRow.first (BODYHASH 6) (PI_BODYHASH 6))
      , .base (.piBinding VmRow.first (BODYHASH 7) (PI_BODYHASH 7))
      , .base (.piBinding VmRow.first (BODYHASH 8) (PI_BODYHASH 8))
      , .base (.piBinding VmRow.first (BODY_ACC 0) (PI_BODY_ACC 0))
      , .base (.piBinding VmRow.first (BODY_ACC 1) (PI_BODY_ACC 1))
      , .base (.piBinding VmRow.first (BODY_ACC 2) (PI_BODY_ACC 2))
      , .base (.piBinding VmRow.first (BODY_ACC 3) (PI_BODY_ACC 3))
      , .base (.piBinding VmRow.first (BODY_ACC 4) (PI_BODY_ACC 4))
      , .base (.piBinding VmRow.first (BODY_ACC 5) (PI_BODY_ACC 5))
      , .base (.piBinding VmRow.first (BODY_ACC 6) (PI_BODY_ACC 6))
      , .base (.piBinding VmRow.first (BODY_ACC 7) (PI_BODY_ACC 7))
      -- ⚑⚑⚑ 2026-08-10 — the nine that give the `state-hash-preimage` port an output to land on.
      -- ⚠ `.first`, against `tipPins`' `.last` on the SAME columns: see `PI_HEAD_OWN`.
      , .base (.piBinding VmRow.first (OWNHASH 0) (PI_HEAD_OWN 0))
      , .base (.piBinding VmRow.first (OWNHASH 1) (PI_HEAD_OWN 1))
      , .base (.piBinding VmRow.first (OWNHASH 2) (PI_HEAD_OWN 2))
      , .base (.piBinding VmRow.first (OWNHASH 3) (PI_HEAD_OWN 3))
      , .base (.piBinding VmRow.first (OWNHASH 4) (PI_HEAD_OWN 4))
      , .base (.piBinding VmRow.first (OWNHASH 5) (PI_HEAD_OWN 5))
      , .base (.piBinding VmRow.first (OWNHASH 6) (PI_HEAD_OWN 6))
      , .base (.piBinding VmRow.first (OWNHASH 7) (PI_HEAD_OWN 7))
      , .base (.piBinding VmRow.first (OWNHASH 8) (PI_HEAD_OWN 8)) ] := rfl

/-- ⚑⚑⚑ **THE TWO `OWNHASH` PUBLICATIONS ARE DIFFERENT ROWS, AND THAT IS THE COVER'S WHOLE
CONTENT.** `PI_TIP` reads the LAST row's own hash; `PI_HEAD_OWN` reads the FIRST row's. They name
the same nine COLUMNS and different `VmRow` selectors, so on any segment longer than one row they
are different values.

Stated as a theorem rather than a comment because the cheap mistake — covering the port against
`PI_TIP` — is exactly the ∃-image vacuity `PI_HEAD_OWN`'s docblock names: at the last row both
absorbed elements are unpublished, so a prover picks a pair, computes its image and publishes THAT
as the tip. At the first row both are grounded. A future edit that "simplifies" these to one block
reds here. -/
theorem the_head_own_pins_are_a_different_row_than_the_tip_pins :
    headOwnPins.filterMap (fun l => match l with | .pin p => some (p.row, p.col) | _ => none)
        = (List.range STATE_LIMBS).map (fun j => (VmRow.first, OWNHASH j))
      ∧ tipPins.filterMap (fun l => match l with | .pin p => some (p.row, p.col) | _ => none)
        = (List.range STATE_LIMBS).map (fun j => (VmRow.last, OWNHASH j))
      ∧ headOwnPins.length = STATE_LIMBS
      ∧ (∀ j, (PI_HEAD_OWN j) ≠ (PI_TIP j)) := by
  refine ⟨by decide, by decide, by decide, fun j => ?_⟩
  simp only [PI_HEAD_OWN, PI_TIP, STATE_LIMBS]
  omega

/-- ⚑⚑⚑ **THE BODY-CHAIN SEAM, AT ITS EMITTED POSITION.** Constraint 61 is the second `proofBind`:
an unconditional guard, a commitment whose first 27 lanes are the pinned `MinaProtoStateBody` salt
CONSTANTS, then this row's body-hash nonet, then the chain's EIGHT-lane ordered accumulator, and
nine attested program columns pinned to `dregg-pasta-fp-chainlink::v1`'s fingerprint.

⚠ A leg that dropped the accumulator tail — the exact vacuity §2c names — moves this. -/
theorem minaLinkDesc_body_chain_seam :
    (minaLinkDesc.constraints.drop 61).take 1 =
      [ .proofBind
          { guard  := Dregg2.Exec.CircuitEmit.emitExpr (.const 1)
          , commit := bodyChainCommitLanes.map Dregg2.Exec.CircuitEmit.emitExpr
          , vk     := chainVkCommitLanes.map Dregg2.Exec.CircuitEmit.emitExpr
          , vkPin  := some FP_CHAINLINK_VK_LANES
          , bound  := .port ⟨"body-hash",
              "dregg_turn::executor::mina_head_verifier::check_body_chain_binding"⟩ } ] := rfl

/-- ⚑⚑ **THE BODY-CHAIN SEAM NAMES THE ABSORBED STREAM, NOT JUST `(salt, BODYHASH)`.** Forty-four
commit lanes: 27 salt constants, 9 body-hash lanes, 8 accumulator lanes. ⚠ The 8 is the whole
anti-vacuity content — with 36 the bind would be a hash from a pinned head over a FREE stream, and
`perm` being a permutation means such a bind refuses nothing. -/
theorem minaLink_body_chain_seam_binds_the_stream :
    (match bodyChainBindLeg with | .bind b => b.mainRailOk | _ => false) = true
      ∧ (match bodyChainBindLeg with | .bind b => b.commit.length | _ => 0) = 44
      ∧ (match bodyChainBindLeg with | .bind b => b.vk.length | _ => 0) = 9
      ∧ bodyAccCommitLanes.length = 8 := by
  refine ⟨by rfl, by rfl, by rfl, by rfl⟩

/-- ⚑ **THE TWO SEAMS NAME TWO DIFFERENT SALTS.** Mina's domain separation between `state_hash` and
`state_body_hash` is exactly this, and a copy-paste that reused `MINA_PROTO_STATE_SALT_LANES` here
would name a different hash function with every gate green. -/
theorem the_two_seams_name_two_different_salts :
    MINA_PROTO_STATE_BODY_SALT_LANES ≠ MINA_PROTO_STATE_SALT_LANES := by decide

/-- ⚑ **THE BODY SALT LANES ARE THE BODY SALT.** The 27 `.const` lanes recompose, nine at a time
base `2^29`, to the three elements of `Bridge.MinaStateHashDerive.saltProtoStateBody` — itself
pinned to openmina's own regression constants. Without this the constants are a transcription
nothing checks.

⚠ `native_decide`: `saltProtoStateBody` is a Kimchi Poseidon permutation and reducing one under the
kernel is measured at 47.6 GB / 68 min in this tree. Compiled evaluator, confessed. -/
theorem mina_link_body_salt_lanes_are_the_body_salt :
    MINA_PROTO_STATE_BODY_SALT_LANES =
      ((Dregg2.Bridge.MinaStateHashDerive.saltProtoStateBody.flatMap
        (fun v => (List.range 9).map (fun i => ((v / 2 ^ (29 * i)) % 2 ^ 29 : Nat)))).map
          (fun n => (n : ℤ))) := by native_decide

/-- Layout sanity as theorems: the two nonets are contiguous, disjoint and inside the declared
width, and the counting columns sit above them. -/
theorem minaLink_layout_wellformed :
    PARENT 0 = 0 ∧ PARENT 8 = 8 ∧ OWNHASH 0 = 9 ∧ OWNHASH 8 = 17
      ∧ HEIGHT = 18 ∧ IS_REAL = 19 ∧ REAL_COUNT = 20 ∧ ANCHOR_H = 21
      ∧ BODYHASH 0 = 22 ∧ BODYHASH 8 = 30 ∧ HASH_VK 0 = 31 ∧ HASH_VK 8 = 39
      ∧ BODY_ACC 0 = 40 ∧ BODY_ACC 7 = 47 ∧ CHAIN_VK 0 = 48 ∧ CHAIN_VK 8 = 56
      ∧ MINA_LINK_WIDTH = 57
      ∧ PI_BODYHASH 0 = 20 ∧ PI_BODYHASH 8 = 28 ∧ PI_BODY_ACC 0 = 29 ∧ PI_BODY_ACC 7 = 36
      ∧ PI_HEAD_OWN 0 = 37 ∧ PI_HEAD_OWN 8 = 45
      ∧ MINA_LINK_PI_COUNT = 46
      ∧ CHAIN_VK 8 < MINA_LINK_WIDTH ∧ PI_HEAD_OWN 8 < MINA_LINK_PI_COUNT := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩ <;> decide

/-- ⚑ **THE SALT LANES ARE THE SALT.** The 27 `.const` lanes of the seam's commitment head
recompose, nine at a time base `2^29`, to the three elements of
`Bridge.MinaStateHashDerive.saltProtoState` — which is itself pinned to openmina's own regression
constants. Without this the constants are a transcription nothing checks, and a wrong lane would
name a different hash function while every gate stayed green.

⚠ `native_decide`: `saltProtoState` is a Kimchi Poseidon permutation, and reducing one under the
kernel is measured at 47.6 GB / 68 min in this tree. This is the compiled evaluator, confessed. -/
theorem mina_link_salt_lanes_are_the_salt :
    MINA_PROTO_STATE_SALT_LANES =
      ((Dregg2.Bridge.MinaStateHashDerive.saltProtoState.flatMap
        (fun v => (List.range 9).map (fun i => ((v / 2 ^ (29 * i)) % 2 ^ 29 : Nat)))).map
          (fun n => (n : ℤ))) := by native_decide

/-! ### §3b — ⚑ THE (a)/(b) DECISION, DECIDED ON THE EMITTED BYTES.

The header claims this rung needs no non-native multiplication. That is not a promise about intent.
`prodCols` collects the columns appearing under a `.mul` whose BOTH sides read a trace cell — the
syntactic signature of a limb product — and the theorem below says the whole descriptor's set is
`{IS_REAL}`. So no gate multiplies two different columns anywhere, hence no schoolbook limb-product
accumulator is reachable from this descriptor and it inherits nothing from the Pasta cone. -/

/-- Does this body read a trace cell at all? -/
def readsCell : WindowExpr → Bool
  | .loc _ => true
  | .nxt _ => true
  | .const _ => false
  | .add a b => readsCell a || readsCell b
  | .mul a b => readsCell a || readsCell b

/-- Every column index this body reads. -/
def cellCols : WindowExpr → List Nat
  | .loc c => [c]
  | .nxt c => [c]
  | .const _ => []
  | .add a b => cellCols a ++ cellCols b
  | .mul a b => cellCols a ++ cellCols b

/-- ⚑ The columns appearing under a product of two cell-reading factors. Empty for a body that is
affine in the trace; `[c]` for a body squaring one column; two DIFFERENT indices exactly when the
body multiplies two distinct witnesses, which is the limb-product signature. -/
def prodCols : WindowExpr → List Nat
  | .loc _ => []
  | .nxt _ => []
  | .const _ => []
  | .add a b => prodCols a ++ prodCols b
  | .mul a b =>
      (if readsCell a && readsCell b then cellCols a ++ cellCols b else []) ++
        prodCols a ++ prodCols b

/-- The product columns of one emitted constraint (only window gates carry bodies here). -/
def constraintProdCols : VmConstraint2 → List Nat
  | .windowGate w => prodCols w.body
  | _ => []

/-- ⚑⚑ **NO PRODUCT OF TWO DISTINCT COLUMNS ANYWHERE IN THE EMITTED OBJECT.** The only column that
ever appears under a two-sided product is `IS_REAL` — the boolean pin `x·(x−1)` and the monotone pin
`x'·(1−x)`, both degree 2 in ONE column and neither a limb product. This is the (a)/(b) decision
decided on the compiler's output rather than asserted in prose: a non-native Pasta multiply would put
two different limb columns in this list. -/
theorem minaLink_products_are_only_the_real_bit :
    (minaLinkDesc.constraints.flatMap constraintProdCols).eraseDups = [IS_REAL] := by rfl

/-- …and the emitted bodies never multiply two DIFFERENT columns: the product-column set is a
singleton. Stated separately because it is the property that matters (a limb product needs two
indices) and it survives a re-layout that moves `IS_REAL`. -/
theorem minaLink_no_two_column_product :
    (minaLinkDesc.constraints.flatMap constraintProdCols).eraseDups.length = 1 := by rfl

/-! ## §4 — the acceptance predicate, and its tie to the EMITTED bodies.

Acceptance is stated over a `VmRowEnv` window (`loc`/`nxt`/`pub`), exactly as
`EffectVmEmitTurnChainBinding.turnChainWindowHolds` is, so it is the emitted constraint set's own
denotation rather than a private notion. -/

/-- The emitted constraint set, on one row window. -/
def linkWindowHolds (hash : List ℤ → ℤ) (tf : Dregg2.Circuit.DescriptorIR2.TraceFamily)
    (env : VmRowEnv) (isFirst isLast : Bool) : Prop :=
  ∀ c ∈ minaLinkDesc.constraints, c.holdsAt hash tf env isFirst isLast

/-- ⚑ **A TRANSITION WINDOW MEANS ITS BODY VANISHES mod `P`** — the window analog of
`LightClientMinaAir.emitted_gate_means_source`, so §7's conjuncts are the emitted bodies' meaning and
not a restatement of them. -/
theorem emitted_transition_means_body (hash : List ℤ → ℤ)
    (tf : Dregg2.Circuit.DescriptorIR2.TraceFamily) (env : VmRowEnv) (isFirst : Bool)
    (body : WindowExpr) :
    (VmConstraint2.windowGate ⟨body, true⟩).holdsAt hash tf env isFirst false
      ↔ body.eval env ≡ 0 [ZMOD 2013265921] := by
  simp [VmConstraint2.holdsAt, WindowConstraint.holdsAt]

/-- …and an `.all`-scoped window vanishes on every row, the LAST row included. That is why the
boolean pin is `.all`: at `.transition` a padding row in the final slot would be unpinned. -/
theorem emitted_all_means_body (hash : List ℤ → ℤ)
    (tf : Dregg2.Circuit.DescriptorIR2.TraceFamily) (env : VmRowEnv) (isFirst isLast : Bool)
    (body : WindowExpr) :
    (VmConstraint2.windowGate ⟨body, false⟩).holdsAt hash tf env isFirst isLast
      ↔ body.eval env ≡ 0 [ZMOD 2013265921] := by
  simp [VmConstraint2.holdsAt, WindowConstraint.holdsAt]

/-! ## §5 — ⚑ THE COUPLING: canonical lanes make the mod-`P` linkage an EXACT equality. -/

/-- Every lane of a canonical nonet lies in `[0, P)` — the hypothesis the exactness lemma needs, and
it is DERIVED from the emitted lookups rather than assumed (`2^29 < P` and `2^22 < P`). -/
theorem limbsInRange_below_field {a : Assignment} :
    ∀ l : List Nat, LimbsInRange MINA_LANE_BITS a l → ∀ c ∈ l, 0 ≤ a c ∧ a c < 2013265921 := by
  intro l
  induction l with
  | nil => intro _ c hc; simp at hc
  | cons d ds ih =>
    rintro ⟨⟨hd0, hdlt⟩, hrest⟩ c hc
    rcases List.mem_cons.mp hc with rfl | hc'
    · exact ⟨hd0, lt_of_lt_of_le hdlt (by norm_num [MINA_LANE_BITS])⟩
    · exact ih hrest c hc'

theorem laneCanon_lane_below_field {a : Assignment} {low : List Nat} {top : Nat}
    (h : laneCanon a low top) :
    (∀ c ∈ low, 0 ≤ a c ∧ a c < 2013265921) ∧ (0 ≤ a top ∧ a top < 2013265921) := by
  obtain ⟨hlow, htop0, htoplt⟩ := h
  exact ⟨limbsInRange_below_field low hlow,
         htop0, lt_of_lt_of_le htoplt (by norm_num [MINA_TOP_LANE_BITS])⟩

/-- ⚑ **THE EXACTNESS LEMMA.** A lane-continuity gate forces `OWNHASH[j] − PARENT'[j] ≡ 0 [ZMOD P]`.
With BOTH lanes range-gated below `2^29 < P` — which the canonicality legs of the SAME descriptor
force — the congruence is an EXACT equality. ⚠ Without the canonicality rung this is FALSE: each lane
could differ by `P` and every gate would still hold. The two rungs are coupled. -/
theorem link_lane_equality_is_exact {x y : ℤ}
    (hx : 0 ≤ x ∧ x < 2013265921) (hy : 0 ≤ y ∧ y < 2013265921)
    (h : x + (-1) * y ≡ 0 [ZMOD 2013265921]) : x = y := by
  rw [Int.modEq_zero_iff_dvd] at h
  obtain ⟨k, hk⟩ := h
  omega

/-! ## §6 — ⚑⚑ THE RESIDUAL, DERIVED. -/

/-- The base-`2^29` recomposition of a LANE VECTOR (as opposed to a column vector). The seam's
`commit` is a list of VALUES, so the tie back to `stateValue` needs this shape. -/
def laneVal : List ℤ → ℤ
  | [] => 0
  | v :: rest => v + (2 : ℤ) ^ MINA_LANE_BITS * laneVal rest

/-- `laneVal` of a column vector's readings IS `limbValue` of the columns — the bridge between the
seam's value-level commitment and this file's column-level `stateValue`. -/
theorem laneVal_map (a : Assignment) :
    ∀ cs : List Nat, laneVal (cs.map a) = limbValue MINA_LANE_BITS a cs := by
  intro cs
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [laneVal, ih]

/-- ⚑ **`minaLinkHash` — MINA'S OWN LINKAGE HASH, at `ℤ`.**
`Bridge.MinaStateHashDerive.stateHash` is `hashFrom saltProtoState [previousStateHash,
stateBodyHash]` (`:392-393`, the daemon's `protocol_state.ml:45-55`). This is that function, on the
two arguments the row carries. It is Mina's, not this file's: no hash is authored here. -/
def minaLinkHash (parent body : ℤ) : ℤ :=
  (Dregg2.Bridge.MinaStateHashDerive.hashFrom
     Dregg2.Bridge.MinaStateHashDerive.saltProtoState [parent.toNat, body.toNat] : ℤ)

/-- ⚑ **THE SEAM, AS THE `ProofBind` THE COMPILER EMITS.** Named so the theorems below can quantify
over `proofBindsOf` and land on THIS object rather than on a re-description of it. -/
def minaLinkSeam : Dregg2.Circuit.DescriptorIR2.ProofBind :=
  { guard  := Dregg2.Exec.CircuitEmit.emitExpr (.const 1)
  , commit := seamCommitLanes.map Dregg2.Exec.CircuitEmit.emitExpr
  , vk     := hashVkCommitLanes.map Dregg2.Exec.CircuitEmit.emitExpr
  , vkPin  := some ABSORB_VK_LANES
  , bound  := .port ⟨"state-hash-preimage", "dregg_turn::executor::mina_head_verifier::check_state_hash_preimage_binding"⟩ }

/-- The nine attested-program lanes a row READS, as values. The seam compares exactly this vector
against `ABSORB_VK_LANES`. -/
def hashVkRead (a : Assignment) : List ℤ := minaLinkSeam.vk.map (fun e => e.eval a)

/-- ⚑ **THE BODY-CHAIN SEAM, AS THE `ProofBind` THE COMPILER EMITS** (2026-08-08). -/
def minaLinkBodyChainSeam : Dregg2.Circuit.DescriptorIR2.ProofBind :=
  { guard  := Dregg2.Exec.CircuitEmit.emitExpr (.const 1)
  , commit := bodyChainCommitLanes.map Dregg2.Exec.CircuitEmit.emitExpr
  , vk     := chainVkCommitLanes.map Dregg2.Exec.CircuitEmit.emitExpr
  , vkPin  := some FP_CHAINLINK_VK_LANES
  , bound  := .port ⟨"body-hash",
      "dregg_turn::executor::mina_head_verifier::check_body_chain_binding"⟩ }

/-- The emitted descriptor's proof-binding ops are exactly these TWO seams — the state-hash seam
(2026-08-06) and the body-chain seam (2026-08-08), in emission order. ⚑ `proofBind_bound`'s
`∀ m ∈ proofBindsOf d` is about both and no others. -/
theorem minaLink_proofBinds : Dregg2.Circuit.DescriptorIR2.proofBindsOf minaLinkDesc =
    [minaLinkSeam, minaLinkBodyChainSeam] := rfl

/-- ⚑ **A GATED LANE-VECTOR CONGRUENCE IS AN EXACT EQUALITY when both sides are canonical.** The
list-level form of `link_lane_equality_is_exact`, and it is the SAME coupling: `zeroLanes` says
`1·(xᵢ − yᵢ) ≡ 0 [ZMOD P]`, which admits a `+P` alias per lane; the width gates are what collapse
each alias family to a point. ⚠ Without the canonicality hypotheses this is FALSE. -/
theorem zeroLanes_one_exact : ∀ (xs ys : List ℤ),
    (∀ v ∈ xs, 0 ≤ v ∧ v < 2013265921) → (∀ v ∈ ys, 0 ≤ v ∧ v < 2013265921) →
    Dregg2.Circuit.DescriptorIR2.zeroLanes 1 xs ys → xs = ys := by
  intro xs
  induction xs with
  | nil =>
    intro ys _ _ h
    exact (List.eq_nil_of_length_eq_zero h.1.symm).symm
  | cons x xs ih =>
    intro ys hx hy h
    obtain ⟨hlen, hz⟩ := h
    match ys with
    | [] => simp at hlen
    | y :: ys' =>
      have hzip : ((x, y) : ℤ × ℤ) ∈ (x :: xs).zip (y :: ys') := by simp
      have hcong := hz (x, y) hzip
      have hform : (1 : ℤ) * (x - y) = x + (-1) * y := by ring
      rw [hform] at hcong
      have hhead : x = y :=
        link_lane_equality_is_exact (hx x (by simp)) (hy y (by simp)) hcong
      have htail : xs = ys' :=
        ih ys' (fun v hv => hx v (by simp [hv])) (fun v hv => hy v (by simp [hv]))
          ⟨by simpa using hlen, fun p hp => hz p (by simp [hp])⟩
      rw [hhead, htail]

/-- ⚑ **`HashVkCanon`** — the nine attested-program lanes a row reads are field-canonical. This is
the content of the nine emitted 29-bit lookups, stated at the model's own resolution: `Assignment`
is `Nat → ℤ`, so nothing in the TYPE says a column is a residue, while in the deployed prover every
column IS one. It is named because it is precisely what turns the seam's `≡ 0 [ZMOD P]` `vkPin`
congruence into an EXACT program equality — the same coupling `link_lane_equality_is_exact` states
for the lane chain, one object over. -/
def HashVkCanon (a : Assignment) : Prop :=
  ∀ v ∈ hashVkRead a, 0 ≤ v ∧ v < 2013265921

/-- ⚑⚑ **THE SEAM FORCES THE PINNED PROGRAM, EXACTLY.** `ProofBind.holdsAt`'s middle conjunct is
nine congruences `1·(vkⱼ − pinⱼ) ≡ 0 [ZMOD P]`; with the columns canonical and every pin literal
below `2^29`, that is equality of the whole nine-lane fingerprint. So the sub-proof the off-row leg
produces is a proof of `dregg-pasta-fp-absorb::v1` and not of some other program — which is the
difference between this seam and the decorative shape `ProofBind.isDeclarative` counts. -/
theorem seam_forces_the_pinned_program {env : VmRowEnv} (hc : HashVkCanon env.loc)
    (h : Dregg2.Circuit.DescriptorIR2.ProofBind.holdsAt env minaLinkSeam) :
    hashVkRead env.loc = ABSORB_VK_LANES := by
  obtain ⟨-, hvk, -⟩ := h
  refine zeroLanes_one_exact _ _ hc (by decide) ?_
  simpa [hashVkRead, minaLinkSeam, Dregg2.Exec.CircuitEmit.emitExpr,
    Dregg2.Exec.CircuitEmit.EmittedExpr.eval] using hvk

/-- ⚑⚑⚑ **`StateHashEngine` — WHAT THE PINNED SUB-PROGRAM PROVES, as a NAMED hypothesis about the
recursion engine.**

A proof that VERIFIES under the engine and attests the fingerprint of `dregg-pasta-fp-absorb::v1`,
whose public-input commitment is `salt ‖ x ‖ y ‖ z` in `Faithful9` lanes, has
`laneVal z = Poseidon_{salt}(laneVal x, laneVal y)`.

⚑ **Read what this is and what it is not.** It is the sub-program's own denotation, which that
descriptor's file PROVES about the emitted object
(`MinaWrapVerifierSpongeFp.the_fp_absorb_program_squeezes_the_kimchi_hash`,
`the_emitted_fp_absorb_output_is_K3s_hash`, on the SAME `programAir` at `pLimb`, with the incoming
state a public input and `the_absorb_program_permutes_gen` carrying no hypothesis on it). What is
NOT discharged here is the recursion boundary itself — that a verifying STARK implies its statement
— which is the FRI obligation this whole stack carries and names
(`RecursiveAggregation.EngineSound.recursive_sound`). Every `proofBind` in this tree stands at
exactly that resolution; this one is not weaker and not stronger.

⚠ It also carries a LIMB-ENCODING obligation the consumer discharges: the absorb descriptor
publishes 32 eight-bit limbs an element and this seam commits nine base-`2^29` lanes, so the node
re-limbs 54 lanes into six 32-limb blocks and refuses a mismatch. That is an executor check, not a
constraint, and saying so is the point of naming this structure rather than asserting the
conclusion. -/
structure StateHashEngine (E : Dregg2.Circuit.DescriptorIR2.ProofEngine) : Prop where
  squeezes : ∀ p : E.Proof, E.verify p = true → E.vkOf p = ABSORB_VK_LANES →
    ∀ x y z : List ℤ,
      E.piCommit p = MINA_PROTO_STATE_SALT_LANES ++ x ++ y ++ z →
      laneVal z = minaLinkHash (laneVal x) (laneVal y)

/-- ⚑⚑⚑ **THE CLOSURE: A ROW'S `OWNHASH` IS THE IMAGE OF THAT ROW.** Given the seam's row-local
half (which pins the program) and its off-row half (which produces the verifying sub-proof), the
row's own-hash nonet denotes `Poseidon_{MinaProtoState}(parent, bodyHash)` — Mina's own linkage
hash, on this row's own two lanes. `OWNHASH` is no longer a value a prover writes down. -/
theorem seam_derives_the_own_hash (E : Dregg2.Circuit.DescriptorIR2.ProofEngine)
    (hSH : StateHashEngine E) {env : VmRowEnv} (hc : HashVkCanon env.loc)
    (hrow : Dregg2.Circuit.DescriptorIR2.ProofBind.holdsAt env minaLinkSeam)
    (hbound : Dregg2.Circuit.DescriptorIR2.ProofBind.boundAt E env minaLinkSeam) :
    ownHashValue env.loc
      = minaLinkHash (parentValue env.loc) (bodyHashValue env.loc) := by
  obtain ⟨p, hp, hpc, hpv⟩ := hbound rfl
  have hvk : E.vkOf p = ABSORB_VK_LANES := by
    rw [hpv]; simpa [hashVkRead] using seam_forces_the_pinned_program hc hrow
  have hsplit : minaLinkSeam.commit.map (fun e => e.eval env.loc) =
      MINA_PROTO_STATE_SALT_LANES
        ++ (Dregg2.Circuit.Emit.LightClientMinaAir.nonetOf parentLowLanes (PARENT 8)).map env.loc
        ++ (Dregg2.Circuit.Emit.LightClientMinaAir.nonetOf bodyHashLowLanes (BODYHASH 8)).map env.loc
        ++ (Dregg2.Circuit.Emit.LightClientMinaAir.nonetOf ownHashLowLanes (OWNHASH 8)).map env.loc :=
    rfl
  have hsq := hSH.squeezes p hp hvk _ _ _ (by rw [hpc, hsplit])
  rw [laneVal_map, laneVal_map, laneVal_map] at hsq
  exact hsq

/-- ⚑ **`LinkOwnHashIsImage` — what the seam DERIVES, over a whole segment.** Every row's own-hash
nonet denotes Mina's linkage hash of that row's own two lanes. `seam_derives_the_own_hash` is the
per-row form; this is the list form the refinement consumes. -/
def LinkOwnHashIsImage (rows : List Assignment) : Prop :=
  ∀ i, (hi : i < rows.length) →
    ownHashValue rows[i] = minaLinkHash (parentValue rows[i]) (bodyHashValue rows[i])

/-- ⚑ **`LinkHashResidual` — RETAINED, BUT NO LONGER A RESIDUAL.**

Row `i`'s `OWNHASH` denotes the protocol-state hash of block `i`. Until 2026-08-06 this was an
ASSUMPTION every theorem below carried: *"the Pasta multiply, discharged by the witness generator,
i.e. TRUSTED"*. It is a CONCLUSION now — `linkHashResidual_of_seam` derives it from the emitted
seam plus `LeafHashIsMina`, and the only thing left in that second hypothesis is an ENCODING claim
with no hash in it. The `Prop` keeps its name because §8 is stated in terms of it and the name is
what a reader greps for; what changed is which side of the turnstile it sits on. -/
def LinkHashResidual (L : MinaLeaf) (enc : L.Digest → ℤ) (rows : List Assignment)
    (blocks : List (MinaHeader L)) : Prop :=
  ∀ i, (hi : i < rows.length) → (hb : i < blocks.length) →
    ownHashValue rows[i] = enc (blockHash L blocks[i])

/-- ⚑ **`LeafHashIsMina` — ALL THAT REMAINS of the old residual, and it computes no hash.** The
ABSTRACT bridge leaf's `MinaLeaf.stateHash` is Mina's own `MinaStateHashDerive.stateHash`, read
through the lane encoding. ⚠ This is `LightClientMinaHashFold`'s named RESIDUAL #2 — the
protocol-state PREIMAGE SHAPE — and it is genuinely still open at the bridge-leaf boundary: the
abstract leaf hashes a four-tuple while the daemon hashes `[previous_state_hash ; state_body_hash]`
over a `Body.to_input` of ~38 elements. Naming it here keeps the two apart instead of letting the
seam's closure launder it. -/
def LeafHashIsMina (L : MinaLeaf) (enc : L.Digest → ℤ) (rows : List Assignment)
    (blocks : List (MinaHeader L)) : Prop :=
  ∀ i, (hi : i < rows.length) → (hb : i < blocks.length) →
    enc (blockHash L blocks[i]) = minaLinkHash (parentValue rows[i]) (bodyHashValue rows[i])

/-- ⚑⚑ **THE RESIDUAL, DISCHARGED.** What §8 took as a hypothesis is now the composition of a fact
the descriptor forces (`LinkOwnHashIsImage`, out of the seam) with a fact that computes nothing
(`LeafHashIsMina`). ⚑ Read the asymmetry: the *hash* moved to the sub-proof; what is left is the
claim that two spellings of the same digest agree. -/
theorem linkHashResidual_of_seam (L : MinaLeaf) (enc : L.Digest → ℤ)
    (rows : List Assignment) (blocks : List (MinaHeader L))
    (himg : LinkOwnHashIsImage rows) (hleaf : LeafHashIsMina L enc rows blocks) :
    LinkHashResidual L enc rows blocks := by
  intro i hi hb
  rw [himg i hi, hleaf i hi hb]

/-- The companion tie for the PARENT nonet. ⚑ Like `LeafHashIsMina` this is a pure ENCODING
statement — no hash is computed — discharged by writing the nine lanes of a value the generator
already holds (`turn/src/executor/mina_head_verifier.rs::check_head_binding` computes exactly this
decomposition). -/
def LinkParentEncoding (L : MinaLeaf) (enc : L.Digest → ℤ) (rows : List Assignment)
    (blocks : List (MinaHeader L)) : Prop :=
  ∀ i, (hi : i < rows.length) → (hb : i < blocks.length) →
    parentValue rows[i] = enc (blocks[i]).parent

/-! ## §7 — the segment predicate over a whole trace, and the derived facts. -/

/-- One adjacent-row window's content, as the five transition gates force it (exactly on the lane
half, via §5's coupling). -/
structure LinkStep (a b : Assignment) : Prop where
  /-- The nine lane equalities — `OWNHASH[i] = PARENT[i+1]`, `rootContinuity` at nine lanes. -/
  lanes : ∀ j, j < STATE_LIMBS → a (OWNHASH j) = b (PARENT j)
  /-- The height ticks by exactly one. -/
  height : b HEIGHT = a HEIGHT + 1
  /-- Real rows are a prefix. -/
  monotone : b IS_REAL * (1 - a IS_REAL) = 0
  /-- The counter accumulates. -/
  count : b REAL_COUNT = a REAL_COUNT + b IS_REAL

/-- The first row's boundary content (two `.first` windows and ten `.first` pins). -/
structure LinkFirst (a : Assignment) (pub : Assignment) : Prop where
  anchor : ∀ j, j < STATE_LIMBS → a (PARENT j) = pub (PI_ANCHOR j)
  anchorH : a ANCHOR_H = pub PI_ANCHOR_H
  height : a HEIGHT = a ANCHOR_H + 1
  count : a REAL_COUNT = a IS_REAL

/-- The last row's boundary content (ten `.last` pins). -/
structure LinkLast (a : Assignment) (pub : Assignment) : Prop where
  tip : ∀ j, j < STATE_LIMBS → a (OWNHASH j) = pub (PI_TIP j)
  segLen : a REAL_COUNT = pub PI_SEG_LEN

/-- ⚑ All THREE nonets of a row are canonical `Fp` elements — the twenty-seven per-row lookups.
`BODYHASH` joined on 2026-08-06 and it is not decoration: it is an ARGUMENT of the hash the seam
binds, and an argument that could sit at `v + p` would let two body hashes give one state hash
(`MinaStateQuery.poseidonPair_shift_collides` — a structural collision, not a birthday event). -/
def RowCanon (a : Assignment) : Prop :=
  laneCanon a parentLowLanes (PARENT 8) ∧ laneCanon a ownHashLowLanes (OWNHASH 8)
    ∧ laneCanon a bodyHashLowLanes (BODYHASH 8)

/-- ⚑ **`linkShapeAccepts` — THE DERIVED PREDICATE, AND ITS NAME STILL SAYS WHAT IT IS.** The
emitted descriptor accepts this trace: every row canonical and `IS_REAL`-boolean, every adjacent
pair a `LinkStep`, the first row anchored, the last row pinned to the tip and to the segment length,
and — new on 2026-08-06 — every row ATTESTING the pinned state-hash program.

⚠ It is still the segment's SHAPE, and the name is not being quietly widened. What the shape
predicate can see of the seam is its ROW-LOCAL half: the guard is a bit and the nine `HASH_VK`
columns are the pinned fingerprint. The half that makes `OWNHASH` an IMAGE is the off-row
existential (`ProofBind.boundAt`), which no row-level predicate can state — that is
`seam_derives_the_own_hash`, and it takes an engine. -/
structure linkShapeAccepts (rows : List Assignment) (pub : Assignment) : Prop where
  nonempty : rows ≠ []
  canon : ∀ a ∈ rows, RowCanon a
  isReal : ∀ a ∈ rows, a IS_REAL * (a IS_REAL - 1) = 0
  steps : List.IsChain LinkStep rows
  first : ∀ a, rows.head? = some a → LinkFirst a pub
  last : ∀ a, rows.getLast? = some a → LinkLast a pub
  /-- ⚑ Every row's nine attested-program lanes ARE `dregg-pasta-fp-absorb::v1`'s fingerprint. This
  is the `vkPin` congruence at the row level, made exact by the nine 29-bit lookups. -/
  program : ∀ a ∈ rows, hashVkRead a = ABSORB_VK_LANES

/-- ⚑ **DERIVED FACT 1 — THE LANE CHAIN IS AN `Fp` CHAIN.** Nine lane equalities on an adjacent pair
give equality of the two nonets' DENOTED field elements. This is `chainLinked`'s `h.parent = prev`
conjunct at the representation BabyBear actually has. -/
theorem step_chains_values {a b : Assignment} (h : LinkStep a b) :
    ownHashValue a = parentValue b := by
  simp only [ownHashValue, parentValue, stateValue,
    Dregg2.Circuit.Emit.LightClientMinaAir.nonetOf, parentLowLanes, ownHashLowLanes,
    List.cons_append, List.nil_append,
    Dregg2.Circuit.LimbTally.limbValue_cons, Dregg2.Circuit.LimbTally.limbValue_nil,
    h.lanes 0 (by decide), h.lanes 1 (by decide), h.lanes 2 (by decide),
    h.lanes 3 (by decide), h.lanes 4 (by decide), h.lanes 5 (by decide), h.lanes 6 (by decide),
    h.lanes 7 (by decide), h.lanes 8 (by decide)]

/-- The `Fp` element the PUBLIC anchor lanes denote. -/
def anchorValue (pub : Assignment) : ℤ :=
  stateValue pub [PI_ANCHOR 0, PI_ANCHOR 1, PI_ANCHOR 2, PI_ANCHOR 3, PI_ANCHOR 4, PI_ANCHOR 5,
    PI_ANCHOR 6, PI_ANCHOR 7] (PI_ANCHOR 8)

/-- The `Fp` element the PUBLIC tip lanes denote. -/
def tipValue (pub : Assignment) : ℤ :=
  stateValue pub [PI_TIP 0, PI_TIP 1, PI_TIP 2, PI_TIP 3, PI_TIP 4, PI_TIP 5, PI_TIP 6, PI_TIP 7]
    (PI_TIP 8)

/-- The first row's nine anchor pins give the `Fp`-level anchoring. -/
theorem first_pins_anchor_value {a pub : Assignment} (h : LinkFirst a pub) :
    parentValue a = anchorValue pub := by
  simp only [parentValue, anchorValue, stateValue,
    Dregg2.Circuit.Emit.LightClientMinaAir.nonetOf, parentLowLanes,
    List.cons_append, List.nil_append,
    Dregg2.Circuit.LimbTally.limbValue_cons, Dregg2.Circuit.LimbTally.limbValue_nil,
    h.anchor 0 (by decide), h.anchor 1 (by decide), h.anchor 2 (by decide),
    h.anchor 3 (by decide), h.anchor 4 (by decide), h.anchor 5 (by decide),
    h.anchor 6 (by decide), h.anchor 7 (by decide), h.anchor 8 (by decide)]

/-- The last row's nine tip pins give the `Fp`-level tip binding. -/
theorem last_pins_tip_value {a pub : Assignment} (h : LinkLast a pub) :
    ownHashValue a = tipValue pub := by
  simp only [ownHashValue, tipValue, stateValue,
    Dregg2.Circuit.Emit.LightClientMinaAir.nonetOf, ownHashLowLanes,
    List.cons_append, List.nil_append,
    Dregg2.Circuit.LimbTally.limbValue_cons, Dregg2.Circuit.LimbTally.limbValue_nil,
    h.tip 0 (by decide), h.tip 1 (by decide), h.tip 2 (by decide),
    h.tip 3 (by decide), h.tip 4 (by decide), h.tip 5 (by decide), h.tip 6 (by decide),
    h.tip 7 (by decide), h.tip 8 (by decide)]

/-- ⚑ **`SegmentFrom` — the `Fp`-level chain the descriptor forces, in `ChainFrom`'s own shape.**
Each row's parent value IS the running value, its height is one more than the running height, and
the running value becomes that row's OWN hash value. Compare `LightClientMina.ChainFrom`
(`Bridge/LightClientMina.lean:214`): the same recursion, over lane-denoted `ℤ` instead of `Digest`. -/
def SegmentFrom (prevVal prevH : ℤ) : List Assignment → Prop
  | [] => True
  | a :: rest =>
      parentValue a = prevVal ∧ a HEIGHT = prevH + 1 ∧
        SegmentFrom (ownHashValue a) (a HEIGHT) rest

/-- ⚑⚑ **DERIVED FACT 2 — ACCEPTANCE IS A CHAIN FROM THE PINNED ANCHOR.** No hypothesis: this is
what the emitted gates force, all of it. The anchor's `Fp` value, the contiguous heights, and every
adjacent link. -/
theorem segmentFrom_of_isChain :
    ∀ (rows : List Assignment) (a : Assignment) (pv ph : ℤ),
      List.IsChain LinkStep (a :: rows) → parentValue a = pv → a HEIGHT = ph + 1 →
      SegmentFrom pv ph (a :: rows) := by
  intro rows
  induction rows with
  | nil => intro a pv ph _ hp hh; exact ⟨hp, hh, trivial⟩
  | cons b rest ih =>
    intro a pv ph hch hp hh
    have hst : LinkStep a b := (List.isChain_cons_cons.mp hch).1
    have hch' : List.IsChain LinkStep (b :: rest) := (List.isChain_cons_cons.mp hch).2
    exact ⟨hp, hh, ih b (ownHashValue a) (a HEIGHT) hch'
      (step_chains_values hst).symm (by rw [hst.height])⟩

theorem linkShapeAccepts_gives_SegmentFrom {rows : List Assignment} {pub : Assignment}
    (h : linkShapeAccepts rows pub) :
    SegmentFrom (anchorValue pub) (pub PI_ANCHOR_H) rows := by
  match rows, h.nonempty with
  | a :: rest, _ =>
    have hf : LinkFirst a pub := h.first a rfl
    exact segmentFrom_of_isChain rest a (anchorValue pub) (pub PI_ANCHOR_H) h.steps
      (first_pins_anchor_value hf) (by rw [hf.height, hf.anchorH])

/-- ⚑ **DERIVED FACT 3 — the heights along an accepted segment are contiguous from the anchor.**
The corollary a reader wants stated in one line. -/
theorem link_heights_are_contiguous {rows : List Assignment} {pub : Assignment}
    (h : linkShapeAccepts rows pub) (a : Assignment) (rest : List Assignment)
    (hrows : rows = a :: rest) : a HEIGHT = pub PI_ANCHOR_H + 1 := by
  subst hrows
  exact ((linkShapeAccepts_gives_SegmentFrom h).2.1)

/-- The counter's law along a chain: the last row's `REAL_COUNT` is at most the starting value plus
the number of further rows, because every `IS_REAL` is at most `1`. -/
theorem last_count_le (rows : List Assignment) :
    ∀ (a : Assignment) (n : ℤ), List.IsChain LinkStep (a :: rows) →
      (∀ x ∈ (a :: rows), x IS_REAL * (x IS_REAL - 1) = 0) →
      a REAL_COUNT ≤ n →
      ∀ z, (a :: rows).getLast? = some z → z REAL_COUNT ≤ n + (rows.length : ℤ) := by
  induction rows with
  | nil =>
    intro a n _ _ hstart z hz
    simp only [List.getLast?_singleton, Option.some.injEq] at hz
    subst hz; simpa using hstart
  | cons b rest ih =>
    intro a n hch hbool hstart z hz
    have hst : LinkStep a b := (List.isChain_cons_cons.mp hch).1
    have hch' : List.IsChain LinkStep (b :: rest) := (List.isChain_cons_cons.mp hch).2
    have hb : b IS_REAL * (b IS_REAL - 1) = 0 := hbool b (by simp)
    have hb1 : b IS_REAL ≤ 1 := by
      rcases mul_eq_zero.mp hb with h0 | h1 <;> omega
    have hstart' : b REAL_COUNT ≤ n + 1 := by rw [hst.count]; linarith
    have hz' : (b :: rest).getLast? = some z := by simpa using hz
    have := ih b (n + 1) hch' (fun x hx => hbool x (by simp [hx])) hstart' z hz'
    simp only [List.length_cons]
    push_cast
    linarith

/-- ⚑⚑ **DERIVED FACT 4 — THE PUBLISHED SEGMENT LENGTH IS PAID FOR IN ROWS.** `PI_SEG_LEN` is the
last row's `REAL_COUNT`, which accumulates `IS_REAL` over rows that are `0/1`-pinned — so a prover
publishing `PI_SEG_LEN = n` has committed a trace with at least `n` rows.

⚑ **This is the tooth `LightClientMinaAir` could not have.** There `SEG_LEN` is a free witness column
in a SINGLE-ROW descriptor, constrained only into `[1, 2^24]`, and `minaLcAir_no_forgery` takes
`a SEG_LEN = u.blocks.length` as a HYPOTHESIS. Here it is a theorem about the committed trace. -/
theorem link_seg_len_counts_the_real_rows {rows : List Assignment} {pub : Assignment}
    (h : linkShapeAccepts rows pub) : pub PI_SEG_LEN ≤ (rows.length : ℤ) := by
  obtain ⟨hne, _, hbool, hch, hfst, hlst⟩ := h
  match rows, hne with
  | a :: rest, _ =>
    have hf : LinkFirst a pub := hfst a rfl
    have ha : a IS_REAL * (a IS_REAL - 1) = 0 := hbool a (by simp)
    have ha1 : a REAL_COUNT ≤ 1 := by
      rw [hf.count]; rcases mul_eq_zero.mp ha with h0 | h1 <;> omega
    obtain ⟨z, hz⟩ : ∃ z, (a :: rest).getLast? = some z :=
      ⟨(a :: rest).getLast (by simp), by simp [List.getLast?_eq_getLast]⟩
    have hle := last_count_le rest a 1 hch hbool ha1 z hz
    have hpin := (hlst z hz).segLen
    rw [← hpin]
    simp only [List.length_cons]
    push_cast
    linarith

/-! ## §8 — ⚑ THE REFINEMENT: acceptance + the NAMED residual ⟹ `LightClientMina.ChainFrom`. -/

/-- ⚑ **THE PAYOFF, WITH ITS RESIDUAL IN THE STATEMENT.** Given a segment the emitted descriptor
accepts, an INJECTIVE nine-lane encoding of digests, the parent-encoding tie and — the wall —
`LinkHashResidual`, the exhibited segment IS `LightClientMina.ChainFrom` from the pinned anchor.

⚑ Read the hypotheses, not the conclusion. `hres` is the Poseidon-over-Pasta leg and it is TRUSTED.
What the DESCRIPTOR contributes is the `SegmentFrom` argument — the chaining and the heights — and
those are the only conjuncts a gate discharges. `hinj` is the `Faithful9` lane encoding's
injectivity, which the tree proves (`fieldToLanes9_injective`) rather than assumes. -/
theorem segmentFrom_refines_chainFrom (L : MinaLeaf) (enc : L.Digest → ℤ)
    (hinj : Function.Injective enc) :
    ∀ (blocks : List (MinaHeader L)) (rows : List Assignment) (prev : L.Digest) (ph : Nat),
      rows.length = blocks.length →
      (∀ i, (hi : i < rows.length) → (hb : i < blocks.length) →
        rows[i] HEIGHT = ((blocks[i]).height : ℤ)) →
      LinkParentEncoding L enc rows blocks →
      LinkHashResidual L enc rows blocks →
      SegmentFrom (enc prev) (ph : ℤ) rows →
      ChainFrom L prev ph blocks := by
  intro blocks
  induction blocks with
  | nil => intro _ _ _ _ _ _ _ _; trivial
  | cons b rest ih =>
    intro rows prev ph hlen hht hpar hres hseg
    match rows with
    | [] => simp at hlen
    | a :: rows' =>
      obtain ⟨hpv, hhv, hrec⟩ := hseg
      -- the head block's parent IS the running digest
      have hparHead : parentValue a = enc b.parent := hpar 0 (by simp) (by simp)
      have hpb : b.parent = prev := hinj (by rw [← hparHead, hpv])
      -- and its height is one above the running height
      have hhtHead : ((b.height : ℤ)) = (ph : ℤ) + 1 := by
        have h0 := hht 0 (by simp) (by simp)
        simp only [List.getElem_cons_zero] at h0
        rw [← h0, hhv]
      have hhtN : b.height = ph + 1 := by exact_mod_cast hhtHead
      refine ⟨hpb, hhtN, ?_⟩
      -- the running value becomes this block's OWN hash — the residual's one use
      have hown : ownHashValue a = enc (blockHash L b) := hres 0 (by simp) (by simp)
      have hheq : a HEIGHT = ((b.height : ℤ)) := by
        have h0 := hht 0 (by simp) (by simp); simpa using h0
      refine ih rows' (blockHash L b) b.height (by simpa using hlen)
        (fun i hi hb' => by
          have h := hht (i + 1) (by simpa using hi) (by simpa using hb')
          simp only [List.getElem_cons_succ] at h
          exact h)
        (fun i hi hb' => by
          have h := hpar (i + 1) (by simpa using hi) (by simpa using hb')
          simp only [List.getElem_cons_succ] at h
          exact h)
        (fun i hi hb' => by
          have h := hres (i + 1) (by simpa using hi) (by simpa using hb')
          simp only [List.getElem_cons_succ] at h
          exact h)
        ?_
      rw [← hown, ← hheq]
      exact hrec

/-- ⚑ **THE DESCRIPTOR-LEVEL FORM.** An accepted trace, at the pinned anchor, entails the Mina
light client's own `ChainFrom` — modulo `LinkHashResidual`, stated in the hypotheses where a reader
cannot miss it. -/
theorem link_refines_chainFrom (L : MinaLeaf) (ts : MinaTrustedState L)
    (rows : List Assignment) (pub : Assignment) (blocks : List (MinaHeader L))
    (enc : L.Digest → ℤ) (hinj : Function.Injective enc)
    (hlen : rows.length = blocks.length)
    (hanchorEnc : anchorValue pub = enc ts.anchorState)
    (hanchorH : pub PI_ANCHOR_H = (ts.anchorHeight : ℤ))
    (hht : ∀ i, (hi : i < rows.length) → (hb : i < blocks.length) →
      rows[i] HEIGHT = ((blocks[i]).height : ℤ))
    (hpar : LinkParentEncoding L enc rows blocks)
    (hres : LinkHashResidual L enc rows blocks)
    (hacc : linkShapeAccepts rows pub) :
    ChainFrom L ts.anchorState ts.anchorHeight blocks := by
  apply segmentFrom_refines_chainFrom L enc hinj blocks rows ts.anchorState ts.anchorHeight
    hlen hht hpar hres
  have := linkShapeAccepts_gives_SegmentFrom hacc
  rwa [hanchorEnc, hanchorH] at this


/-! ## §9 — ⚑ BOTH POLARITIES, EXHIBITED ON CONCRETE ROWS.

A refusal nothing witnesses is decoration. These are three-row segments on the REAL devnet genesis
anchor and the REAL block-539508 tip (the same two values `LightClientMinaAir` §7 pins against their
Base58Check decimals), accepted; and the same segment with ONE lane bent, refused. -/

/-- A row from its column values, index-ordered from `PARENT 0`. -/
def rowOf (vs : List ℤ) : Assignment := fun w => vs.getD w 0

/-- The two interior state hashes of the exhibited segment. Any canonical nonet does: what the
descriptor forces is that they CHAIN, not what they are — and that is exactly the residual. -/
def MID1_LANES : List ℤ := [11, 22, 33, 44, 55, 66, 77, 88, 99]
def MID2_LANES : List ℤ := [111, 222, 333, 444, 555, 666, 777, 888, 999]

/-- Three canonical body-hash nonets. ⚑ These are SHAPE witnesses: `linkShapeAccepts` is the
row-local predicate and says nothing about which `Fp` element a body hash is — the tie
`OWNHASH = Poseidon_salt(PARENT, BODYHASH)` lives in `seam_derives_the_own_hash`, off-row, and no
`decide` over three rows could witness it. Saying so here is the point. -/
def BODY0_LANES : List ℤ := [7, 14, 21, 28, 35, 42, 49, 56, 63]
def BODY1_LANES : List ℤ := [70, 140, 210, 280, 350, 420, 490, 560, 630]
def BODY2_LANES : List ℤ := [700, 1400, 2100, 2800, 3500, 4200, 4900, 5600, 6300]

/-- Row 0 — parent is the REAL devnet genesis anchor, height 1001, real; the nine attested-program
lanes are `dregg-pasta-fp-absorb::v1`'s fingerprint. -/
def hrow0 : Assignment :=
  rowOf (Dregg2.Circuit.Emit.LightClientMinaAir.GENESIS_ANCHOR_LANES ++ MID1_LANES
    ++ [1001, 1, 1, 1000] ++ BODY0_LANES ++ ABSORB_VK_LANES)

/-- Row 1 — parent is row 0's own hash. -/
def hrow1 : Assignment :=
  rowOf (MID1_LANES ++ MID2_LANES ++ [1002, 1, 2, 1000] ++ BODY1_LANES ++ ABSORB_VK_LANES)

/-- Row 2 — parent is row 1's own hash, own hash is the REAL devnet block-539508 tip. -/
def hrow2 : Assignment :=
  rowOf (MID2_LANES ++ Dregg2.Circuit.Emit.LightClientMinaAir.DEVNET_TIP_LANES
    ++ [1003, 1, 3, 1000] ++ BODY2_LANES ++ ABSORB_VK_LANES)

/-- The public inputs: the pinned anchor, the verified tip, the anchor height, and the segment
length THE TRACE PAYS FOR. -/
def honestPub : Assignment :=
  rowOf (Dregg2.Circuit.Emit.LightClientMinaAir.GENESIS_ANCHOR_LANES
    ++ Dregg2.Circuit.Emit.LightClientMinaAir.DEVNET_TIP_LANES ++ [1000, 3])

/-- The honest three-block exhibited segment. -/
def honestSegment : List Assignment := [hrow0, hrow1, hrow2]

theorem honest_step_01 : LinkStep hrow0 hrow1 :=
  { lanes := by decide, height := by decide, monotone := by decide, count := by decide }

theorem honest_step_12 : LinkStep hrow1 hrow2 :=
  { lanes := by decide, height := by decide, monotone := by decide, count := by decide }

theorem honest_first : LinkFirst hrow0 honestPub :=
  { anchor := by decide, anchorH := by decide, height := by decide, count := by decide }

theorem honest_last : LinkLast hrow2 honestPub :=
  { tip := by decide, segLen := by decide }

/-- ⚑ **ACCEPTED — a three-block anchored segment on REAL devnet lanes.** Every row canonical, every
`IS_REAL` boolean, both links exact, the anchor pinned, the tip pinned, and `PI_SEG_LEN = 3` paid for
by three rows. Without this the rung would be satisfied by a descriptor that refuses everything. -/
theorem honest_segment_accepted : linkShapeAccepts honestSegment honestPub where
  nonempty := by simp [honestSegment]
  canon := by
    intro a ha
    simp only [honestSegment, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl <;> exact ⟨by decide, by decide, by decide⟩
  isReal := by
    intro a ha
    simp only [honestSegment, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl <;> decide
  program := by
    intro a ha
    simp only [honestSegment, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl <;> decide
  steps := by
    refine List.isChain_cons_cons.mpr ⟨honest_step_01, ?_⟩
    exact List.isChain_cons_cons.mpr ⟨honest_step_12, List.isChain_singleton _⟩
  first := by
    intro a ha
    simp only [honestSegment, List.head?_cons, Option.some.injEq] at ha
    subst ha; exact honest_first
  last := by
    intro a ha
    simp only [honestSegment] at ha
    have h2 : a = hrow2 := by simpa using ha.symm
    subst h2; exact honest_last

/-- ⚑ **DERIVED FACT 4, ON THE WITNESS.** The accepted segment's published length is paid for in
rows — three claimed, three committed. -/
theorem honest_segment_pays_for_its_length : honestPub PI_SEG_LEN ≤ (honestSegment.length : ℤ) :=
  link_seg_len_counts_the_real_rows honest_segment_accepted

/-- ⚑ **THE BENT LANE.** Row 1's parent lane 0 is `12` where row 0's own-hash lane 0 is `11`. It is a
perfectly canonical lane (`12 < 2^29`), so every canonicality lookup still passes, every height still
ticks, and `IS_REAL`/`REAL_COUNT` are untouched. Only the linkage is broken. -/
def brokenRow1 : Assignment :=
  rowOf ((12 :: MID1_LANES.tail) ++ MID2_LANES ++ [1002, 1, 2, 1000] ++ BODY1_LANES
    ++ ABSORB_VK_LANES)

/-- The bent row is still a well-formed canonical row — so the refusal below is the LINKAGE gate's
and not the canonicality gate's. -/
theorem broken_row_is_still_canonical : RowCanon brokenRow1 := ⟨by decide, by decide, by decide⟩

/-- …and its height and counter are still exactly the honest row's, so nothing but the link differs. -/
theorem broken_row_differs_only_in_the_link :
    brokenRow1 HEIGHT = hrow1 HEIGHT ∧ brokenRow1 IS_REAL = hrow1 IS_REAL
      ∧ brokenRow1 REAL_COUNT = hrow1 REAL_COUNT
      ∧ brokenRow1 (PARENT 0) ≠ hrow0 (OWNHASH 0) := by
  refine ⟨by decide, by decide, by decide, by decide⟩

def brokenSegment : List Assignment := [hrow0, brokenRow1, hrow2]

/-- ⚑⚑ **REFUSED — THE MISMATCHED PARENT.** This is the forgery `LightClientMinaAir`'s witnessed
`LINK_OK = 1` waves through: a segment whose second block's `previousStateHash` is NOT the first
block's state hash. The bent lane is canonical, so the canonicality rung does not refuse it; the
lane-continuity window gate does. -/
theorem broken_link_refused : ¬ linkShapeAccepts brokenSegment honestPub := by
  intro h
  have hst : LinkStep hrow0 brokenRow1 := (List.isChain_cons_cons.mp h.steps).1
  have := hst.lanes 0 (by decide)
  revert this
  decide

/-- ⚑⚑ **OLD ADMITS, NEW REJECTS — the rung as one theorem.** The bent segment satisfies everything
the PRE-RUNG descriptor could see about linkage: its rows are canonical, its heights are contiguous,
its counter is right, and `LINK_OK` is a bit a prover sets to `1`. `linkShapeAccepts` refuses it.
Nothing about the trace changed; the carrier stopped being a bit somebody wrote down. -/
theorem broken_link_old_admits_new_rejects :
    (RowCanon hrow0 ∧ RowCanon brokenRow1 ∧ RowCanon hrow2)
      ∧ brokenRow1 HEIGHT = hrow0 HEIGHT + 1
      ∧ ¬ linkShapeAccepts brokenSegment honestPub :=
  ⟨⟨⟨by decide, by decide, by decide⟩, broken_row_is_still_canonical,
     ⟨by decide, by decide, by decide⟩⟩,
   by decide, broken_link_refused⟩

/-- ⚑ **REFUSED — THE FREE DEPTH.** The same three exhibited rows, but the published `PI_SEG_LEN`
claims 290 (mainnet Samasika `k`). `link_seg_len_counts_the_real_rows` refuses it: 290 rows were not
committed. ⚠ This is the shape `LightClientMinaAir` CANNOT refuse — there `SEG_LEN` is a free witness
column in a single-row descriptor and 290 is as cheap to write as 3. -/
def liarPub : Assignment :=
  rowOf (Dregg2.Circuit.Emit.LightClientMinaAir.GENESIS_ANCHOR_LANES
    ++ Dregg2.Circuit.Emit.LightClientMinaAir.DEVNET_TIP_LANES ++ [1000, 290])

theorem short_segment_refused : ¬ linkShapeAccepts honestSegment liarPub := by
  intro h
  have hle := link_seg_len_counts_the_real_rows h
  have : liarPub PI_SEG_LEN = 290 := by decide
  rw [this] at hle
  simp only [honestSegment, List.length_cons, List.length_nil] at hle
  norm_num at hle

/-! ### §9a — ⚑⚑ THE SEAM'S OWN POLARITY, and the falsifier is checked for MOVING. -/

/-- ⚑ **THE ROW THAT ATTESTS A PROGRAM NOBODY PINNED.** Row 0 with `HASH_VK` lane 0 moved by one —
`446814635 → 446814636`. Three things about this forgery, each of which a sibling lane's falsifier
got wrong on a measured occasion:

* it moves a **NON-ZERO** value **to** a non-zero value, so it is not the zero-into-zero mutation
  `decide` cheerfully proves is not a tamper;
* it stays **INSIDE the 29-bit lookup**, so a range gate cannot be what refuses it;
* it changes **nothing else** — same parent, same own hash, same body hash, same height, same
  `IS_REAL`, same counter — so the refusal cannot come from any pre-existing gate. -/
def forgedProgramRow : Assignment :=
  rowOf (Dregg2.Circuit.Emit.LightClientMinaAir.GENESIS_ANCHOR_LANES ++ MID1_LANES
    ++ [1001, 1, 1, 1000] ++ BODY0_LANES ++ (446814636 :: ABSORB_VK_LANES.tail))

/-- ⚑ **THE FALSIFIER MOVES, AND IT MOVES THE RIGHT THING.** Checked, not asserted. -/
theorem forged_program_falsifier_moves :
    forgedProgramRow (HASH_VK 0) ≠ hrow0 (HASH_VK 0)
      ∧ forgedProgramRow (HASH_VK 0) ≠ 0
      ∧ hrow0 (HASH_VK 0) ≠ 0
      ∧ forgedProgramRow (HASH_VK 0) < 2 ^ MINA_LANE_BITS
      ∧ (∀ j, j < STATE_LIMBS → forgedProgramRow (PARENT j) = hrow0 (PARENT j))
      ∧ (∀ j, j < STATE_LIMBS → forgedProgramRow (OWNHASH j) = hrow0 (OWNHASH j))
      ∧ (∀ j, j < STATE_LIMBS → forgedProgramRow (BODYHASH j) = hrow0 (BODYHASH j))
      ∧ forgedProgramRow HEIGHT = hrow0 HEIGHT
      ∧ forgedProgramRow IS_REAL = hrow0 IS_REAL
      ∧ forgedProgramRow REAL_COUNT = hrow0 REAL_COUNT := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
          by decide, by decide, by decide⟩

/-- …and it is a perfectly canonical row, so the twenty-seven canonicality lookups are not what
objects. -/
theorem forged_program_row_is_still_canonical : RowCanon forgedProgramRow :=
  ⟨by decide, by decide, by decide⟩

/-- ⚑ ACCEPT side: the honest row's nine lanes ARE `dregg-pasta-fp-absorb::v1`'s fingerprint. -/
theorem honest_row_attests_the_pinned_program : hashVkRead hrow0 = ABSORB_VK_LANES := by decide

/-- ⚑ REFUSE side, at the lane vector the seam compares. -/
theorem forged_row_attests_a_different_program :
    hashVkRead forgedProgramRow ≠ ABSORB_VK_LANES := by decide

def forgedProgramSegment : List Assignment := [forgedProgramRow, hrow1, hrow2]

/-- ⚑⚑ **REFUSED — AND THE REFUSING GATE IS NAMED.** The forged segment satisfies every conjunct
`linkShapeAccepts` had before 2026-08-06: its rows are canonical, its `IS_REAL` bits are boolean,
its two links are exact, its first row is anchored and its last row is pinned to the tip and to the
counted length. The conjunct it fails is `program` — the seam's `vkPin` congruence — and the proof
below goes through that field and no other. -/
theorem forged_program_segment_refused :
    ¬ linkShapeAccepts forgedProgramSegment honestPub := by
  intro h
  exact forged_row_attests_a_different_program
    (h.program forgedProgramRow (by simp [forgedProgramSegment]))

/-- ⚑ **OLD ADMITS, NEW REJECTS — for the state-hash seam.** Every shape conjunct that existed
before the seam holds of the forged segment; the pre-seam predicate accepted it. -/
theorem forged_program_old_admits_new_rejects :
    (RowCanon forgedProgramRow ∧ RowCanon hrow1 ∧ RowCanon hrow2)
      ∧ LinkStep forgedProgramRow hrow1
      ∧ LinkFirst forgedProgramRow honestPub
      ∧ ¬ linkShapeAccepts forgedProgramSegment honestPub :=
  ⟨⟨forged_program_row_is_still_canonical, ⟨by decide, by decide, by decide⟩,
    ⟨by decide, by decide, by decide⟩⟩,
   { lanes := by decide, height := by decide, monotone := by decide, count := by decide },
   { anchor := by decide, anchorH := by decide, height := by decide, count := by decide },
   forged_program_segment_refused⟩

/-- ⚑ **THE POLARITY TRIPLE, AS ONE STATEMENT.** The emitted logic DISCRIMINATES: it accepts an
honest anchored segment on real devnet lanes and refuses the mismatched parent, the free depth, and
— new on 2026-08-06 — the row that recursion-binds to a program nobody pinned. -/
theorem mina_link_discriminates :
    linkShapeAccepts honestSegment honestPub
      ∧ ¬ linkShapeAccepts brokenSegment honestPub
      ∧ ¬ linkShapeAccepts honestSegment liarPub
      ∧ ¬ linkShapeAccepts forgedProgramSegment honestPub :=
  ⟨honest_segment_accepted, broken_link_refused, short_segment_refused,
   forged_program_segment_refused⟩

/-! ## §10 — axiom hygiene. Every asserted fact above is a NAMED THEOREM; this file contains no
`#guard` (`metatheory/docs/GUARD-DISCIPLINE.md`). -/

#assert_axioms minaLinkAir_mainRailOk
#assert_axioms minaLinkAir_pinsFit
#assert_axioms minaLinkAir_leg_count
#assert_axioms minaLinkAir_window_selectors
#assert_axioms minaLinkAir_limbs_shape
#assert_axioms minaLinkDesc_constraint_count
#assert_axioms minaLinkDesc_lane_continuity_gates
#assert_axioms minaLinkDesc_canon_lookups
#assert_axioms minaLinkDesc_pins
#assert_axioms minaLink_layout_wellformed
#assert_axioms minaLink_products_are_only_the_real_bit
#assert_axioms minaLink_no_two_column_product
#assert_axioms emitted_transition_means_body
#assert_axioms emitted_all_means_body
#assert_axioms limbsInRange_below_field
#assert_axioms laneCanon_lane_below_field
#assert_axioms link_lane_equality_is_exact
#assert_axioms step_chains_values
#assert_axioms first_pins_anchor_value
#assert_axioms last_pins_tip_value
#assert_axioms segmentFrom_of_isChain
#assert_axioms linkShapeAccepts_gives_SegmentFrom
#assert_axioms link_heights_are_contiguous
#assert_axioms last_count_le
#assert_axioms link_seg_len_counts_the_real_rows
#assert_axioms segmentFrom_refines_chainFrom
#assert_axioms link_refines_chainFrom
#assert_axioms honest_segment_accepted
#assert_axioms honest_segment_pays_for_its_length
#assert_axioms broken_row_is_still_canonical
#assert_axioms broken_link_refused
#assert_axioms broken_link_old_admits_new_rejects
#assert_axioms short_segment_refused
#assert_axioms mina_link_discriminates
#assert_axioms minaLink_seam_shape
#assert_axioms minaLinkDesc_state_hash_seam
#assert_axioms minaLink_commit_is_salt_then_the_row
#assert_axioms minaLink_has_two_pinned_seams
#assert_axioms minaLinkDesc_body_chain_seam
#assert_axioms minaLink_body_chain_seam_binds_the_stream
#assert_axioms the_two_seams_name_two_different_salts
#assert_axioms minaLink_proofBinds
#assert_axioms laneVal_map
#assert_axioms zeroLanes_one_exact
#assert_axioms seam_forces_the_pinned_program
#assert_axioms seam_derives_the_own_hash
#assert_axioms linkHashResidual_of_seam
#assert_axioms forged_program_falsifier_moves
#assert_axioms forged_program_row_is_still_canonical
#assert_axioms honest_row_attests_the_pinned_program
#assert_axioms forged_row_attests_a_different_program
#assert_axioms forged_program_segment_refused
#assert_axioms forged_program_old_admits_new_rejects

-- ⚑ THE ONE COMPILED FACT, CONFESSED. `saltProtoState` is a Kimchi Poseidon permutation and the
-- kernel cannot reduce one (47.6 GB / 68 min, measured in this tree), so the salt-lane
-- decomposition is checked by the compiled evaluator and says so.
#assert_compiled mina_link_salt_lanes_are_the_salt
#assert_compiled mina_link_body_salt_lanes_are_the_body_salt

end Dregg2.Circuit.Emit.LightClientMinaLinkAir
