/-
# Dregg2.Circuit.Emit.EffectVmEmitRotationV3 — THE FULL-COHORT REGEN at the rotated block
(R = 24, CONFIRMED), staged.

`docs/ROTATION-CUTOVER.md` §5 item 1: the staged probes pin the rotated SHAPE; the 26
per-effect descriptors still emit against the 186/14 layout. THIS module re-emits EVERY
cohort member against the rotated 25+…-limb state block — as ONE parametric transformation
(`rotateV3`), so the soundness keystones lift ONCE, for all 26, not per-descriptor:

  * **§1 the appended geometry** — each rotated descriptor carries, PAST its v1 layout
    (every v1 column index, constraint, and theorem untouched): a rotated BEFORE block at
    `d.traceWidth` (37 absorption-ordered limbs · iroot · state_commit · 12 chain carriers
    = 51 columns, the R=24 register geometry PLUS the `commitments_root` + `lifecycle_disc` +
    `perms_digest` + `vk_digest` + `mode` + `fields_root` limbs), a rotated AFTER block at `d.traceWidth + 91`, and the
    WIDENED-CAVEAT region at `d.traceWidth + 182` (29-felt manifest · 9 chain carriers · caveat
    commit = 39 columns). Width: `+141`.
  * **§2 col-chained sites** — the chained absorptions reference their carrier COLUMNS
    (`.col`), never `.digest k`, so the site group is POSITION-INDEPENDENT (appendable
    after any descriptor's own sites with no index shift) and graduates to the SAME wire
    bytes as the digest-chained probe (`#guard` byte-identity tripwire below;
    `HashInput.toExpr` resolves `.digest k` to site `k`'s `digestCol`).
  * **§3 the welds** — the rotated blocks are tied to the v1 state blocks where the datum
    EXISTS in the v1 layout (per side): `r0 ↔ BALANCE_LO` and `r1 ↔ NONCE` (the CONFIRMED
    balance/nonce → r0/r1 assignment, ember 2026-06-12), `r2 ↔ BALANCE_HI` (the high
    limb's STAGED home — the single-felt-vs-two-limb encoding refinement is the §5.2
    flag-day line, HORIZONLOG'd), `r3..r10 ↔ fields[0..7]`, `CAP_ROOT ↔ CAP_ROOT`.
    The remaining limbs (cells_root · nullifier/heap roots · lifecycle · epoch ·
    committed_height · iroot · r11..r23) are WITNESS-CARRIED, commitment-bound limbs:
    their per-turn producers are `turn/src/rotation_witness.rs` (cells_root + iroot +
    lifecycle/epoch carriers — ROTATION-CUTOVER §5 items 3-5); nothing here claims they
    are v1-column-derived.
  * **§4 the keystones, ONCE, parametric in `d`** — `go_colOnly_mem` (col-only sites'
    equations survive ANY walk position), `rotV3SitesAt_pin`/`caveatV3SitesAt_pin` (the
    appended chains pin `wireCommitR`/`caveatCommit` of the row's OWN limbs, parametric
    in the block base), `rotateV3_satisfiedVm_v1` (the rotated descriptor still forces
    the FULL v1 denotation — every existing per-effect faithfulness/anti-ghost theorem
    composes unchanged), `graduable_rotateV3` (graduation side conditions lift),
    `rotV3_pins` / `rotV3_publishes` (4 appended PI pins: rotated OLD commit on the
    first row, rotated NEW commit + height + caveat commit on the last), and THE
    END-TO-END `rotV3_binds_published`: two `Satisfied2` witnesses of ANY cohort member's
    rotated form publishing the same rotated commits agree on the WHOLE before block, the
    WHOLE after block, both iroots, the published height, AND the WHOLE caveat manifest —
    under the ONE `Poseidon2SpongeCR` floor, via the parametric `wireCommitR_binds` /
    `caveatCommit_binds`. One theorem, 26 descriptors.
  * **§5 the v3 registry** — `v3Registry`: all 36 cohort members rotated. The 28 `v2Registry`
    members (the 17 graduated cohort + attenuate WITH its phase-B map ops/submask lookup + revoke
    WITH its cap-crown map ops + CUSTOM WITH its recursive-proof-binding op + the dynamic setField
    WITH its mem ops + the 8 per-slot setFields)
    PLUS the 8 LIVE-path effects
    the v2 graduation never covered but the v1 wire DID (STEP 1 / ROTATION-CUTOVER §2c cohort
    widening): grantCap (the bare unattenuated cap-root grant), makeSovereign, createCell,
    factory, spawn, receiptArchive, cellUnseal, emitEvent — each the graduated RUNTIME row
    lifted through the SAME `rotateV3`, so the soundness keystones apply unchanged. Keys
    suffixed `R24`. Driver: `EmitRotationV3.lean` (the Rust staged twin is
    `circuit/descriptors/rotation-v3-staged-registry.tsv`, sha-pinned).
    HONEST RESIDUE: **EMPTY** — every LIVE selector now has a rotated descriptor. `Custom` (8) was
    the last; it GRADUATED via the new accumulator / recursive-proof-binding constraint kind
    (`DescriptorIR2.ProofBind`): the rotated `customV3` carries the `proofBind` op that ties the
    row's `custom_proof_commitment` to a VERIFYING external sub-proof of the named recursion engine
    (the row commits to the verification, rather than trusting it), PLUS (the VK epoch) the eight
    `customPiExposure` PI pins that PUBLISH the bound `(commit, vk)` columns so the per-turn FOLD
    connects the custom sub-proof leaf — the binding is at the fold, not a row gate. (`RevokeCapability` (24)
    GRADUATED via the cap-crown `revokeCapabilityVmDescriptor2` — held-membership map-read +
    ZERO-value remove-write — rotated as `revokeCapabilityV3`.)

## Honest boundary notes (do NOT over-read)

  * STAGED beside v1/v2: a new registry constant, NO VK bump, nothing on the live wire.
    The v1 path stays byte-identical; the v2 registry is untouched.
  * The appended blocks are ADDITIVE: the v1 state commitment (GROUP-4) still binds
    everything it bound before (including `BALANCE_HI`, wherever the flip's encoding
    decision lands); the rotated commitment binds the NEW block beside it. The flip
    (§3 steps 1-6 of ROTATION-CUTOVER.md) replaces; this stages.
  * `attenuateV3`/`setFieldDynV3` carry their v2 extras verbatim; their §7/§8 theorems
    re-state through `memOpsOf`/membership transport (`setFieldDynV3_readback_genuine`,
    `attenuateV3_non_amp` below).

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; crypto only as the named
`Poseidon2SpongeCR` hypothesis.
-/
import Dregg2.Circuit.Emit.EffectVmEmitRotationCaveat
-- The LIVE-PATH (non-v2-cohort) effects whose wire descriptors the flag-day must keep
-- reachable once v1 dies (ROTATION-CUTOVER §2c cohort boundary). Each is the GRADUATED
-- RUNTIME row (frozen-frame / passthrough + nonce-tick), lifted through the SAME `rotateV3`.
import Dregg2.Circuit.Emit.EffectVmEmitMakeSovereign
import Dregg2.Circuit.Emit.EffectVmEmitCreateCell
import Dregg2.Circuit.Emit.EffectVmEmitCreateCellFromFactory
import Dregg2.Circuit.Emit.EffectVmEmitSpawn
import Dregg2.Circuit.Emit.EffectVmEmitReceiptArchive
import Dregg2.Circuit.Emit.EffectVmEmitCellUnseal
import Dregg2.Circuit.Emit.EffectVmEmitEmitEvent

namespace Dregg2.Circuit.Emit.EffectVmEmitRotationV3

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmitV2
open Dregg2.Circuit.Emit.EffectVmEmitRotationR
open Dregg2.Circuit.Emit.EffectVmEmitRotationCaveat
  (RotCaveatManifest caveatCommit caveatCommit_binds)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Crypto
open Dregg2.Substrate.Heap (refSponge)

set_option linter.unusedVariables false
set_option autoImplicit false

/-! ## §1 — the appended geometry (R = 24, offsets relative to a block base). -/

-- ── THE MODE/FIELDS-ROOT FLAG-DAY (NUM_PRE_LIMBS 35→37) — WAVE 3 (the mover tail) ────────────────
-- On TOP of the perms/VK flag-day (limbs 33,34), the deployed rotated block now carries TWO more
-- dedicated authority sub-limbs as the NEW LAST pre-iroot limbs: the committed cell `MODE` byte limb
-- at in-block offset 35 (`B_MODE`, the `Hosted=0 / Sovereign=1` byte that
-- `compute_authority_digest_felt` folds — `rotation_witness.rs::mode_felt`) and the committed
-- `fields_root` digest limb at offset 36 (`B_FIELDS_ROOT`, the overflow named-field map root the same
-- digest folds — `hash_bytes(cell.state.fields_root)`). Committed BESIDE the opaque `record_digest`
-- (r23, limb 24). Every offset 0..34 stays STABLE (`B_LIFECYCLE = 29`, `B_RECORD_DIGEST = 24`,
-- `B_CAP_ROOT = 25`, `B_COMMITMENTS_ROOT = 27`, `B_COMMITTED_HEIGHT = 31`, `B_DISC = 32`,
-- `B_PERMS = 33`, `B_VK = 34` UNCHANGED); only the iroot/state_commit/chain carriers shift +2, the
-- block span 49→51, and the post-block (`+49`→`+51`) offsets follow. The 37-limb pre-iroot list chains
-- as: a 4-wide head (limbs 0..3) + ELEVEN 3-wide body groups (limbs 4..36, exactly 33 = 11×3 limbs,
-- so NO arity-2 leftover — the WAVE-2 vk singleton is absorbed into the eleventh 3-wide group) + the
-- iroot ALONE last. The site count stays 13 (12 chain carriers + the state-commit carrier). The
-- `chunk31` (`EffectVmEmitRotationR`) is length-generic, so the chained-commitment binding lifts
-- unchanged; only the literal site walk + offsets move here. This commits the mode + fields_root
-- authority shape so the per-effect movers go LIVE: makeSovereign FORCES the AFTER mode limb to
-- `Sovereign(1)` as a CONSTANT (the disc shape, NO trusted post-cell); setFieldDyn / refusal WELD the
-- AFTER fields_root sub-limb to the declared post-`fields_root` param column (the perms/VK weld shape,
-- declared-param anchored).

/-- The per-block span: 67 pre-iroot limbs + iroot + state_commit + 22 chain carriers (v10:
NUM_PRE_LIMBS 37→67 — the faithful 8-felt completion grows the pre-iroot vector by 30 new limbs at
offsets 37..66, giving the five remaining 8-felt components (cap_root · heap_root · perms · vk ·
fields_root) their 7 extra limbs each, beside the 5 repurposed headroom limbs 19..23). -/
def B_SPAN : Nat := 91
/-- lifecycle-disc offset inside a block (limb 32 — the WAVE-1 flag-day committed discriminant limb,
committed BESIDE the opaque `lifecycle_felt` at 29; UNCHANGED by the perms/VK + mode/fields-root flag-days). -/
def B_DISC : Nat := 32
/-- committed-permissions digest offset inside a block (limb 33 — the WAVE-2 flag-day committed
perms-digest limb; the deployed `params[0]` felt for a setPermissions row, `= permsHash[0]`). -/
def B_PERMS : Nat := 33
/-- committed-verification-key digest offset inside a block (limb 34 — the WAVE-2 flag-day committed
vk-digest limb; the deployed `params[0]` felt for a setVK row, `= vkHash[0]`). -/
def B_VK : Nat := 34
/-- committed cell-MODE offset inside a block (limb 35 — the WAVE-3 flag-day committed mode byte,
`Hosted=0 / Sovereign=1`; the makeSovereign CONSTANT-force limb). -/
def B_MODE : Nat := 35
/-- committed `fields_root` digest offset inside a block (limb 36 — the WAVE-3 flag-day committed
overflow named-field map root; the setFieldDyn / refusal declared-param weld limb). -/
def B_FIELDS_ROOT : Nat := 36
/-- iroot offset inside a block (limb 67, shifted +30 by the v10 faithful-8-felt completion limbs). -/
def B_IROOT : Nat := 67
/-- state-commit offset inside a block (carrier `B_SPAN - 1`). -/
def B_STATE_COMMIT : Nat := 68
/-- committed-height offset inside a block (limb 31, after the `commitments_root` shift — UNCHANGED
by the disc / perms-VK flag-days, which append PAST it). -/
def B_COMMITTED_HEIGHT : Nat := 31
/-- cap-root offset inside a block (unshifted — `commitments_root` rides AFTER nullifier_root). -/
def B_CAP_ROOT : Nat := 25
/-- nullifier-root offset inside a block (unshifted, limb 26). -/
def B_NULLIFIER_ROOT_OFF : Nat := 26
/-- commitments-root offset inside a block (limb 27 — the flag-day new committed shielded-set root). -/
def B_COMMITMENTS_ROOT : Nat := 27
/-- delegation-epoch offset inside a block (limb 30 — the committed per-cell `delegation_epoch`,
`commitment.rs::compute_rotated_pre_limbs` `pre[30]`; absorption order cells_root · r0..r23 · cap_root ·
nullifier_root · commitments_root · heap_root · lifecycle · **epoch** · committed_height). The forced
limb for `revokeDelegation`'s parent-epoch BUMP (the §14.EPOCH write-gate). -/
def B_EPOCH : Nat := 30
/-- The caveat region span: 29 manifest felts + 9 chain carriers + 1 commit. -/
def C_SPAN : Nat := 39
/-- caveat-commit offset inside the caveat region. -/
def C_COMMIT : Nat := 38
/-- The whole appendix width: two rotated blocks + the caveat region (v10: 2·91 + 39 = 221). -/
def APPENDIX_SPAN : Nat := 221

-- The map-root offsets ride past the R=24 probe's named columns (cap_root at probe `capRootCol 24`);
-- the `commitments_root` limb is the +1 over the bare R=24 register shape.
#guard B_CAP_ROOT == capRootCol 24
#guard B_COMMITMENTS_ROOT == B_NULLIFIER_ROOT_OFF + 1
#guard B_DISC == 32                  -- the WAVE-1 disc limb (after committed_height at 31)
#guard B_PERMS == 33                 -- WAVE-2 committed perms-digest limb
#guard B_VK == 34                    -- WAVE-2 committed vk-digest limb
#guard B_MODE == 35                  -- WAVE-3 committed mode byte limb
#guard B_FIELDS_ROOT == 36           -- WAVE-3 committed fields_root digest limb
#guard B_IROOT == 67                 -- 67 pre-iroot limbs (v10), then iroot
#guard B_STATE_COMMIT == B_IROOT + 1
#guard B_COMMITTED_HEIGHT == 31      -- last SCALAR pre-iroot limb (disc/perms/vk/mode/fields-root ride past it)
#guard B_SPAN == B_IROOT + 24        -- 67 pre-iroot + iroot + state_commit + 22 chain carriers = 91 (v10)
#guard APPENDIX_SPAN == 2 * B_SPAN + C_SPAN

/-- The pre-iroot limb list of a block at `base` (v10: 67 limbs, absorption order: cells_root ·
r0..r23 · cap_root · nullifier_root · commitments_root · heap_root · lifecycle · epoch ·
committed height · lifecycle_disc · perms_digest · vk_digest · **mode** · **fields_root** · then the
30 NEW faithful-8-felt completion limbs 37..66 — the 7 extra felts each for cap_root · heap_root ·
perms · vk · fields_root, plus the 5 repurposed headroom limbs 19..23). Literal, so every positional
fact is `rfl`. -/
def preLimbsAt (base : Nat) (a : Assignment) : List ℤ :=
  [ a (base + 0), a (base + 1), a (base + 2), a (base + 3), a (base + 4), a (base + 5)
  , a (base + 6), a (base + 7), a (base + 8), a (base + 9), a (base + 10), a (base + 11)
  , a (base + 12), a (base + 13), a (base + 14), a (base + 15), a (base + 16), a (base + 17)
  , a (base + 18), a (base + 19), a (base + 20), a (base + 21), a (base + 22), a (base + 23)
  , a (base + 24), a (base + 25), a (base + 26), a (base + 27), a (base + 28), a (base + 29)
  , a (base + 30), a (base + 31), a (base + 32), a (base + 33), a (base + 34), a (base + 35)
  , a (base + 36), a (base + 37), a (base + 38), a (base + 39), a (base + 40), a (base + 41)
  , a (base + 42), a (base + 43), a (base + 44), a (base + 45), a (base + 46), a (base + 47)
  , a (base + 48), a (base + 49), a (base + 50), a (base + 51), a (base + 52), a (base + 53)
  , a (base + 54), a (base + 55), a (base + 56), a (base + 57), a (base + 58), a (base + 59)
  , a (base + 60), a (base + 61), a (base + 62), a (base + 63), a (base + 64), a (base + 65)
  , a (base + 66) ]

theorem preLimbsAt_length (base : Nat) (a : Assignment) :
    (preLimbsAt base a).length = 67 := rfl

/-- Read the caveat manifest off a row at region base `base` (positional, 29 felts). -/
def manifestAt (base : Nat) (a : Assignment) : RotCaveatManifest :=
  { count := a (base + 0)
  , e0 := ⟨a (base + 1), a (base + 2), a (base + 3), a (base + 4), a (base + 5),
           a (base + 6), a (base + 7)⟩
  , e1 := ⟨a (base + 8), a (base + 9), a (base + 10), a (base + 11), a (base + 12),
           a (base + 13), a (base + 14)⟩
  , e2 := ⟨a (base + 15), a (base + 16), a (base + 17), a (base + 18), a (base + 19),
           a (base + 20), a (base + 21)⟩
  , e3 := ⟨a (base + 22), a (base + 23), a (base + 24), a (base + 25), a (base + 26),
           a (base + 27), a (base + 28)⟩ }

/-! ## §2 — the col-chained sites (position-independent; graduate to the probe's bytes). -/

/-- The 23 chained absorption sites of a rotated block at `base` (v10): the 4-wide head, TWENTY-ONE
3-wide body groups (limbs 4..66 — the 63-limb body `[4..66]` is exactly twenty-one 3-wide groups, NO
arity-2 leftover), then the iroot ALONE last onto the state-commit carrier. Chaining is by CARRIER
COLUMNS (`.col`), which graduates to the SAME wire bytes as `.digest` chaining while keeping the group
position-independent. Chain carriers ride `base + 69 .. base + 90` (22 carriers); the state-commit
carrier is `base + 68`. -/
def rotV3SitesAt (base : Nat) : List VmHashSite :=
  [ ⟨base + 69, [.col (base + 0), .col (base + 1), .col (base + 2), .col (base + 3)], 4⟩
  , ⟨base + 70, [.col (base + 69), .col (base + 4), .col (base + 5), .col (base + 6)], 4⟩
  , ⟨base + 71, [.col (base + 70), .col (base + 7), .col (base + 8), .col (base + 9)], 4⟩
  , ⟨base + 72, [.col (base + 71), .col (base + 10), .col (base + 11), .col (base + 12)], 4⟩
  , ⟨base + 73, [.col (base + 72), .col (base + 13), .col (base + 14), .col (base + 15)], 4⟩
  , ⟨base + 74, [.col (base + 73), .col (base + 16), .col (base + 17), .col (base + 18)], 4⟩
  , ⟨base + 75, [.col (base + 74), .col (base + 19), .col (base + 20), .col (base + 21)], 4⟩
  , ⟨base + 76, [.col (base + 75), .col (base + 22), .col (base + 23), .col (base + 24)], 4⟩
  , ⟨base + 77, [.col (base + 76), .col (base + 25), .col (base + 26), .col (base + 27)], 4⟩
  , ⟨base + 78, [.col (base + 77), .col (base + 28), .col (base + 29), .col (base + 30)], 4⟩
  , ⟨base + 79, [.col (base + 78), .col (base + 31), .col (base + 32), .col (base + 33)], 4⟩
  , ⟨base + 80, [.col (base + 79), .col (base + 34), .col (base + 35), .col (base + 36)], 4⟩
  , ⟨base + 81, [.col (base + 80), .col (base + 37), .col (base + 38), .col (base + 39)], 4⟩
  , ⟨base + 82, [.col (base + 81), .col (base + 40), .col (base + 41), .col (base + 42)], 4⟩
  , ⟨base + 83, [.col (base + 82), .col (base + 43), .col (base + 44), .col (base + 45)], 4⟩
  , ⟨base + 84, [.col (base + 83), .col (base + 46), .col (base + 47), .col (base + 48)], 4⟩
  , ⟨base + 85, [.col (base + 84), .col (base + 49), .col (base + 50), .col (base + 51)], 4⟩
  , ⟨base + 86, [.col (base + 85), .col (base + 52), .col (base + 53), .col (base + 54)], 4⟩
  , ⟨base + 87, [.col (base + 86), .col (base + 55), .col (base + 56), .col (base + 57)], 4⟩
  , ⟨base + 88, [.col (base + 87), .col (base + 58), .col (base + 59), .col (base + 60)], 4⟩
  , ⟨base + 89, [.col (base + 88), .col (base + 61), .col (base + 62), .col (base + 63)], 4⟩
  , ⟨base + 90, [.col (base + 89), .col (base + 64), .col (base + 65), .col (base + 66)], 4⟩
  , ⟨base + 68, [.col (base + 90), .col (base + 67)], 2⟩ ]

/-- The 10 chained caveat sites at region base `base` (the `caveatSites` shape, positional):
4-wide head over `[count, e0.tag, e0.dom, e0.key]`, eight (carrier+3) body groups, the
(carrier+1) tail onto the caveat-commit carrier. -/
def caveatV3SitesAt (base : Nat) : List VmHashSite :=
  [ ⟨base + 29, [.col (base + 0), .col (base + 1), .col (base + 2), .col (base + 3)], 4⟩
  , ⟨base + 30, [.col (base + 29), .col (base + 4), .col (base + 5), .col (base + 6)], 4⟩
  , ⟨base + 31, [.col (base + 30), .col (base + 7), .col (base + 8), .col (base + 9)], 4⟩
  , ⟨base + 32, [.col (base + 31), .col (base + 10), .col (base + 11), .col (base + 12)], 4⟩
  , ⟨base + 33, [.col (base + 32), .col (base + 13), .col (base + 14), .col (base + 15)], 4⟩
  , ⟨base + 34, [.col (base + 33), .col (base + 16), .col (base + 17), .col (base + 18)], 4⟩
  , ⟨base + 35, [.col (base + 34), .col (base + 19), .col (base + 20), .col (base + 21)], 4⟩
  , ⟨base + 36, [.col (base + 35), .col (base + 22), .col (base + 23), .col (base + 24)], 4⟩
  , ⟨base + 37, [.col (base + 36), .col (base + 25), .col (base + 26), .col (base + 27)], 4⟩
  , ⟨base + 38, [.col (base + 37), .col (base + 28)], 2⟩ ]

/-- The whole appendix site group for a descriptor of width `w`. The AFTER block rides at
`w + B_SPAN` (= `w + 91`); the caveat region at `w + 2·B_SPAN` (= `w + 182`). -/
def rotV3Appendix (w : Nat) : List VmHashSite :=
  rotV3SitesAt w ++ rotV3SitesAt (w + 91) ++ caveatV3SitesAt (w + 182)

-- Arity discipline: every appendix site is arity 4 or 2 (the chip refuses 3) — checked at
-- a concrete base; the literal arities are base-independent.
#guard (rotV3Appendix 186).all fun s => s.arity == 4 || s.arity == 2
#guard (rotV3Appendix 186).length == 56   -- 23 (before) + 23 (after) + 10 (caveat)

-- **THE BYTE-IDENTITY TRIPWIRE** (v10 67-limb shape): the col-chained 23-site block at base 0
-- graduates to the EXACT wire JSON of its DIGEST-chained twin (the running accumulator referenced
-- as `.digest (k-1)` instead of `.col carrier`). `HashInput.toExpr` resolves `.digest k` to site
-- `k`'s `digestCol`, which IS the chain-carrier column the col-chained form names, so the two emit
-- byte-for-byte. This is the standalone analog of the old R=24-probe cross-check, at the deployed
-- 67-limb geometry (the R-register probe no longer matches the +30 faithful-8-felt completion limbs).
private def rotV3SitesDigestAt0 : List VmHashSite :=
  [ ⟨69, [.col 0, .col 1, .col 2, .col 3], 4⟩
  , ⟨70, [.digest 0, .col 4, .col 5, .col 6], 4⟩
  , ⟨71, [.digest 1, .col 7, .col 8, .col 9], 4⟩
  , ⟨72, [.digest 2, .col 10, .col 11, .col 12], 4⟩
  , ⟨73, [.digest 3, .col 13, .col 14, .col 15], 4⟩
  , ⟨74, [.digest 4, .col 16, .col 17, .col 18], 4⟩
  , ⟨75, [.digest 5, .col 19, .col 20, .col 21], 4⟩
  , ⟨76, [.digest 6, .col 22, .col 23, .col 24], 4⟩
  , ⟨77, [.digest 7, .col 25, .col 26, .col 27], 4⟩
  , ⟨78, [.digest 8, .col 28, .col 29, .col 30], 4⟩
  , ⟨79, [.digest 9, .col 31, .col 32, .col 33], 4⟩
  , ⟨80, [.digest 10, .col 34, .col 35, .col 36], 4⟩
  , ⟨81, [.digest 11, .col 37, .col 38, .col 39], 4⟩
  , ⟨82, [.digest 12, .col 40, .col 41, .col 42], 4⟩
  , ⟨83, [.digest 13, .col 43, .col 44, .col 45], 4⟩
  , ⟨84, [.digest 14, .col 46, .col 47, .col 48], 4⟩
  , ⟨85, [.digest 15, .col 49, .col 50, .col 51], 4⟩
  , ⟨86, [.digest 16, .col 52, .col 53, .col 54], 4⟩
  , ⟨87, [.digest 17, .col 55, .col 56, .col 57], 4⟩
  , ⟨88, [.digest 18, .col 58, .col 59, .col 60], 4⟩
  , ⟨89, [.digest 19, .col 61, .col 62, .col 63], 4⟩
  , ⟨90, [.digest 20, .col 64, .col 65, .col 66], 4⟩
  , ⟨68, [.digest 21, .col 67], 2⟩ ]

#guard emitVmJson2 (graduateV1
    { name := "dregg-effectvm-rotation-v3-commitments-tripwire"
    , traceWidth := B_SPAN
    , piCount := 2
    , constraints :=
        [ .piBinding .last B_STATE_COMMIT Dregg2.Circuit.Emit.EffectVmEmitRotation.PUB_COMMIT
        , .piBinding .last B_COMMITTED_HEIGHT
            Dregg2.Circuit.Emit.EffectVmEmitRotation.PUB_HEIGHT ]
    , hashSites := rotV3SitesAt 0
    , ranges := [] })
  == emitVmJson2 (graduateV1
    { name := "dregg-effectvm-rotation-v3-commitments-tripwire"
    , traceWidth := B_SPAN
    , piCount := 2
    , constraints :=
        [ .piBinding .last B_STATE_COMMIT Dregg2.Circuit.Emit.EffectVmEmitRotation.PUB_COMMIT
        , .piBinding .last B_COMMITTED_HEIGHT
            Dregg2.Circuit.Emit.EffectVmEmitRotation.PUB_HEIGHT ]
    , hashSites := rotV3SitesDigestAt0
    , ranges := [] })

/-! ## §3 — the welds and the transformation. -/

/-- The weld gate `loc a = loc b` (an equality as a vanishing polynomial). -/
def colEq (a b : Nat) : VmConstraint :=
  .gate (.add (.var a) (.mul (.const (-1)) (.var b)))

/-- The weld gate is a `.gate`; under the deployed `when_transition()` it binds on every row but the
last. On a TRANSITION row (`isLast = false`) it holds iff the welded columns are equal. (On the wrap
row it is vacuous — the faithful denotation; weld content is read at the active row.) -/
theorem colEq_holds_iff (env : VmRowEnv) (isFirst isLast : Bool) (a b : Nat)
    (hlast : isLast = false) :
    (colEq a b).holdsVm env isFirst isLast ↔ env.loc a = env.loc b := by
  subst hlast
  simp only [colEq, VmConstraint.holdsVm, EmittedExpr.eval]
  constructor <;> intro h <;> linarith

/-- The per-side welds: rotated block at `base` ↔ v1 state block at `stateBase`
(`STATE_BEFORE_BASE` or `STATE_AFTER_BASE`). r0 ↔ BALANCE_LO · r1 ↔ NONCE (the CONFIRMED
assignment) · r2 ↔ BALANCE_HI (staged home) · r3..r10 ↔ fields[0..7] · CAP_ROOT ↔ CAP_ROOT. -/
def weldsAt (base stateBase : Nat) : List VmConstraint :=
  [ colEq (base + 1) (stateBase + state.BALANCE_LO)
  , colEq (base + 2) (stateBase + state.NONCE)
  , colEq (base + 3) (stateBase + state.BALANCE_HI)
  , colEq (base + 4) (stateBase + state.FIELD_BASE)
  , colEq (base + 5) (stateBase + state.FIELD_BASE + 1)
  , colEq (base + 6) (stateBase + state.FIELD_BASE + 2)
  , colEq (base + 7) (stateBase + state.FIELD_BASE + 3)
  , colEq (base + 8) (stateBase + state.FIELD_BASE + 4)
  , colEq (base + 9) (stateBase + state.FIELD_BASE + 5)
  , colEq (base + 10) (stateBase + state.FIELD_BASE + 6)
  , colEq (base + 11) (stateBase + state.FIELD_BASE + 7)
  , colEq (base + B_CAP_ROOT) (stateBase + state.CAP_ROOT) ]

/-- **`weldsAtNoCapRoot`** — the per-side welds WITHOUT the `B_CAP_ROOT ↔ state.CAP_ROOT` weld. The rotated
cap-root limb (limb 25) is then WITNESS-CARRIED (note-spend-shaped, like the unwelded nullifier limb 26):
the cap-write `MapOp` drives it before≠after and it folds into the rotated commitment, while the v1-state
`cap_root` column (col 65/87) stays free to pass through continuously (`transition CAP_ROOT CAP_ROOT`
trivially holds when the prover freezes it). Used by `rotateV3CapWrite` for the cap-WRITE wrappers; identical
to `weldsAt` minus the last (cap-root) weld. -/
def weldsAtNoCapRoot (base stateBase : Nat) : List VmConstraint :=
  [ colEq (base + 1) (stateBase + state.BALANCE_LO)
  , colEq (base + 2) (stateBase + state.NONCE)
  , colEq (base + 3) (stateBase + state.BALANCE_HI)
  , colEq (base + 4) (stateBase + state.FIELD_BASE)
  , colEq (base + 5) (stateBase + state.FIELD_BASE + 1)
  , colEq (base + 6) (stateBase + state.FIELD_BASE + 2)
  , colEq (base + 7) (stateBase + state.FIELD_BASE + 3)
  , colEq (base + 8) (stateBase + state.FIELD_BASE + 4)
  , colEq (base + 9) (stateBase + state.FIELD_BASE + 5)
  , colEq (base + 10) (stateBase + state.FIELD_BASE + 6)
  , colEq (base + 11) (stateBase + state.FIELD_BASE + 7) ]

/-- The four appended PI pins of a rotated descriptor (PI slots `piBase..piBase+3`):
rotated OLD commit (first row) · rotated NEW commit · rotated height · caveat commit (last). -/
def rotPins (w piBase : Nat) : List VmConstraint :=
  [ .piBinding .first (w + B_STATE_COMMIT) piBase
  , .piBinding .last (w + 91 + B_STATE_COMMIT) (piBase + 1)
  , .piBinding .last (w + 91 + B_COMMITTED_HEIGHT) (piBase + 2)
  , .piBinding .last (w + 182 + C_COMMIT) (piBase + 3) ]

/-- **`rotateV3`** — the ONE parametric regen: append the rotated BEFORE/AFTER blocks and
the caveat region past the descriptor's own layout; weld where the v1 block carries the
datum; pin the rotated commits to four appended PI slots. Every v1 column index, constraint,
hash site, and range tooth is UNTOUCHED — the v1 theorems survive verbatim
(`rotateV3_satisfiedVm_v1`). -/
def rotateV3 (d : EffectVmDescriptor) : EffectVmDescriptor :=
  { name        := d.name ++ "-rot24-v3-staged"
  , traceWidth  := d.traceWidth + APPENDIX_SPAN
  , piCount     := d.piCount + 4
  , constraints := d.constraints
      ++ (weldsAt d.traceWidth STATE_BEFORE_BASE
          ++ weldsAt (d.traceWidth + 91) STATE_AFTER_BASE
          ++ rotPins d.traceWidth d.piCount)
  , hashSites   := d.hashSites ++ rotV3Appendix d.traceWidth
  , ranges      := d.ranges }

/-- **`rotateV3CapWrite`** — `rotateV3` with the cap-root weld DROPPED (`weldsAtNoCapRoot`), for the cap-WRITE
wrappers. The rotated cap-root limb (limb 25) is freed from the v1-state weld, so the cap-write `MapOp`
(`insertWriteOpRot`/`removeWriteOpRot`) drives it before≠after — note-spend-shaped, folding into the rotated
`wireCommitR` commitment — while the v1-state `cap_root` column (col 65/87) stays continuous. EVERYTHING ELSE
is `rotateV3` verbatim (same width, PI count, hash sites, ranges, the 11 other welds + the 4 commit pins), so
the per-effect faithfulness chains and the commitment-binding keystones are structurally identical; only the
single cap-root weld is absent. -/
def rotateV3CapWrite (d : EffectVmDescriptor) : EffectVmDescriptor :=
  { name        := d.name ++ "-rot24-v3-capwrite"
  , traceWidth  := d.traceWidth + APPENDIX_SPAN
  , piCount     := d.piCount + 4
  , constraints := d.constraints
      ++ (weldsAtNoCapRoot d.traceWidth STATE_BEFORE_BASE
          ++ weldsAtNoCapRoot (d.traceWidth + 91) STATE_AFTER_BASE
          ++ rotPins d.traceWidth d.piCount)
  , hashSites   := d.hashSites ++ rotV3Appendix d.traceWidth
  , ranges      := d.ranges }

/-- `rotateV3CapWrite` and `rotateV3` share width / piCount / hashSites / ranges (only the weld list
differs). -/
theorem rotateV3CapWrite_shape (d : EffectVmDescriptor) :
    (rotateV3CapWrite d).traceWidth = (rotateV3 d).traceWidth
    ∧ (rotateV3CapWrite d).piCount = (rotateV3 d).piCount
    ∧ (rotateV3CapWrite d).hashSites = (rotateV3 d).hashSites
    ∧ (rotateV3CapWrite d).ranges = (rotateV3 d).ranges :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ## §4 — the keystones, proved ONCE, parametric. -/

/-- A hash-site input that never reads the digest accumulator. -/
def colOnlyInput : HashInput → Bool
  | .col _ => true
  | .zero => true
  | .digest _ => false

/-- A site whose inputs are all accumulator-free. -/
def colOnly (s : VmHashSite) : Bool := s.inputs.all colOnlyInput

/-- A col-only site resolves identically under EVERY accumulator. -/
theorem resolvedInputs_colOnly (env : VmRowEnv) (acc acc' : List ℤ) (s : VmHashSite)
    (h : colOnly s = true) :
    s.resolvedInputs env acc = s.resolvedInputs env acc' := by
  unfold VmHashSite.resolvedInputs
  apply List.map_congr_left
  intro i hi
  have hci := List.all_eq_true.mp h i hi
  cases i with
  | col c => rfl
  | digest k => simp [colOnlyInput] at hci
  | zero => rfl

/-- **The col-only walk lemma**: anywhere in the ordered site walk — after ANY prefix, under
ANY accumulator — a col-only site's equation holds in its accumulator-free form. THIS is what
makes the appendix position-independent: no induction over the host descriptor's own sites is
ever needed. -/
theorem go_colOnly_mem (hash : List ℤ → ℤ) (env : VmRowEnv) :
    ∀ (acc : List ℤ) (sites : List VmHashSite),
      siteHoldsAll.go hash env acc sites →
      ∀ s ∈ sites, colOnly s = true →
        env.loc s.digestCol = hash (s.resolvedInputs env []) := by
  intro acc sites
  induction sites generalizing acc with
  | nil => intro _ s hs _; cases hs
  | cons t ts ih =>
    intro h s hs hcol
    obtain ⟨hd, hgo⟩ := h
    rcases List.mem_cons.mp hs with rfl | hs'
    · rw [hd, resolvedInputs_colOnly env acc [] s hcol]
    · exact ih _ hgo s hs' hcol

/-- The walk restricts to any prefix (the host descriptor's own sites still walk). -/
theorem go_append_left (hash : List ℤ → ℤ) (env : VmRowEnv) :
    ∀ (acc : List ℤ) (P Q : List VmHashSite),
      siteHoldsAll.go hash env acc (P ++ Q) → siteHoldsAll.go hash env acc P := by
  intro acc P
  induction P generalizing acc with
  | nil => intro Q _; trivial
  | cons t ts ih =>
    intro Q h
    obtain ⟨hd, hgo⟩ := h
    exact ⟨hd, ih _ Q hgo⟩

/-- Every rotated-block site is col-only (13 literal cases). -/
theorem rotV3SitesAt_colOnly (base : Nat) : ∀ s ∈ rotV3SitesAt base, colOnly s = true := by
  intro s hs
  simp only [rotV3SitesAt, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- Every caveat site is col-only (10 literal cases). -/
theorem caveatV3SitesAt_colOnly (base : Nat) :
    ∀ s ∈ caveatV3SitesAt base, colOnly s = true := by
  intro s hs
  simp only [caveatV3SitesAt, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

set_option maxHeartbeats 6400000 in
/-- **The block pin, parametric in `base`** (v10): the twenty-three col-chained site equations compose
into the chained rotated commitment — the row's state-commit carrier at `base + 68` IS
`wireCommitR` of the row's OWN 67 limbs and iroot (the faithful-8-felt completion shape). -/
theorem rotV3SitesAt_pin (hash : List ℤ → ℤ) (env : VmRowEnv) (base : Nat)
    (h : ∀ s ∈ rotV3SitesAt base, env.loc s.digestCol = hash (s.resolvedInputs env [])) :
    env.loc (base + 68)
      = wireCommitR hash (preLimbsAt base env.loc) (env.loc (base + 67)) := by
  have h0 : env.loc (base + 69) = hash [env.loc (base + 0), env.loc (base + 1),
      env.loc (base + 2), env.loc (base + 3)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 69, [.col (base + 0), .col (base + 1), .col (base + 2), .col (base + 3)], 4⟩
        (by simp [rotV3SitesAt])
  have h1 : env.loc (base + 70) = hash [env.loc (base + 69), env.loc (base + 4),
      env.loc (base + 5), env.loc (base + 6)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 70, [.col (base + 69), .col (base + 4), .col (base + 5), .col (base + 6)], 4⟩
        (by simp [rotV3SitesAt])
  have h2 : env.loc (base + 71) = hash [env.loc (base + 70), env.loc (base + 7),
      env.loc (base + 8), env.loc (base + 9)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 71, [.col (base + 70), .col (base + 7), .col (base + 8), .col (base + 9)], 4⟩
        (by simp [rotV3SitesAt])
  have h3 : env.loc (base + 72) = hash [env.loc (base + 71), env.loc (base + 10),
      env.loc (base + 11), env.loc (base + 12)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 72, [.col (base + 71), .col (base + 10), .col (base + 11),
        .col (base + 12)], 4⟩ (by simp [rotV3SitesAt])
  have h4 : env.loc (base + 73) = hash [env.loc (base + 72), env.loc (base + 13),
      env.loc (base + 14), env.loc (base + 15)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 73, [.col (base + 72), .col (base + 13), .col (base + 14),
        .col (base + 15)], 4⟩ (by simp [rotV3SitesAt])
  have h5 : env.loc (base + 74) = hash [env.loc (base + 73), env.loc (base + 16),
      env.loc (base + 17), env.loc (base + 18)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 74, [.col (base + 73), .col (base + 16), .col (base + 17),
        .col (base + 18)], 4⟩ (by simp [rotV3SitesAt])
  have h6 : env.loc (base + 75) = hash [env.loc (base + 74), env.loc (base + 19),
      env.loc (base + 20), env.loc (base + 21)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 75, [.col (base + 74), .col (base + 19), .col (base + 20),
        .col (base + 21)], 4⟩ (by simp [rotV3SitesAt])
  have h7 : env.loc (base + 76) = hash [env.loc (base + 75), env.loc (base + 22),
      env.loc (base + 23), env.loc (base + 24)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 76, [.col (base + 75), .col (base + 22), .col (base + 23),
        .col (base + 24)], 4⟩ (by simp [rotV3SitesAt])
  have h8 : env.loc (base + 77) = hash [env.loc (base + 76), env.loc (base + 25),
      env.loc (base + 26), env.loc (base + 27)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 77, [.col (base + 76), .col (base + 25), .col (base + 26),
        .col (base + 27)], 4⟩ (by simp [rotV3SitesAt])
  have h9 : env.loc (base + 78) = hash [env.loc (base + 77), env.loc (base + 28),
      env.loc (base + 29), env.loc (base + 30)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 78, [.col (base + 77), .col (base + 28), .col (base + 29),
        .col (base + 30)], 4⟩ (by simp [rotV3SitesAt])
  have h10 : env.loc (base + 79) = hash [env.loc (base + 78), env.loc (base + 31),
      env.loc (base + 32), env.loc (base + 33)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 79, [.col (base + 78), .col (base + 31), .col (base + 32),
        .col (base + 33)], 4⟩ (by simp [rotV3SitesAt])
  have h11 : env.loc (base + 80) = hash [env.loc (base + 79), env.loc (base + 34),
      env.loc (base + 35), env.loc (base + 36)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 80, [.col (base + 79), .col (base + 34), .col (base + 35),
        .col (base + 36)], 4⟩ (by simp [rotV3SitesAt])
  have h12 : env.loc (base + 81) = hash [env.loc (base + 80), env.loc (base + 37),
      env.loc (base + 38), env.loc (base + 39)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 81, [.col (base + 80), .col (base + 37), .col (base + 38),
        .col (base + 39)], 4⟩ (by simp [rotV3SitesAt])
  have h13 : env.loc (base + 82) = hash [env.loc (base + 81), env.loc (base + 40),
      env.loc (base + 41), env.loc (base + 42)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 82, [.col (base + 81), .col (base + 40), .col (base + 41),
        .col (base + 42)], 4⟩ (by simp [rotV3SitesAt])
  have h14 : env.loc (base + 83) = hash [env.loc (base + 82), env.loc (base + 43),
      env.loc (base + 44), env.loc (base + 45)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 83, [.col (base + 82), .col (base + 43), .col (base + 44),
        .col (base + 45)], 4⟩ (by simp [rotV3SitesAt])
  have h15 : env.loc (base + 84) = hash [env.loc (base + 83), env.loc (base + 46),
      env.loc (base + 47), env.loc (base + 48)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 84, [.col (base + 83), .col (base + 46), .col (base + 47),
        .col (base + 48)], 4⟩ (by simp [rotV3SitesAt])
  have h16 : env.loc (base + 85) = hash [env.loc (base + 84), env.loc (base + 49),
      env.loc (base + 50), env.loc (base + 51)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 85, [.col (base + 84), .col (base + 49), .col (base + 50),
        .col (base + 51)], 4⟩ (by simp [rotV3SitesAt])
  have h17 : env.loc (base + 86) = hash [env.loc (base + 85), env.loc (base + 52),
      env.loc (base + 53), env.loc (base + 54)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 86, [.col (base + 85), .col (base + 52), .col (base + 53),
        .col (base + 54)], 4⟩ (by simp [rotV3SitesAt])
  have h18 : env.loc (base + 87) = hash [env.loc (base + 86), env.loc (base + 55),
      env.loc (base + 56), env.loc (base + 57)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 87, [.col (base + 86), .col (base + 55), .col (base + 56),
        .col (base + 57)], 4⟩ (by simp [rotV3SitesAt])
  have h19 : env.loc (base + 88) = hash [env.loc (base + 87), env.loc (base + 58),
      env.loc (base + 59), env.loc (base + 60)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 88, [.col (base + 87), .col (base + 58), .col (base + 59),
        .col (base + 60)], 4⟩ (by simp [rotV3SitesAt])
  have h20 : env.loc (base + 89) = hash [env.loc (base + 88), env.loc (base + 61),
      env.loc (base + 62), env.loc (base + 63)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 89, [.col (base + 88), .col (base + 61), .col (base + 62),
        .col (base + 63)], 4⟩ (by simp [rotV3SitesAt])
  have h21 : env.loc (base + 90) = hash [env.loc (base + 89), env.loc (base + 64),
      env.loc (base + 65), env.loc (base + 66)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 90, [.col (base + 89), .col (base + 64), .col (base + 65),
        .col (base + 66)], 4⟩ (by simp [rotV3SitesAt])
  have h22 : env.loc (base + 68) = hash [env.loc (base + 90), env.loc (base + 67)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 68, [.col (base + 90), .col (base + 67)], 2⟩ (by simp [rotV3SitesAt])
  rw [h22, h21, h20, h19, h18, h17, h16, h15, h14, h13, h12, h11, h10, h9, h8, h7, h6, h5,
    h4, h3, h2, h1, h0]
  rfl

set_option maxHeartbeats 6400000 in
/-- **The caveat pin, parametric in `base`**: the ten col-chained caveat site equations
compose into the chained caveat commitment of the row's OWN manifest block. -/
theorem caveatV3SitesAt_pin (hash : List ℤ → ℤ) (env : VmRowEnv) (base : Nat)
    (h : ∀ s ∈ caveatV3SitesAt base, env.loc s.digestCol = hash (s.resolvedInputs env [])) :
    env.loc (base + 38) = caveatCommit hash (manifestAt base env.loc) := by
  have h0 : env.loc (base + 29) = hash [env.loc (base + 0), env.loc (base + 1),
      env.loc (base + 2), env.loc (base + 3)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 29, [.col (base + 0), .col (base + 1), .col (base + 2), .col (base + 3)], 4⟩
        (by simp [caveatV3SitesAt])
  have h1 : env.loc (base + 30) = hash [env.loc (base + 29), env.loc (base + 4),
      env.loc (base + 5), env.loc (base + 6)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 30, [.col (base + 29), .col (base + 4), .col (base + 5), .col (base + 6)], 4⟩
        (by simp [caveatV3SitesAt])
  have h2 : env.loc (base + 31) = hash [env.loc (base + 30), env.loc (base + 7),
      env.loc (base + 8), env.loc (base + 9)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 31, [.col (base + 30), .col (base + 7), .col (base + 8), .col (base + 9)], 4⟩
        (by simp [caveatV3SitesAt])
  have h3 : env.loc (base + 32) = hash [env.loc (base + 31), env.loc (base + 10),
      env.loc (base + 11), env.loc (base + 12)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 32, [.col (base + 31), .col (base + 10), .col (base + 11),
        .col (base + 12)], 4⟩ (by simp [caveatV3SitesAt])
  have h4 : env.loc (base + 33) = hash [env.loc (base + 32), env.loc (base + 13),
      env.loc (base + 14), env.loc (base + 15)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 33, [.col (base + 32), .col (base + 13), .col (base + 14),
        .col (base + 15)], 4⟩ (by simp [caveatV3SitesAt])
  have h5 : env.loc (base + 34) = hash [env.loc (base + 33), env.loc (base + 16),
      env.loc (base + 17), env.loc (base + 18)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 34, [.col (base + 33), .col (base + 16), .col (base + 17),
        .col (base + 18)], 4⟩ (by simp [caveatV3SitesAt])
  have h6 : env.loc (base + 35) = hash [env.loc (base + 34), env.loc (base + 19),
      env.loc (base + 20), env.loc (base + 21)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 35, [.col (base + 34), .col (base + 19), .col (base + 20),
        .col (base + 21)], 4⟩ (by simp [caveatV3SitesAt])
  have h7 : env.loc (base + 36) = hash [env.loc (base + 35), env.loc (base + 22),
      env.loc (base + 23), env.loc (base + 24)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 36, [.col (base + 35), .col (base + 22), .col (base + 23),
        .col (base + 24)], 4⟩ (by simp [caveatV3SitesAt])
  have h8 : env.loc (base + 37) = hash [env.loc (base + 36), env.loc (base + 25),
      env.loc (base + 26), env.loc (base + 27)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 37, [.col (base + 36), .col (base + 25), .col (base + 26),
        .col (base + 27)], 4⟩ (by simp [caveatV3SitesAt])
  have h9 : env.loc (base + 38) = hash [env.loc (base + 37), env.loc (base + 28)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 38, [.col (base + 37), .col (base + 28)], 2⟩ (by simp [caveatV3SitesAt])
  rw [h9, h8, h7, h6, h5, h4, h3, h2, h1, h0]
  rfl

#assert_axioms go_colOnly_mem
#assert_axioms rotV3SitesAt_pin
#assert_axioms caveatV3SitesAt_pin

/-- **The v1 survival keystone**: a row satisfying the rotated descriptor satisfies the
ORIGINAL descriptor — every existing per-effect faithfulness / anti-ghost / full-state
theorem composes through this unchanged. -/
theorem rotateV3_satisfiedVm_v1 (hash : List ℤ → ℤ) (d : EffectVmDescriptor)
    (env : VmRowEnv) (isFirst isLast : Bool)
    (h : satisfiedVm hash (rotateV3 d) env isFirst isLast) :
    satisfiedVm hash d env isFirst isLast := by
  obtain ⟨hc, hsites, hr⟩ := h
  exact ⟨fun c hc' => hc c (List.mem_append_left _ hc'),
    go_append_left hash env [] d.hashSites (rotV3Appendix d.traceWidth) hsites, hr⟩

/-- The appendix pins, extracted from a satisfying row: the BEFORE commit carrier, the
AFTER commit carrier, and the caveat commit carrier each carry the genuine chained
commitment of the row's OWN limbs. -/
theorem rotateV3_pins_commits (hash : List ℤ → ℤ) (d : EffectVmDescriptor)
    (env : VmRowEnv) (isFirst isLast : Bool)
    (h : satisfiedVm hash (rotateV3 d) env isFirst isLast) :
    env.loc (d.traceWidth + 68)
      = wireCommitR hash (preLimbsAt d.traceWidth env.loc) (env.loc (d.traceWidth + 67))
    ∧ env.loc (d.traceWidth + 91 + 68)
      = wireCommitR hash (preLimbsAt (d.traceWidth + 91) env.loc)
          (env.loc (d.traceWidth + 91 + 67))
    ∧ env.loc (d.traceWidth + 182 + 38)
      = caveatCommit hash (manifestAt (d.traceWidth + 182) env.loc) := by
  have hsites := h.2.1
  have heq := go_colOnly_mem hash env [] _ hsites
  have hmem : ∀ s ∈ rotV3Appendix d.traceWidth, s ∈ (rotateV3 d).hashSites :=
    fun s hs => List.mem_append_right _ hs
  refine ⟨?_, ?_, ?_⟩
  · exact rotV3SitesAt_pin hash env d.traceWidth fun s hs =>
      heq s (hmem s (List.mem_append_left _ (List.mem_append_left _ hs)))
        (rotV3SitesAt_colOnly _ s hs)
  · exact rotV3SitesAt_pin hash env (d.traceWidth + 91) fun s hs =>
      heq s (hmem s (List.mem_append_left _ (List.mem_append_right _ hs)))
        (rotV3SitesAt_colOnly _ s hs)
  · exact caveatV3SitesAt_pin hash env (d.traceWidth + 182) fun s hs =>
      heq s (hmem s (List.mem_append_right _ hs)) (caveatV3SitesAt_colOnly _ s hs)

/-- A weld of the rotated descriptor holds on every satisfying TRANSITION row (`isLast = false`).
The weld is a `.gate`, which under the deployed `when_transition()` binds only off the last row, so
the welded-column equality is read at the active row. -/
theorem rotateV3_weld (hash : List ℤ → ℤ) (d : EffectVmDescriptor)
    (env : VmRowEnv) (isFirst isLast : Bool) (hlast : isLast = false)
    (h : satisfiedVm hash (rotateV3 d) env isFirst isLast)
    {a b : Nat}
    (hw : colEq a b ∈ weldsAt d.traceWidth STATE_BEFORE_BASE
        ∨ colEq a b ∈ weldsAt (d.traceWidth + 91) STATE_AFTER_BASE) :
    env.loc a = env.loc b := by
  have hc := h.1 (colEq a b) (List.mem_append_right _ (by
    rcases hw with hw | hw
    · exact List.mem_append_left _ (List.mem_append_left _ hw)
    · exact List.mem_append_left _ (List.mem_append_right _ hw)))
  exact (colEq_holds_iff env isFirst isLast a b hlast).mp hc

/-- The CONFIRMED scalar welds, named: on every satisfying row, the rotated blocks' `r0`
carries the v1 balance (low limb) and `r1` the v1 nonce, before AND after; the rotated
`CAP_ROOT` limb carries the v1 cap root. -/
theorem rotateV3_welds_named (hash : List ℤ → ℤ) (d : EffectVmDescriptor)
    (env : VmRowEnv) (isFirst isLast : Bool) (hlast : isLast = false)
    (h : satisfiedVm hash (rotateV3 d) env isFirst isLast) :
    env.loc (d.traceWidth + 1) = env.loc (sbCol state.BALANCE_LO)
    ∧ env.loc (d.traceWidth + 2) = env.loc (sbCol state.NONCE)
    ∧ env.loc (d.traceWidth + B_CAP_ROOT) = env.loc (sbCol state.CAP_ROOT)
    ∧ env.loc (d.traceWidth + 91 + 1) = env.loc (saCol state.BALANCE_LO)
    ∧ env.loc (d.traceWidth + 91 + 2) = env.loc (saCol state.NONCE)
    ∧ env.loc (d.traceWidth + 91 + B_CAP_ROOT) = env.loc (saCol state.CAP_ROOT) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact rotateV3_weld hash d env isFirst isLast hlast h (Or.inl (by simp [weldsAt, sbCol]))
  · exact rotateV3_weld hash d env isFirst isLast hlast h (Or.inl (by simp [weldsAt, sbCol]))
  · exact rotateV3_weld hash d env isFirst isLast hlast h (Or.inl (by simp [weldsAt, sbCol]))
  · exact rotateV3_weld hash d env isFirst isLast hlast h (Or.inr (by simp [weldsAt, saCol]))
  · exact rotateV3_weld hash d env isFirst isLast hlast h (Or.inr (by simp [weldsAt, saCol]))
  · exact rotateV3_weld hash d env isFirst isLast hlast h (Or.inr (by simp [weldsAt, saCol]))

/-! ### Graduation side conditions lift parametrically. -/

theorem colOnly_siteInputWF (idx : Nat) (s : VmHashSite) (h : colOnly s = true) :
    s.inputs.all (siteInputWF idx) = true := by
  unfold colOnly at h
  rw [List.all_eq_true] at h ⊢
  intro i hi
  have hci := h i hi
  cases i with
  | col c => rfl
  | digest k => simp [colOnlyInput] at hci
  | zero => rfl

theorem sitesWFAux_colOnly :
    ∀ (idx : Nat) (Q : List VmHashSite), (∀ s ∈ Q, colOnly s = true) →
      sitesWFAux idx Q = true := by
  intro idx Q
  induction Q generalizing idx with
  | nil => intro _; rfl
  | cons t ts ih =>
    intro hQ
    show (t.inputs.all (siteInputWF idx) && sitesWFAux (idx + 1) ts) = true
    rw [colOnly_siteInputWF idx t (hQ t List.mem_cons_self),
      ih (idx + 1) (fun s hs => hQ s (List.mem_cons_of_mem t hs))]
    rfl

theorem sitesWFAux_append_colOnly :
    ∀ (idx : Nat) (P Q : List VmHashSite), (∀ s ∈ Q, colOnly s = true) →
      sitesWFAux idx (P ++ Q) = sitesWFAux idx P := by
  intro idx P
  induction P generalizing idx with
  | nil =>
    intro Q hQ
    rw [List.nil_append, sitesWFAux_colOnly idx Q hQ]
    rfl
  | cons t ts ih =>
    intro Q hQ
    show (t.inputs.all (siteInputWF idx) && sitesWFAux (idx + 1) (ts ++ Q))
      = (t.inputs.all (siteInputWF idx) && sitesWFAux (idx + 1) ts)
    rw [ih (idx + 1) Q hQ]

theorem rotV3Appendix_colOnly (w : Nat) : ∀ s ∈ rotV3Appendix w, colOnly s = true := by
  intro s hs
  unfold rotV3Appendix at hs
  rcases List.mem_append.mp hs with hs' | hs'
  · rcases List.mem_append.mp hs' with hs'' | hs''
    · exact rotV3SitesAt_colOnly _ s hs''
    · exact rotV3SitesAt_colOnly _ s hs''
  · exact caveatV3SitesAt_colOnly _ s hs'

/-- The graduation side conditions LIFT: a graduable cohort member's rotated form is
graduable — so `graduateV1_sound`/`_complete`/`_faithful` apply to all 26 with no new
per-descriptor checks. -/
theorem graduable_rotateV3 {d : EffectVmDescriptor} (h : graduable d = true) :
    graduable (rotateV3 d) = true := by
  unfold graduable at h ⊢
  simp only [Bool.and_eq_true] at h ⊢
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨⟨?_, ?_⟩, h3⟩
  · show sitesWFAux 0 (d.hashSites ++ rotV3Appendix d.traceWidth) = true
    rw [sitesWFAux_append_colOnly 0 d.hashSites _ (rotV3Appendix_colOnly d.traceWidth)]
    exact h1
  · show sitesFit (d.hashSites ++ rotV3Appendix d.traceWidth) = true
    unfold sitesFit at h2 ⊢
    rw [List.all_append, h2, Bool.true_and, List.all_eq_true]
    intro s hs
    unfold rotV3Appendix at hs
    rcases List.mem_append.mp hs with hs' | hs'
    · rcases List.mem_append.mp hs' with hs'' | hs'' <;>
      · simp only [rotV3SitesAt, List.mem_cons, List.not_mem_nil, or_false] at hs''
        rcases hs'' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    · simp only [caveatV3SitesAt, List.mem_cons, List.not_mem_nil, or_false] at hs'
      rcases hs' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

#assert_axioms rotateV3_satisfiedVm_v1
#assert_axioms rotateV3_pins_commits
#assert_axioms rotateV3_welds_named
#assert_axioms graduable_rotateV3

/-! ### The Satisfied2-level keystones (one composition each, parametric in `d`). -/

/-- The graduated rotated descriptor of a cohort member. -/
def v3Of (d : EffectVmDescriptor) : EffectVmDescriptor2 := graduateV1 (rotateV3 d)

/-- A `Satisfied2` witness of the rotated graduation yields the FULL v1 denotation of the
ORIGINAL descriptor on every row — the per-effect soundness chains lift to v3 by THIS one
composition. -/
theorem rotV3_sound_v1 (permOut : List ℤ → List ℤ) (hash : List ℤ → ℤ) (d : EffectVmDescriptor)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hgrad : graduable d = true)
    (hf : Satisfied2Faithful permOut hash (v3Of d) minit mfin maddrs t) :
    ∀ i, i < t.rows.length →
      satisfiedVm hash d (envAt t i) (i == 0) (i + 1 == t.rows.length) := by
  intro i hi
  exact rotateV3_satisfiedVm_v1 hash d _ _ _
    (satisfied2Faithful_satisfiedVm permOut hash (rotateV3 d) minit mfin maddrs t
      (graduable_rotateV3 hgrad) hf i hi)

/-- Every row of a `Satisfied2` witness pins all three rotated commitments. -/
theorem rotV3_pins (permOut : List ℤ → List ℤ) (hash : List ℤ → ℤ) (d : EffectVmDescriptor)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hgrad : graduable d = true)
    (hf : Satisfied2Faithful permOut hash (v3Of d) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) :
    (envAt t i).loc (d.traceWidth + 68)
      = wireCommitR hash (preLimbsAt d.traceWidth (envAt t i).loc)
          ((envAt t i).loc (d.traceWidth + 67))
    ∧ (envAt t i).loc (d.traceWidth + 91 + 68)
      = wireCommitR hash (preLimbsAt (d.traceWidth + 91) (envAt t i).loc)
          ((envAt t i).loc (d.traceWidth + 91 + 67))
    ∧ (envAt t i).loc (d.traceWidth + 182 + 38)
      = caveatCommit hash (manifestAt (d.traceWidth + 182) (envAt t i).loc) :=
  rotateV3_pins_commits hash d _ _ _
    (satisfied2Faithful_satisfiedVm permOut hash (rotateV3 d) minit mfin maddrs t
      (graduable_rotateV3 hgrad) hf i hi)

/-- The rotated descriptor PUBLISHES: first row → rotated OLD commit on PI `d.piCount`;
last row → rotated NEW commit, rotated height, caveat commit on `d.piCount + 1..3`. -/
theorem rotV3_publishes (permOut : List ℤ → List ℤ) (hash : List ℤ → ℤ) (d : EffectVmDescriptor)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hgrad : graduable d = true)
    (hf : Satisfied2Faithful permOut hash (v3Of d) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) :
    ((i == 0) = true →
      (envAt t i).loc (d.traceWidth + B_STATE_COMMIT) = (envAt t i).pub d.piCount)
    ∧ ((i + 1 == t.rows.length) = true →
      (envAt t i).loc (d.traceWidth + 91 + B_STATE_COMMIT) = (envAt t i).pub (d.piCount + 1)
      ∧ (envAt t i).loc (d.traceWidth + 91 + B_COMMITTED_HEIGHT)
          = (envAt t i).pub (d.piCount + 2)
      ∧ (envAt t i).loc (d.traceWidth + 182 + C_COMMIT) = (envAt t i).pub (d.piCount + 3)) := by
  have h := satisfied2Faithful_satisfiedVm permOut hash (rotateV3 d) minit mfin maddrs t
    (graduable_rotateV3 hgrad) hf i hi
  have hmem : ∀ c ∈ rotPins d.traceWidth d.piCount, c ∈ (rotateV3 d).constraints :=
    fun c hc => List.mem_append_right _ (List.mem_append_right _ hc)
  have h0 := h.1 _ (hmem (.piBinding .first (d.traceWidth + B_STATE_COMMIT) d.piCount)
    (by simp [rotPins]))
  have h1 := h.1 _ (hmem (.piBinding .last (d.traceWidth + 91 + B_STATE_COMMIT)
    (d.piCount + 1)) (by simp [rotPins]))
  have h2 := h.1 _ (hmem (.piBinding .last (d.traceWidth + 91 + B_COMMITTED_HEIGHT)
    (d.piCount + 2)) (by simp [rotPins]))
  have h3 := h.1 _ (hmem (.piBinding .last (d.traceWidth + 182 + C_COMMIT) (d.piCount + 3))
    (by simp [rotPins]))
  simp only [VmConstraint.holdsVm] at h0 h1 h2 h3
  exact ⟨h0, fun hl => ⟨h1 hl, h2 hl, h3 hl⟩⟩

set_option maxHeartbeats 1600000 in
/-- **THE END-TO-END KEYSTONE — once, for all 26.** Two `Satisfied2` witnesses of ANY cohort
member's rotated graduation publishing the SAME rotated OLD commit, the SAME rotated NEW
commit, and the SAME caveat commit agree on the WHOLE rotated before block, the WHOLE after
block (all 24 registers — balance/nonce included by the welds — every map root, lifecycle,
epoch, height), BOTH iroots, the published height, AND the WHOLE caveat manifest (every
entry's type tag, DOMAIN TAG, KEY, params) — under the ONE CR floor, via the PARAMETRIC
`wireCommitR_binds` / `caveatCommit_binds`. -/
theorem rotV3_binds_published (permOut : List ℤ → List ℤ) (hash : List ℤ → ℤ)
    (hCR : Poseidon2SpongeCR hash)
    (d : EffectVmDescriptor)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (minit' : ℤ → ℤ) (mfin' : ℤ → ℤ × Nat) (maddrs' : List ℤ) (t' : VmTrace)
    (hgrad : graduable d = true)
    (hf : Satisfied2Faithful permOut hash (v3Of d) minit mfin maddrs t)
    (hf' : Satisfied2Faithful permOut hash (v3Of d) minit' mfin' maddrs' t')
    (i j : Nat) (hi : i < t.rows.length) (hj : j < t'.rows.length)
    (hfirst : (i == 0) = true) (hfirst' : (j == 0) = true)
    (k l : Nat) (hk : k < t.rows.length) (hl : l < t'.rows.length)
    (hlast : (k + 1 == t.rows.length) = true) (hlast' : (l + 1 == t'.rows.length) = true)
    (hpubOld : (envAt t i).pub d.piCount = (envAt t' j).pub d.piCount)
    (hpubNew : (envAt t k).pub (d.piCount + 1) = (envAt t' l).pub (d.piCount + 1))
    (hpubCav : (envAt t k).pub (d.piCount + 3) = (envAt t' l).pub (d.piCount + 3)) :
    (preLimbsAt d.traceWidth (envAt t i).loc = preLimbsAt d.traceWidth (envAt t' j).loc
      ∧ (envAt t i).loc (d.traceWidth + 67) = (envAt t' j).loc (d.traceWidth + 67))
    ∧ (preLimbsAt (d.traceWidth + 91) (envAt t k).loc
        = preLimbsAt (d.traceWidth + 91) (envAt t' l).loc
      ∧ (envAt t k).loc (d.traceWidth + 91 + 67) = (envAt t' l).loc (d.traceWidth + 91 + 67)
      ∧ (envAt t k).pub (d.piCount + 2) = (envAt t' l).pub (d.piCount + 2))
    ∧ manifestAt (d.traceWidth + 182) (envAt t k).loc
        = manifestAt (d.traceWidth + 182) (envAt t' l).loc := by
  have hp := rotV3_pins permOut hash d minit mfin maddrs t hgrad hf
  have hp' := rotV3_pins permOut hash d minit' mfin' maddrs' t' hgrad hf'
  have hq := rotV3_publishes permOut hash d minit mfin maddrs t hgrad hf
  have hq' := rotV3_publishes permOut hash d minit' mfin' maddrs' t' hgrad hf'
  refine ⟨?_, ?_, ?_⟩
  · -- the before block, via the first-row pins
    have hc := (hq i hi).1 hfirst
    have hc' := (hq' j hj).1 hfirst'
    have hwire : wireCommitR hash (preLimbsAt d.traceWidth (envAt t i).loc)
        ((envAt t i).loc (d.traceWidth + 67))
        = wireCommitR hash (preLimbsAt d.traceWidth (envAt t' j).loc)
            ((envAt t' j).loc (d.traceWidth + 67)) := by
      rw [← (hp i hi).1, ← (hp' j hj).1]
      show (envAt t i).loc (d.traceWidth + B_STATE_COMMIT)
        = (envAt t' j).loc (d.traceWidth + B_STATE_COMMIT)
      rw [hc, hc', hpubOld]
    exact wireCommitR_binds hash hCR
      (by rw [preLimbsAt_length, preLimbsAt_length]) hwire
  · -- the after block, via the last-row pins
    obtain ⟨hc, hh, -⟩ := (hq k hk).2 hlast
    obtain ⟨hc', hh', -⟩ := (hq' l hl).2 hlast'
    have hwire : wireCommitR hash (preLimbsAt (d.traceWidth + 91) (envAt t k).loc)
        ((envAt t k).loc (d.traceWidth + 91 + 67))
        = wireCommitR hash (preLimbsAt (d.traceWidth + 91) (envAt t' l).loc)
            ((envAt t' l).loc (d.traceWidth + 91 + 67)) := by
      rw [← (hp k hk).2.1, ← (hp' l hl).2.1]
      show (envAt t k).loc (d.traceWidth + 91 + B_STATE_COMMIT)
        = (envAt t' l).loc (d.traceWidth + 91 + B_STATE_COMMIT)
      rw [hc, hc', hpubNew]
    obtain ⟨hpre, hir⟩ := wireCommitR_binds hash hCR
      (by rw [preLimbsAt_length, preLimbsAt_length]) hwire
    refine ⟨hpre, hir, ?_⟩
    rw [← hh, ← hh']
    exact congrArg (fun L => L.getD 31 0) hpre
  · -- the caveat manifest, via the last-row pin
    obtain ⟨-, -, hk1⟩ := (hq k hk).2 hlast
    obtain ⟨-, -, hk2⟩ := (hq' l hl).2 hlast'
    have hcc : caveatCommit hash (manifestAt (d.traceWidth + 182) (envAt t k).loc)
        = caveatCommit hash (manifestAt (d.traceWidth + 182) (envAt t' l).loc) := by
      rw [← (hp k hk).2.2, ← (hp' l hl).2.2]
      show (envAt t k).loc (d.traceWidth + 182 + C_COMMIT)
        = (envAt t' l).loc (d.traceWidth + 182 + C_COMMIT)
      rw [hk1, hk2, hpubCav]
    exact caveatCommit_binds hash hCR hcc

#assert_axioms rotV3_sound_v1
#assert_axioms rotV3_pins
#assert_axioms rotV3_publishes
#assert_axioms rotV3_binds_published

/-! ## §5 — the v3 registry: all 27 v2-cohort members (+ the 8 widened), rotated. -/

/-- Append v2-native extras (map ops / mem ops / lookups) to a rotated graduation —
the attenuate phase-B leg and the dynamic setField ride through unchanged. -/
def v3OfWith (d : EffectVmDescriptor) (extras : List VmConstraint2) : EffectVmDescriptor2 :=
  { v3Of d with constraints := (v3Of d).constraints ++ extras }

/-- The graduated cap-WRITE rotated descriptor (cap-root weld DROPPED — the rotated cap-root limb is
witness-carried, note-spend-shaped). -/
def v3OfCapWrite (d : EffectVmDescriptor) : EffectVmDescriptor2 := graduateV1 (rotateV3CapWrite d)

/-- Append v2-native extras (the cap-crown ROTATED-limb write leg) to a cap-WRITE rotated graduation. As
`v3OfWith` but over `rotateV3CapWrite` — the cap-root advance lives on the rotated limb (`insertWriteOpRot`/
`removeWriteOpRot`), escaping the v1-state continuity collision. -/
def v3OfWithCapWrite (d : EffectVmDescriptor) (extras : List VmConstraint2) : EffectVmDescriptor2 :=
  { v3OfCapWrite d with constraints := (v3OfCapWrite d).constraints ++ extras }

/-- **`withSelectorGate s d`** — append the per-row SELECTOR-BINDING tooth (`selectorGate s`,
`EffectVmEmit.§6½`) to an ALREADY-graduated v2 registry member, lifted into a v2 `.base`
constraint. This is the cross-selector REPLAY close at the REGISTRY level: it BINDS the
descriptor to its own runtime selector column `s` so a row carrying a FOREIGN selector
(`sel[s] = 0`, `sel[NOOP] = 0`) is UNSAT — a one-row-per-effect trace cannot smuggle a
heterogeneous TAIL effect (whose transition is otherwise unforced by this descriptor) under
this descriptor's proof. `s` is the DEPLOYED runtime selector column (`columns::sel`, the
column `effect_vm/trace.rs::effect_selector` sets), NOT the per-effect Lean faithfulness
abstraction (e.g. the live `AttenuateCapability` row sets `sel[48]`, so the attenuate member
gates on `48`, not `selA.ATTENUATE = 2`). Appending at the registry entry (rather than the v1
FACE) keeps the SHARED faces (grantCap and attenuate both ride `attenuateVmDescriptor`; revoke
rides it via a rename) gating to their OWN distinct runtime selectors. The honest leg is
unaffected: an honest HOMOGENEOUS turn (the only kind the single-descriptor sovereign verify
path receives — heterogeneous turns split per cohort in PATH-PRESERVE / are rejected by the
rotated prover) lays only `sel[s] = 1` active rows and `sel[NOOP] = 1` pads, both of which the
gate admits (`selectorGate_holds_of_active` / `_of_pad`). -/
def withSelectorGate (s : Nat) (d : EffectVmDescriptor2) : EffectVmDescriptor2 :=
  { d with constraints := d.constraints ++ [.base (selectorGate s)] }

/-- `withSelectorGate` ONLY appends a `.base` constraint: it touches no table, hash site, range, or
mem/map op, so the gathered `memOpsOf`/`mapOpsOf`/`memLog`/`mapLog` and the `hashSites`/`ranges`/
`tables` are definitionally those of `d`. -/
theorem withSelectorGate_constraints (s : Nat) (d : EffectVmDescriptor2) :
    (withSelectorGate s d).constraints = d.constraints ++ [.base (selectorGate s)] := rfl

/-- The appended `.base` op surfaces NO mem op, so the gathered `memOpsOf` is `d`'s. -/
theorem withSelectorGate_memOpsOf (s : Nat) (d : EffectVmDescriptor2) :
    Dregg2.Circuit.DescriptorIR2.memOpsOf (withSelectorGate s d)
      = Dregg2.Circuit.DescriptorIR2.memOpsOf d := by
  simp [Dregg2.Circuit.DescriptorIR2.memOpsOf, withSelectorGate_constraints, List.filterMap_append]

/-- ...and NO map op. -/
theorem withSelectorGate_mapOpsOf (s : Nat) (d : EffectVmDescriptor2) :
    Dregg2.Circuit.DescriptorIR2.mapOpsOf (withSelectorGate s d)
      = Dregg2.Circuit.DescriptorIR2.mapOpsOf d := by
  simp [Dregg2.Circuit.DescriptorIR2.mapOpsOf, withSelectorGate_constraints, List.filterMap_append]

/-- ...so the gathered memory log is `d`'s, op-for-op. -/
theorem withSelectorGate_memLog (s : Nat) (d : EffectVmDescriptor2)
    (t : Dregg2.Circuit.DescriptorIR2.VmTrace) :
    Dregg2.Circuit.DescriptorIR2.memLog (withSelectorGate s d) t
      = Dregg2.Circuit.DescriptorIR2.memLog d t := by
  simp [Dregg2.Circuit.DescriptorIR2.memLog, withSelectorGate_memOpsOf]

/-- ...and the gathered map log is `d`'s. -/
theorem withSelectorGate_mapLog (s : Nat) (d : EffectVmDescriptor2)
    (t : Dregg2.Circuit.DescriptorIR2.VmTrace) :
    Dregg2.Circuit.DescriptorIR2.mapLog (withSelectorGate s d) t
      = Dregg2.Circuit.DescriptorIR2.mapLog d t := by
  simp [Dregg2.Circuit.DescriptorIR2.mapLog, withSelectorGate_mapOpsOf]

/-- **`withSelectorGate` is a strict-ADD on `Satisfied2`** (constraint-subset monotonicity). A trace
satisfying the gated descriptor satisfies the BARE descriptor: the gated descriptor's constraint list
is `d`'s plus one appended `.base (selectorGate s)`, so every `d`-constraint is among the gated ones
(`rowConstraints` restricts), and every other `Satisfied2` field (hashes, ranges, the four memory legs
and the map-table leg) is UNCHANGED because the appended `.base` contributes no mem/map op
(`memOpsOf`/`mapOpsOf` filter to `.memOp`/`.mapOp`). This lets every per-effect VALUE/`ClosedLog`
keystone — stated over the bare `d` — lift to the DEPLOYED gated registry member with no reproof. -/
theorem withSelectorGate_satisfied2 (hash : List ℤ → ℤ) (s : Nat) (d : EffectVmDescriptor2)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : Dregg2.Circuit.DescriptorIR2.VmTrace)
    (h : Satisfied2 hash (withSelectorGate s d) minit mfin maddrs t) :
    Satisfied2 hash d minit mfin maddrs t :=
  { rowConstraints := fun i hi c hc =>
      h.rowConstraints i hi c (by
        rw [withSelectorGate_constraints]; exact List.mem_append_left _ hc)
    rowHashes := h.rowHashes
    rowRanges := h.rowRanges
    memAddrsNodup := h.memAddrsNodup
    memClosed := by have := h.memClosed; rwa [withSelectorGate_memLog] at this
    memDisciplined := by have := h.memDisciplined; rwa [withSelectorGate_memLog] at this
    memBalanced := by have := h.memBalanced; rwa [withSelectorGate_memLog] at this
    memTableFaithful := by have := h.memTableFaithful; rwa [withSelectorGate_memLog] at this
    mapTableFaithful := by have := h.mapTableFaithful; rwa [withSelectorGate_mapLog] at this }

/-- The v1 face of the dynamic setField (its two mem ops are the v2 extras). -/
def setFieldDynV1Face : EffectVmDescriptor :=
  { name        := "dregg-effectvm-setfield-dyn-v2"
  , traceWidth  := EFFECT_VM_WIDTH
  , piCount     := 42
  , constraints := [ .gate gSlotRange, selectorGate EffectVmEmitSetField.SEL_SET_FIELD ]
  , hashSites   := []
  , ranges      := [] }

-- `attenuateV3` / `revokeCapabilityV3` are defined BELOW, after the ROTATED-limb cap-write ops
-- (`heldReadOpRot` / `keepWriteOpRot` / `removeWriteOpRot`), onto which they are rebased (the SILENT-FORGE
-- close — see `keepWriteOpRot`'s FORGE NOTE). The original `v3OfWith … [heldReadOp, keepWriteOp/removeWriteOp]`
-- forms wrote the V1-STATE cap-root (col 65/87) guarded on the never-firing `selA.ATTENUATE = 2`, so the
-- post cap-root was UNBOUND (forgeable). Their rebased forms ride `v3OfWithCapWrite` over the tick face with
-- the rotated-limb write ops guarded on the FIRING selector.

/-! ### The cap-family WRITE map-ops (the guarantee-A soundness close — `docs/CIRCUIT-FUNCTIONAL-
CORRECTNESS.md`, the 5 REAL Class-B gaps).

The fan-out cap-family effects (delegate / introduce / delegateAtten / revokeDelegation /
refreshDelegation) carry the 70-gate authority-READ appendix (`capOpenConstraintsEff`, the in-circuit
membership open) but their base descriptor left the cap-tree WRITE unforced: the post cap-root rode
either an OPAQUE parameter move (`param.CAP_DIGEST_NEW` — the moving face, delegate/delegateAtten/
grantCap) or the on-row FREEZE (`gCapPass` — introduce/revokeDelegation/refreshDelegation), with the
genuine sorted-tree move asserted only off-row as a PROVER-SUPPLIED `SpineCommits` hypothesis. A prover
could publish a wrong post-cap-root undetected — guarantee A (Authority) unforced.

These WRITE map-ops close that ON THE LIVE WIRE, mirroring `keepWriteOp` (attenuate): the post cap-root
is the GENUINE sorted insert/remove/update of the touched key against the BEFORE cap-root the appendix
membership-opens (`writesTo`, FUNCTIONAL under CR via `writesTo_functional` — a forged `new_cap_root`
is UNSAT). The MOVING-face slots (delegate/delegateAtten/grantCap) bind the move gate's post-root to a
genuine `.insert`; the value column is the conferred-rights mask (`prmCol KEEP_MASK`), the key the
edge's cap-key (`prmCol CAP_KEY`). All guard on the abstract cap-graph-row selector
`selA.ATTENUATE` (the same one `heldReadOp`/`keepWriteOp` use; the concrete sel-N mapping is the Rust
registry's job). -/

/-- The delegate/grant INSERT: the post `cap_root` is the GENUINE sorted INSERT of the conferred-rights
mask (`param[KEEP_MASK]`) at the new edge's cap-key (`param[CAP_KEY]`) — the FRESH grant. `op = .insert`
opens against the new tree; the paired authority membership-open (the cap-open appendix) authenticates
the delegator's held cap. Guarded by the cap-graph-row selector. -/
def insertWriteOp : MapOp :=
  { guard   := .var EffectVmEmitAttenuateA.selA.ATTENUATE
  , root    := .var (sbCol state.CAP_ROOT)
  , key     := .var (prmCol CAP_KEY)
  , value   := .var (prmCol KEEP_MASK)
  , newRoot := .var (saCol state.CAP_ROOT)
  , op      := .insert }

/-! ### The ROTATED-LIMB cap-write ops (the v1-state continuity-collision close — note-spend-shaped).

The original `heldReadOp`/`insertWriteOp`/`removeWriteOp` read/write the cap-root on the V1-STATE column
(`sbCol/saCol state.CAP_ROOT` = col 65/87). That column is subject to the v1 cross-row CONTINUITY transition
`transition CAP_ROOT CAP_ROOT` (`next.before[11] == this.after[11]`, `EffectVmEmitTransfer.transitionAll`).
A genuine cap-tree write moves the AFTER cap-root (col 87) off the BEFORE (col 65); the continuity then
demands `before_root == after_root` row-over-row — JOINTLY UNSAT for any real write, so the wrapper was
UNPROVABLE (no satisfying trace, hence the Rust prove-through could never close).

The note-spend grow-gate ESCAPES this exactly: its nullifier accumulator lives on the rotated-block limb 26
(`beforeNullifierRootCol`/`afterNullifierRootCol`) — a WITNESS-CARRIED limb that is NOT a v1-state column and
carries NO `transitionAll` continuity, yet folds into the rotated `wireCommitR` commitment as an absorbed
input (site `base+47` absorbs limbs 25/26/27). MIRROR that for the cap-root: place the WRITE accumulator on
the rotated-block CAP_ROOT limb (limb 25, `B_CAP_ROOT`) of the BEFORE/AFTER blocks. The v1-state col 65/87
stays FROZEN (the prover sets `before==after` there, continuity trivially holds — the cap move is carried by
the rotated limb), and limb 25 — once FREED from the `weldsAt` v1-state weld (`rotateV3CapWrite` below) — is
free to move before≠after and folds into the committed rotated state-commit. -/

/-- The rotated BEFORE-block `cap_root` limb column (limb 25 of the before block at `base = w`). The deployed
cap accumulator's PRE root the membership-open + write-gate open against — note-spend-shaped, NOT col 65. -/
def beforeCapRootCol (w : Nat) : Nat := w + B_CAP_ROOT

/-- The rotated AFTER-block `cap_root` limb column (limb 25 of the after block at `base = w + 91`). The
deployed cap accumulator's POST root — the write-gate's `newRoot`, witness-carried (no v1-state continuity). -/
def afterCapRootCol (w : Nat) : Nat := w + 91 + B_CAP_ROOT

/-- The held-capability MEMBERSHIP read on the ROTATED before-block cap-root limb (limb 25). The before
`cap_root` (rotated limb) opens at `param[CAP_KEY]` to `param[HELD_MASK]` (root unchanged — a read). The
membership-read authenticates against the SAME root the write-gate opens against. **Guarded by the per-effect
runtime selector column `s`** — the column the trace generator sets to `1` on THIS effect's active row (e.g.
`sel.REVOKE_DELEGATION = 30` for revokeDelegation). The forge close (`bd7ba0bf9`): the guard MUST be the
selector that fires on the cap-write row, else the map_op never fires and the AFTER cap-root rides unbound. -/
def heldReadOpRot (s : Nat) : MapOp :=
  { guard   := .var s
  , root    := .var (beforeCapRootCol EFFECT_VM_WIDTH)
  , key     := .var (prmCol CAP_KEY)
  , value   := .var (prmCol HELD_MASK)
  , newRoot := .var (beforeCapRootCol EFFECT_VM_WIDTH)
  , op      := .read }

/-- The held/anchor MEMBERSHIP read for the INSERT cap-write wrappers, on the ROTATED before-block cap-root
limb (limb 25), at a key DISTINCT from the inserted `CAP_KEY`. The before `cap_root` opens at
`param[ANCHOR_KEY]` to `param[ANCHOR_MASK]` (root unchanged — a read). This authenticates the delegator's
held authority against an ALREADY-PRESENT anchor leaf, while the paired `insertWriteOpRot` creates the FRESH
edge at the ABSENT `CAP_KEY` — the two no longer collide on one key (the joint-UNSAT the shared-`CAP_KEY`
read+insert hit on the deployed `insert_witness`, which refuses an already-present key). The revoke wrapper
keeps `heldReadOpRot` (read+remove the SAME present key — consistent, the proven template). **Guarded by the
per-effect runtime selector column `s`** (the column the trace sets to `1` on THIS effect's active row, e.g.
`sel.GRANT_CAP = 3` / `sel.INTRODUCE = 35`) — the forge close: a wrong guard (the old `selA.ATTENUATE = 2`)
never fires, leaving the AFTER cap-root unbound. -/
def anchorReadOpRot (s : Nat) : MapOp :=
  { guard   := .var s
  , root    := .var (beforeCapRootCol EFFECT_VM_WIDTH)
  , key     := .var (prmCol ANCHOR_KEY)
  , value   := .var (prmCol ANCHOR_MASK)
  , newRoot := .var (beforeCapRootCol EFFECT_VM_WIDTH)
  , op      := .read }

/-- The delegate/grant/introduce INSERT on the ROTATED limbs: the AFTER rotated cap-root (limb 25 of the
after block) IS the GENUINE sorted insert of `param[KEEP_MASK]` at `param[CAP_KEY]` into the BEFORE rotated
cap-root (limb 25). `writesTo` is FUNCTIONAL under CR — a forged after-root is UNSAT. The accumulator lives
on a witness-carried rotated limb (note-spend-shaped), so the v1-state continuity transition is undisturbed.
**Guarded by the per-effect runtime selector column `s`** (the column that is `1` on this effect's active
cap-write row — `sel.GRANT_CAP`/`sel.INTRODUCE`); the forge close re-points it off the never-firing
`selA.ATTENUATE = 2`, so the AFTER cap-root (`afterCapRootCol`) is GENUINELY bound. -/
def insertWriteOpRot (s : Nat) : MapOp :=
  { guard   := .var s
  , root    := .var (beforeCapRootCol EFFECT_VM_WIDTH)
  , key     := .var (prmCol CAP_KEY)
  , value   := .var (prmCol KEEP_MASK)
  , newRoot := .var (afterCapRootCol EFFECT_VM_WIDTH)
  , op      := .insert }

/-- The revokeDelegation REMOVE on the ROTATED limbs: the AFTER rotated cap-root is the genuine sorted
ZERO-value write (the slot REMOVE) at `param[CAP_KEY]` into the BEFORE rotated cap-root. Note-spend-shaped:
witness-carried, folds into the committed rotated state-commit, no v1-state continuity collision.
**Guarded by the per-effect runtime selector column `s`** (`sel.REVOKE_DELEGATION = 30` on the
revokeDelegation row); the forge close re-points it off the never-firing `selA.ATTENUATE = 2` so the
AFTER cap-root is GENUINELY bound to the sorted REMOVE. -/
def removeWriteOpRot (s : Nat) : MapOp :=
  { guard   := .var s
  , root    := .var (beforeCapRootCol EFFECT_VM_WIDTH)
  , key     := .var (prmCol CAP_KEY)
  , value   := .const 0
  , newRoot := .var (afterCapRootCol EFFECT_VM_WIDTH)
  , op      := .write }

/-- The attenuate IN-PLACE UPDATE-AT-KEY on the ROTATED limbs: the AFTER rotated cap-root (limb 25 of the
after block) IS the GENUINE sorted insert-or-update of the NARROWED rights (`param[KEEP_MASK]`) at the
SAME held key (`param[CAP_KEY]`) into the BEFORE rotated cap-root (limb 25). The attenuate analog of
`removeWriteOpRot` (a `.write` insert-or-update, not the ZERO-sentinel remove): the slot's rights are
narrowed to `KEEP_MASK ⊑ HELD_MASK`. `writesTo` is FUNCTIONAL under CR — a forged after-root is UNSAT.
The accumulator lives on a witness-carried rotated limb (note-spend-shaped), so the v1-state continuity
transition is undisturbed. **Guarded by the per-effect runtime selector column `s`** (the column that is
`1` on the live attenuate row — `sel.ATTENUATE_CAPABILITY = 48`); the forge close re-points it off the
never-firing `selA.ATTENUATE = 2` (the SET_FIELD column), so the AFTER cap-root (`afterCapRootCol`) is
GENUINELY bound — the var2-guarded V1-state `keepWriteOp` (col 65/87) silent-forge is closed. -/
def keepWriteOpRot (s : Nat) : MapOp :=
  { guard   := .var s
  , root    := .var (beforeCapRootCol EFFECT_VM_WIDTH)
  , key     := .var (prmCol CAP_KEY)
  , value   := .var (prmCol KEEP_MASK)
  , newRoot := .var (afterCapRootCol EFFECT_VM_WIDTH)
  , op      := .write }

/-! ### The SILENT-FORGE close for attenuate / revokeCapability (the cap-WRITE wrapper rebase, applied).

`attenuateV3` (sel `ATTENUATE_CAPABILITY = 48`) and `revokeCapabilityV3` (sel `REVOKE_CAPABILITY = 24`)
previously rode `v3OfWith … [.mapOp heldReadOp, .mapOp keepWriteOp/removeWriteOp, …]` — the V2 ops whose guard
is the never-firing `selA.ATTENUATE = 2` (the SET_FIELD column) AND whose write target is the V1-STATE cap-root
(col 65/87, NOT a rotated-limb commitment input, no witness-heap bridge). So on the live wire the map_op never
fired and the post cap-root rode UNBOUND — a fabricated root provable + light-client-accepted (the SAME forge
the cap-WRITE wrappers carried). The close mirrors `delegateV3`/`revokeDelegationWriteV3` EXACTLY: rebase onto
the MOVING tick face (`attenuateVmDescriptorGenuineNoRecomputeTick` — frees `cap_root`, ticks the nonce) via
`v3OfWithCapWrite` (drops the cap-root weld; the rotated limb 25 is witness-carried, note-spend-shaped) with
the ROTATED-limb write ops guarded on the FIRING selector. The map_op now FIRES on the effect's row and binds
`afterCapRootCol` (descriptor var 264); the v1-state cap-root (col 65/87) FREEZES (pass-through). -/

/-- The rotated attenuate WITH the cap-crown phase-B circuit leg, on the ROTATED-limb write path (the
silent-forge close): held-membership map read (`heldReadOpRot` — read+narrow the SAME held key, the
revoke-shaped consistent template), the attenuated IN-PLACE UPDATE-AT-KEY write (`keepWriteOpRot` — the
NARROWED rights onto the rotated AFTER cap-root limb), and the `granted ⊑ held` submask lookup. Guarded on
`sel.ATTENUATE_CAPABILITY = 48` (the FIRING selector), so var 264 is GENUINELY bound. -/
def attenuateV3 : EffectVmDescriptor2 :=
  v3OfWithCapWrite EffectVmEmitAttenuateA.attenuateVmDescriptorGenuineNoRecomputeTick
    [.mapOp (heldReadOpRot sel.ATTENUATE_CAPABILITY),
     .mapOp (keepWriteOpRot sel.ATTENUATE_CAPABILITY), .lookup submaskLookup]

/-- The rotated REVOKE-CAPABILITY (sel 24) WITH the cap-crown circuit leg, on the ROTATED-limb write path:
held-membership map read (`heldReadOpRot`) + the ZERO-value REMOVE-write (`removeWriteOpRot` — the slot deleted
on the rotated AFTER cap-root limb; NO submask — revoke deletes a slot, it does not narrow rights). Guarded on
`sel.REVOKE_CAPABILITY = 24` (the FIRING selector), so var 264 is GENUINELY bound. -/
def revokeCapabilityV3 : EffectVmDescriptor2 :=
  v3OfWithCapWrite EffectVmEmitAttenuateA.attenuateVmDescriptorGenuineNoRecomputeTick
    [.mapOp (heldReadOpRot sel.REVOKE_CAPABILITY),
     .mapOp (removeWriteOpRot sel.REVOKE_CAPABILITY)]

/-- The rotated DELEGATE (the unattenuated cross-vat grant) WITH the cap-crown circuit leg: the held
authority membership-read (REUSED `heldReadOp`) + the conferred-grant INSERT-write. The delegate base
IS the attenuate-A moving face (`delegateVmDescriptor := attenuateVmDescriptor`), whose `gCapMove` lets
`cap_root` move on-row; `insertWriteOp` FORCES that move to be the genuine sorted insert. NO submask
lookup — an unattenuated delegate confers the held edge as-is (the recipient's authority is bounded by
the delegator's held cap, authenticated by the membership read). -/
def delegateV3 : EffectVmDescriptor2 :=
  v3OfWithCapWrite EffectVmEmitAttenuateA.attenuateVmDescriptorGenuineNoRecomputeTick
    [.mapOp (anchorReadOpRot sel.GRANT_CAP), .mapOp (insertWriteOpRot sel.GRANT_CAP)]

/-- The rotated DELEGATE-ATTEN (the attenuated grant) WITH the cap-crown circuit leg: held-membership
read + the conferred (attenuated) INSERT-write + the submask lookup (`granted ⊑ held` — the
non-amplification tooth, REUSED from attenuate). Shares the moving attenuate-A face. -/
def delegateAttenV3 : EffectVmDescriptor2 :=
  v3OfWithCapWrite EffectVmEmitAttenuateA.attenuateVmDescriptorGenuineNoRecomputeTick
    [.mapOp (anchorReadOpRot sel.GRANT_CAP), .mapOp (insertWriteOpRot sel.GRANT_CAP),
     .lookup submaskLookup]

/-- The rotated GRANT-CAP (the bare cap grant) WITH the cap-crown circuit leg: held-membership read +
the conferred INSERT-write. Shares the moving attenuate-A face (the deployed grantCap base). -/
def grantCapWriteV3 : EffectVmDescriptor2 :=
  v3OfWithCapWrite EffectVmEmitAttenuateA.attenuateVmDescriptorGenuineNoRecomputeTick
    [.mapOp (anchorReadOpRot sel.GRANT_CAP), .mapOp (insertWriteOpRot sel.GRANT_CAP)]

/-! ### The FROZEN-FACE cap-family WRITE rebase (introduce / revokeDelegation) — guarantee A closed.

The triage (a93b40505) found the v1 faces of `introduce`/`revokeDelegation`/`refreshDelegation` FREEZE
`cap_root` on-row (`gCapPass`: `saCol CAP_ROOT = sbCol CAP_ROOT`), so the genuine cap-tree move rode only
an OFF-ROW prover-supplied `SpineCommits` hypothesis — a prover could publish a wrong post-cap-root
undetected. A `writesTo (sbCol CAP_ROOT) k v (saCol CAP_ROOT)` map-op is JOINTLY UNSAT with that freeze
for any genuine move, so these CANNOT close on the frozen face.

The close: rebase the V3 base onto the MOVING `…Genuine` face. `introduceVmDescriptorGenuine` and
`revokeVmDescriptorGenuine` are both DEFINITIONALLY `attenuateVmDescriptorGenuine` — the genuine cap-graph
face that DROPS the freeze (`gCapPass`) AND the opaque `gCapMove` (the `cap_root` move is FORCED by the
recompute sites, leaving `saCol CAP_ROOT` free to carry the genuine sorted write). With `cap_root` un-frozen,
the SAME `insertWriteOp` / `removeWriteOp` (mirroring `delegateV3` / `revokeCapabilityV3`) FORCE the post
cap-root to the genuine sorted insert / remove against the membership-opened before root.

These touch the CAP tree (introduce INSERTs `recDelegateCaps`, revokeDelegation REMOVEs `removeEdgeCaps` —
both move `caps`), so the cap-root write-op is the right primitive. `refreshDelegation` is NOT rebased here:
its move rides the `delegations` tree (the `DELEG` system-root), NOT `cap_root`, and that root has no in-row
map-ops-bound write column on the deployed wire — the genuine obstruction reported in
`RotatedKernelRefinementCapFamily.§3.5R`. -/

/-- The rotated INTRODUCE on the MOVING `introduceVmDescriptorGenuine` face (no `gCapPass` freeze) WITH the
cap-crown circuit leg: the held authority membership-read + the conferred-grant INSERT-write. The genuine
recompute frees `cap_root` to carry the move; `insertWriteOp` FORCES it to be the genuine sorted insert of
the conferred rights (`param[KEEP_MASK]`) at the new edge key (`param[CAP_KEY]`). NO submask lookup — an
introduce grants the held edge as-is (the recipient is bounded by the introducer's membership-read cap). -/
def introduceWriteV3 : EffectVmDescriptor2 :=
  v3OfWithCapWrite EffectVmEmitAttenuateA.attenuateVmDescriptorGenuineNoRecomputeTick
    [.mapOp (anchorReadOpRot sel.INTRODUCE), .mapOp (insertWriteOpRot sel.INTRODUCE)]

/-! ### §14.EPOCH — the revokeDelegation parent-epoch BUMP write-gate (the freshness-forgery close).

`revokeDelegation` does the FULL `apply_revoke_delegation`: the cap-edge `removeEdge` (the cap-tree
REMOVE `removeWriteOpRot` forces above) COMPOSED with the parent's `delegation_epoch += 1` (the
freshness-revocation tick — every child snapshot stamped at the OLD epoch is now stale). The committed
per-cell `delegation_epoch` rides the rotated limb `B_EPOCH = 30` (`compute_rotated_pre_limbs` `pre[30]`),
which `weldsAtNoCapRoot` does NOT weld and `rotateV3CapWrite` does NOT freeze — so on the deployed
descriptor it was a FREE witness limb that only FOLDS into the committed `state_commit`. A malicious
prover could publish a revoke whose committed AFTER epoch EQUALS the before (or is otherwise wrong): the
cap-edge is removed, the commitment binds the wrong epoch, and a ledgerless light client accepts a
revocation that did NOT stale the children — a FRESHNESS FORGERY (the named `RevokeDelegationEpochResidual`
clause `delegationEpoch += 1`).

`epochBumpGate sel beforeC afterC = sel · (loc afterC − loc beforeC − 1) = 0` CLOSES that on the live wire,
mirroring `discForceGate`/`permsVKWeldGate` (the disc / perms-VK selector-gated forces): on the ACTIVE
revoke row (`sel = 1`) it FORCES `loc afterC = loc beforeC + 1` (the committed AFTER epoch is exactly the
genuine BUMP of the committed BEFORE epoch); on a pad row (`sel = 0`) it vanishes. A revoke whose committed
AFTER epoch ≠ before+1 is now UNSAT for a ledgerless client — the freshness bump is in-circuit-forced. -/

/-- **`epochBumpGate sel beforeC afterC`** — the selector-gated epoch-BUMP force:
`sel · (loc afterC − loc beforeC − 1)`. On a row with `loc sel = 1` it forces the committed AFTER epoch
limb to be exactly `loc beforeC + 1` (the genuine revoke bump); on a pad row it vanishes. -/
def epochBumpGate (sel beforeC afterC : Nat) : VmConstraint :=
  .gate (.mul (.var sel) (.add (.add (.var afterC) (.mul (.const (-1)) (.var beforeC))) (.const (-1))))

theorem epochBumpGate_forces (env : VmRowEnv) (isFirst isLast : Bool) (hlast : isLast = false)
    (sel beforeC afterC : Nat)
    (hsel : env.loc sel = 1)
    (h : (epochBumpGate sel beforeC afterC).holdsVm env isFirst isLast) :
    env.loc afterC = env.loc beforeC + 1 := by
  subst hlast
  simp only [epochBumpGate, VmConstraint.holdsVm, EmittedExpr.eval] at h
  rw [hsel] at h
  linarith

/-- The rotated BEFORE-block `delegation_epoch` limb column (limb 30 of the before block at `base = w`). -/
def beforeEpochCol (w : Nat) : Nat := w + B_EPOCH

/-- The rotated AFTER-block `delegation_epoch` limb column (limb 30 of the after block at `base = w + 91`). -/
def afterEpochCol (w : Nat) : Nat := w + 91 + B_EPOCH

/-- The rotated REVOKE-DELEGATION on the MOVING `revokeVmDescriptorGenuine` face (no `gCapPass` freeze) WITH
the cap-crown circuit leg: held-membership read + the ZERO-value REMOVE-write (`removeWriteOp`, reused from
`revokeCapabilityV3` — revoke deletes a slot, NO submask) AND the §14.EPOCH parent-epoch BUMP gate
(`epochBumpGate` on the rotated `B_EPOCH = 30` limbs). The genuine recompute frees `cap_root`;
`removeWriteOp` FORCES the post root to the genuine sorted REMOVE (the ZERO sentinel write) at the revoked
edge key against the membership-opened before root, and `epochBumpGate` FORCES the committed AFTER epoch to
be the BEFORE epoch + 1 (the freshness tick that stales every child snapshot — the
`RevokeDelegationEpochResidual` `delegationEpoch += 1` clause, now in-circuit-forced). -/
def revokeDelegationWriteV3 : EffectVmDescriptor2 :=
  v3OfWithCapWrite EffectVmEmitAttenuateA.attenuateVmDescriptorGenuineNoRecomputeTick
    [.mapOp (heldReadOpRot sel.REVOKE_DELEGATION), .mapOp (removeWriteOpRot sel.REVOKE_DELEGATION),
     .base (epochBumpGate sel.REVOKE_DELEGATION
        (beforeEpochCol EFFECT_VM_WIDTH) (afterEpochCol EFFECT_VM_WIDTH))]

/-! ### The DELEGATIONS-tree WRITE op (refreshDelegation — the `DELEG` system-root move, in-circuit).

`refreshDelegation` is the ONE cap-graph effect whose genuine move is on the DELEGATIONS tree (the `DELEG`
system-root), NOT `caps`: `delegations := refreshDelegationsMap k child` is an in-place UPDATE-AT-KEY (the
child KEY stays present; the snapshot VALUE — the parent's c-list snapshot — moves). The §7 `DELEG`
system-root binds that move at the RECORD layer, but the WRITE itself was a prover-supplied `SpineCommits`
hypothesis (`delegRoot_runtime_column_pending`) — unanchored to any in-circuit write gate.

This op CLOSES that, mirroring the cap-tree write: the deleg accumulator rides the ROTATED before/after
limb (note-spend-shaped, witness-carried). refresh FREEZES `caps`, so the v1-state `cap_root` column (col
65/87) passes through continuously while the ROTATED cap-root limb (limb 25, freed from its weld by
`rotateV3CapWrite`) carries the DELEG before→after root. The `.write` op (insert-or-update — the same
`writesTo` the cap-update uses) FORCES the post DELEG-root to the genuine sorted update of the child's
snapshot (`param[KEEP_MASK]`, the recomputed snapshot digest) at the child key (`param[CAP_KEY]`) against
the membership-opened before DELEG-root. `writesTo` is FUNCTIONAL under CR — a forged post-deleg-root is
UNSAT. The limb folds into the rotated `wireCommitR` commitment, so the deleg WRITE is in-circuit-forced
instead of a supplied digest. -/

/-- The rotated BEFORE-block DELEG-root limb column. For refresh this rotated limb (limb 25, the
cap-root slot, freed from its v1-state weld by `rotateV3CapWrite`) carries the DELEGATIONS-tree PRE root —
refresh freezes `caps` on the v1 column, so the rotated limb is free to carry the deleg accumulator. -/
def beforeDelegRootCol (w : Nat) : Nat := beforeCapRootCol w

/-- The rotated AFTER-block DELEG-root limb column — the deleg-write op's `newRoot`, witness-carried
(no v1-state continuity), folding into the rotated state-commit. -/
def afterDelegRootCol (w : Nat) : Nat := afterCapRootCol w

/-- The child-key MEMBERSHIP read on the ROTATED before-block DELEG-root limb. The before DELEG-root
opens at the child key (`param[CAP_KEY]`) to the OLD snapshot (`param[HELD_MASK]`) — root unchanged (a
read). Refresh is an UPDATE-AT-KEY, so the child key is PRESENT; this read authenticates that and pairs
with the update-write at the SAME key (read+update consistent, the proven revoke-shaped template). -/
def delegReadOpRot (s : Nat) : MapOp :=
  { guard   := .var s
  , root    := .var (beforeDelegRootCol EFFECT_VM_WIDTH)
  , key     := .var (prmCol CAP_KEY)
  , value   := .var (prmCol HELD_MASK)
  , newRoot := .var (beforeDelegRootCol EFFECT_VM_WIDTH)
  , op      := .read }

/-- The refreshDelegation UPDATE-AT-KEY on the ROTATED DELEG-root limbs: the AFTER rotated DELEG-root IS
the GENUINE sorted update of the recomputed snapshot (`param[KEEP_MASK]`) at the child key
(`param[CAP_KEY]`) into the BEFORE rotated DELEG-root. `.write` is insert-or-update (key already present —
an overwrite), `writesTo` FUNCTIONAL under CR — a forged after-root is UNSAT. Note-spend-shaped: the
accumulator folds into the committed rotated state-commit, no v1-state continuity collision. -/
def delegUpdateWriteOpRot (s : Nat) : MapOp :=
  { guard   := .var s
  , root    := .var (beforeDelegRootCol EFFECT_VM_WIDTH)
  , key     := .var (prmCol CAP_KEY)
  , value   := .var (prmCol KEEP_MASK)
  , newRoot := .var (afterDelegRootCol EFFECT_VM_WIDTH)
  , op      := .write }

/-- The rotated REFRESH-DELEGATION on the MOVING genuine face (no `gCapPass` freeze — the rotated limb is
free to carry the deleg move) WITH the DELEG-tree circuit leg: the child-key membership-read + the
snapshot UPDATE-write. The genuine face frees the rotated cap-root limb; `delegUpdateWriteOpRot` FORCES it
to be the genuine sorted update of the child's snapshot at the child key against the membership-opened
before DELEG-root. The v1-state `cap_root` column stays FROZEN (refresh's `caps` unchanged); the DELEG
WRITE is now in-circuit-forced (no longer the `delegRoot_runtime_column_pending` supplied digest). NO
submask — refresh re-arms an existing delegation (`granted = held`, non-amplification reflexive). -/
def refreshDelegationWriteV3 : EffectVmDescriptor2 :=
  v3OfWithCapWrite EffectVmEmitAttenuateA.attenuateVmDescriptorGenuineNoRecomputeTick
    [.mapOp (delegReadOpRot sel.REFRESH_DELEGATION),
     .mapOp (delegUpdateWriteOpRot sel.REFRESH_DELEGATION)]

/-- The rotated dynamic setField WITH its memory ops (the Blum write→read transport). -/
def setFieldDynV3 : EffectVmDescriptor2 :=
  v3OfWith setFieldDynV1Face [.memOp fieldWriteOp, .memOp fieldReadbackOp]

/-- **The VK-epoch PI exposure for the rotated Custom member.** Eight `.piBinding .first`
constraints publishing the `proofBind` op's bound columns as PUBLIC INPUTS of the descriptor:
the four `custom_proof_commitment` limbs (`prmCol (CUSTOM_COMMIT + k)` = cols 72..75) at IR2 PI
slots `46..49` (the first slots past the four rotated commit pins, `rotateV3` produces
`piCount = 46`), and the four low `custom_program_vk_hash` limbs (`prmCol (CUSTOM_VK + k)` =
cols 68..71) at slots `50..53`, all pinned on the FIRST (the lead Custom) row — the row the
`generate_rotated_custom_wide` generator lays the bound `(vk, commit)` on. Exposing these
columns as PIs is THE change that lets the per-turn FOLD connect the custom sub-proof leaf's
4-felt PI-commitment to the descriptor: the binding (a verifying sub-proof of `E` whose PI
commitment EQUALS this column) is enforced at the FOLD via these PIs + the custom-leaf recursion
(`StarkSoundCustom` / `EngineBinding`, the Lean model in `CustomApex`, axiom-clean), NOT by a
row-local in-AIR gate — so the per-row `proofBind` denotation stays `True` like `memOp`/`umemOp`
(`DescriptorIR2.VmConstraint2.holdsAt`). The full 8-felt `vk_hash` is carried by the wide host
PI (`pi.rs::CUSTOM_PROOFS_BASE`) / the turn hash; the descriptor exposes only the four vk-hash
limbs that exist as trace columns (`columns.rs::CUSTOM_VK_HASH_BASE = 4 elements`). -/
def customPiExposure : List VmConstraint2 :=
  (List.range 4).map (fun k =>
    .base (.piBinding .first (prmCol (CUSTOM_COMMIT + k)) (46 + k)))
  ++ (List.range 4).map (fun k =>
    .base (.piBinding .first (prmCol (CUSTOM_VK + k)) (50 + k)))

/-- The rotated CUSTOM (sel 8) WITH the recursive-proof-binding leg: the runtime passthrough face
lifted through `rotateV3`, carrying the `proofBind` op (`customProofBind`) that ties the row's
`custom_proof_commitment` to a verifying external sub-proof — the accumulator constraint the
per-row IR gained — PLUS (the VK epoch) the eight `customPiExposure` PI bindings that publish the
bound `(commit, vk)` columns so the per-turn FOLD can connect the custom sub-proof leaf. The
`proofBind` row gate stays `True`; the binding is enforced at the fold (see `customPiExposure`).
This is THE last rotation-cohort member: with it the HONEST RESIDUE is EMPTY. -/
def customV3 : EffectVmDescriptor2 :=
  let d := v3OfWith customV1Face [.proofBind customProofBind]
  { d with
    piCount     := d.piCount + 8
    constraints := d.constraints ++ customPiExposure }

/-! ### The note-spend nullifier PI weld (the C4 last-flip-gate close).

The v1 hand-AIR (`circuit/src/effect_vm/air.rs`, D5) carries a per-row GATED cross-binding
`s_notespend · (param0 − PI[NOTESPEND_NULLIFIER])` (offset 198): the spend row's folded
nullifier (`param::NULLIFIER = param0`, column `prmCol 0`) MUST equal the published
`PI[198]` — the weld that forbids the EffectVM from spending a different nullifier than the
one the SCHEMA_NOTE_SPEND binding proof certified (the off-AIR verifier reconstructs PI[198]
from the binding proof's `fields[0]` and `verify_full_turn` step 8 cross-checks the
non-revocation proof's queried item == PI[198]).

That cross-binding tooth lives ONLY in the v1 hand-AIR — `noteSpendVmDescriptor` (the Lean
per-effect descriptor) does NOT bind the nullifier to any PI (its `piCount = 42` is the v1
prefix only). So when the rotated leg retires the hand-AIR, the rotated 46-PI omits the
nullifier and a note-spending turn with a freshness binding CANNOT rotate (it falls back to
v1 — the documented C4 boundary, `verify_full_turn` step 8 REFUSES the rotated leg).

`noteSpendV3` CLOSES that gate: it appends a FIFTH PI pin past the four rotated commit pins
(`rotateV3` produces `piCount = 42 + 4 = 46`), binding the spend row's `param0` (the folded
nullifier) to the new rotated PI slot 46 on the FIRST row. The note-spend turn lays the spend
on row 0 (`generate_effect_vm_trace`'s `Effect::NoteSpend` arm + the trace generator's
`row[PARAM_BASE + param::NULLIFIER]` write are on row 0; `boundaryFirstPins` pins the first
row), so the first-row pin is the rotated analog of the v1 per-row gate. The SOUNDNESS TOOTH
(`noteSpendV3_rejects_nullifier_tamper`): a row whose `param0` differs from the published
PI[46] FAILS the pin and is UNSAT — exactly the v1 `rejects_swap` adversarial test, now at the
rotated boundary. The Rust `verify_full_turn` step 8 reads PI[46] of the rotated leg instead
of refusing, so the no-double-spend cross-check (`queried_item == nullifier`) fires on the
rotated note-spend turn. -/

/-- The rotated nullifier-PI slot: the FIRST slot past the four rotated commit pins
(`rotateV3` appends OLD/NEW commit · height · caveat commit at `piCount..piCount+3`). For the
note-spend cohort member this is `42 + 4 = 46`. -/
def ROT_NULLIFIER_PI : Nat := 46

/-- The folded-nullifier parameter column (`param::NULLIFIER = param0`, `prmCol 0`) — the
spend row's single folded `fold_bytes32_to_bb(nullifier)` felt the v1 hand-AIR cross-binds. -/
def NULLIFIER_PARAM_COL : Nat := prmCol 0

/-- **`rotateV3WithNullifierPin`** — `rotateV3` PLUS the fifth appended PI pin welding the
spend row's folded nullifier (`prmCol 0`) to the rotated PI slot `ROT_NULLIFIER_PI = 38` on
the FIRST row. Every v1 column, constraint, hash site, and the four rotated commit pins are
UNTOUCHED (so `rotateV3`'s keystones — `rotateV3_satisfiedVm_v1`, `rotV3_binds_published`,
`graduable_rotateV3` — all compose verbatim; this only ADDS one PI pin + one PI slot). -/
def rotateV3WithNullifierPin (d : EffectVmDescriptor) : EffectVmDescriptor :=
  let r := rotateV3 d
  { r with
    piCount     := r.piCount + 1
    constraints := r.constraints ++ [.piBinding .first NULLIFIER_PARAM_COL ROT_NULLIFIER_PI] }

/-! ## §5.FEE — the FEE PI weld (trust-surface hole #5: the fee debit becomes a proven balance
constraint, bound to a published PI on the deployed wire).

`EffectVmEmitTransfer.transferFeeVmDescriptor` augments the balance-lo gate to debit the fee from
the after-block `RESERVED` state column (`feeCol = saCol state.RESERVED`), so the proven FINAL_BAL
(bound into NEW_COMMIT) is the POST-fee balance. But the fee column is a witness the prover CHOOSES
— the in-circuit gate forces `new = old − transfer − fee` for SOME fee, not the verifier's
`turn.fee`. `rotateV3WithFeePin` closes that: it pins the fee column to a published PI on the LAST
row, so the verifier's `turn.fee` is FORCED equal to the balance the proof actually moved. A proof
claiming a smaller fee PI than the balance moved is then UNSAT — no trusted reconstruction. -/

/-- The rotated fee-PI slot: the FIRST slot past the four rotated commit pins (`rotateV3` appends
OLD/NEW commit · height · caveat commit at `piCount..piCount+3`). For the transfer cohort member
this is `42 + 4 = 46` — the same arithmetic as `ROT_NULLIFIER_PI` (transfer and note-spend never
co-occur on one descriptor, so sharing the slot index is sound). -/
def ROT_FEE_PI : Nat := 46

/-- The fee column (the after-block `RESERVED` state limb of the v1 sub-trace). The v1 columns sit
at fixed offsets inside `[0, EFFECT_VM_WIDTH)`, so this is `traceWidth`-independent. -/
def FEE_COL : Nat := EffectVmEmitTransfer.feeCol

/-- **`rotateV3WithFeePin`** — a rotated descriptor PLUS the fifth appended PI pin welding the fee
column (`feeCol = saCol state.RESERVED`, carrying the debited fee) to the rotated PI slot
`ROT_FEE_PI = 38` on the LAST row (the after-block carries the post-fee balance, so the fee pin is a
last-row pin — the rotated analog of the boundary-last balance pins). `base` is a `rotateV3` /
`rotateV3FrozenAuthority` form; every v1 column, constraint, hash site, and the four rotated commit
pins are UNTOUCHED, so the keystones compose verbatim; this only ADDS one PI pin + one PI slot. -/
def rotateV3WithFeePin (base : EffectVmDescriptor) : EffectVmDescriptor :=
  { base with
    piCount     := base.piCount + 1
    constraints := base.constraints ++ [.piBinding .last FEE_COL ROT_FEE_PI] }

-- `transferFeeV3` (the graduated frozen-authority + fee-pinned descriptor) is defined AFTER
-- `rotateV3FrozenAuthority` (§near `v3OfFrozen`), since the freeze helper appears later in this file.

/-- The rotated BEFORE-block `nullifier_root` limb column (limb 26 of the before block at
`base = traceWidth`). The deployed nullifier accumulator's PRE root — the openable
sorted-Poseidon2 root the grow-gate opens against. -/
def beforeNullifierRootCol (w : Nat) : Nat := w + 26

/-- The rotated AFTER-block `nullifier_root` limb column (limb 26 of the after block at
`base = traceWidth + 91`). The deployed nullifier accumulator's POST root — the grow-gate's
`newRoot`. -/
def afterNullifierRootCol (w : Nat) : Nat := w + 91 + 26

/-! ## §5.N — the noteSpend KERNEL-SET GROW-GATE (the deployment-real set-insert + double-spend
tooth).

`RotatedKernelRefinementNotesFresh.lean` proves, against a MODELED nullifier tree, that a
non-membership open (`GapOpen`/`opensTo … none`) FORCES `nf ∉ pre.nullifiers` and a set-insert
gate FORCES `post.nullifiers = nf :: pre.nullifiers`. Until now the DEPLOYED rotated descriptor
carried `nullifier_root` (limb 26) as a TURN-INVARIANT witness limb (before == after; no gate),
so `kernel_set_insert_is_not_forced_by_the_live_descriptor` proved a frozen/forged nullifier
root still verifies.

These two `MapOp`s CLOSE that on the live wire — the EXISTING IR-v2 map-ops machinery (the same
the cap-crown attenuate write rides) is the row-level grow-gate the negative test claimed the
per-row IR "cannot express":

  * **`nullifierFreshOp`** (`.absent`) — the in-circuit DOUBLE-SPEND tooth: the published
    nullifier `param0` is NON-MEMBER of the BEFORE nullifier tree (limb 26). Under CR
    (`opensTo_none_of_gap` / the gap bracketing) this is the deployed face of the Lean
    `GapOpen` the `NotesFresh` rung consumes; a double-spend (`nf` already present) has no
    bracketing witness and is UNSAT.
  * **`nullifierInsertOp`** (`.insert`) — the SET-INSERT: the AFTER nullifier root (limb 26 of
    the after block) IS the genuine sorted insert of `param0` into the BEFORE root. Under CR
    (`writesTo_functional`) the after-root column cannot be frozen or forged — it is pinned to
    the real grown tree. This is the deployed face of `gNoteGrow`.

Both gated by the noteSpend selector (`SEL_NOTE_SPEND = 4`), so non-spend / NoOp pad rows (where
the selector is 0) contribute nothing. The published nullifier `param0` (`NULLIFIER_PARAM_COL`)
is ALREADY the spend row's folded nullifier (cross-bound to PI[46] by `rotateV3WithNullifierPin`),
so the gate's key IS the same nullifier the apex reads. -/

/-- The DOUBLE-SPEND tooth (the deployed `GapOpen` face): the published nullifier `param0` is a
NON-MEMBER of the BEFORE nullifier tree (limb 26); the root is unchanged by an absent read. -/
def nullifierFreshOp : MapOp :=
  { guard   := .var EffectVmEmitNoteSpend.SEL_NOTE_SPEND
  , root    := .var (beforeNullifierRootCol EFFECT_VM_WIDTH)
  , key     := .var NULLIFIER_PARAM_COL
  , value   := .const 0
  , newRoot := .var (beforeNullifierRootCol EFFECT_VM_WIDTH)
  , op      := .absent }

/-- The SET-INSERT (the deployed `gNoteGrow` face): the AFTER nullifier root (limb 26 of the
after block) IS the genuine sorted write of `param0` into the BEFORE root. The note value
(`param::NOTE_VALUE_LO`) rides as the leaf value so a spent nullifier carries its note datum. -/
def nullifierInsertOp : MapOp :=
  { guard   := .var EffectVmEmitNoteSpend.SEL_NOTE_SPEND
  , root    := .var (beforeNullifierRootCol EFFECT_VM_WIDTH)
  , key     := .var NULLIFIER_PARAM_COL
  , value   := .var (prmCol EffectVmEmitNoteSpend.param.NOTE_VALUE_LO)
  , newRoot := .var (afterNullifierRootCol EFFECT_VM_WIDTH)
  , op      := .insert }

/-- **`noteSpendV3`** — the rotated note-spend WITH the nullifier PI weld AND the KERNEL-SET
GROW-GATE (the deployment-real set-insert + double-spend tooth). `piCount = 39` (the 38-PI
rotated prefix + the appended nullifier slot). Past the graduated `rotateV3WithNullifierPin`
descriptor, it appends the two map-ops that FORCE the nullifier set-insert on the live wire:
`nullifierFreshOp` (the `.absent` double-spend tooth — `nf ∉ pre`) and `nullifierInsertOp` (the
`.insert` set-insert — `after_root = insert(before_root, nf)`). These repoint limb 26 from a
turn-invariant witness limb into a FORCED, grown, fresh nullifier root. -/
def noteSpendV3 : EffectVmDescriptor2 :=
  let base := graduateV1 (rotateV3WithNullifierPin EffectVmEmitNoteSpend.noteSpendVmDescriptor)
  { base with
    constraints := base.constraints ++ [.mapOp nullifierFreshOp, .mapOp nullifierInsertOp] }

/-- **`noteSpendV3_grow_gate_forces_set_insert` — the live descriptor FORCES the nullifier
set-insert + freshness (the deployment-real tooth).** On a satisfying `noteSpendV3` witness whose
spend selector fires, the two appended map-ops hold: (1) the published nullifier is ABSENT from
the BEFORE nullifier tree (limb 26) — the in-circuit double-spend tooth (`opensTo … none`); and
(2) the AFTER nullifier root IS the genuine sorted insert of that nullifier into the BEFORE root
(`writesTo`). Under CR these are FUNCTIONAL (`opensTo_functional` / `writesTo_functional`), so a
frozen or forged after-root, or a double-spent (present) nullifier, cannot satisfy the descriptor
— exactly the forgery `kernel_set_insert_is_not_forced_by_the_live_descriptor` documented, now
REJECTED. The map-ops are the deployed faces of the `NotesFresh` `GapOpen` (`.absent`) and
`gNoteGrow` (`.insert`). -/
theorem noteSpendV3_grow_gate_forces_set_insert (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash noteSpendV3 minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length)
    (hspend : (envAt t i).loc EffectVmEmitNoteSpend.SEL_NOTE_SPEND = 1) :
    -- (1) the double-spend tooth: the published nullifier is absent from the BEFORE tree.
    (opensTo hash ((envAt t i).loc (beforeNullifierRootCol EFFECT_VM_WIDTH))
        ((envAt t i).loc NULLIFIER_PARAM_COL) none)
    -- (2) the set-insert: the AFTER root is the genuine sorted write of the nullifier.
    ∧ writesTo hash ((envAt t i).loc (beforeNullifierRootCol EFFECT_VM_WIDTH))
        ((envAt t i).loc NULLIFIER_PARAM_COL)
        ((envAt t i).loc (prmCol EffectVmEmitNoteSpend.param.NOTE_VALUE_LO))
        ((envAt t i).loc (afterNullifierRootCol EFFECT_VM_WIDTH)) := by
  have hrowc := hsat.rowConstraints i hi
  have hfresh := hrowc (.mapOp nullifierFreshOp) (by simp [noteSpendV3])
  have hins := hrowc (.mapOp nullifierInsertOp) (by simp [noteSpendV3])
  -- the map-op denotations fire under the spend selector (`SEL_NOTE_SPEND = 1`).
  have ha := hfresh hspend
  have hw := hins hspend
  exact ⟨ha.1, hw⟩

/-- The appended pin is the only constraint past `rotateV3`'s, and it targets the new slot. -/
theorem rotateV3WithNullifierPin_constraints (d : EffectVmDescriptor) :
    (rotateV3WithNullifierPin d).constraints
      = (rotateV3 d).constraints
        ++ [.piBinding .first NULLIFIER_PARAM_COL ROT_NULLIFIER_PI] := rfl

/-- The nullifier pin does NOT disturb graduation: the hash sites and ranges are `rotateV3`'s
verbatim (the pin is a CONSTRAINT, and `graduable` reads only sites/ranges). -/
theorem graduable_rotateV3WithNullifierPin {d : EffectVmDescriptor}
    (h : graduable d = true) : graduable (rotateV3WithNullifierPin d) = true := by
  have hr := graduable_rotateV3 h
  unfold rotateV3WithNullifierPin
  unfold graduable at hr ⊢
  -- `rotateV3WithNullifierPin` shares `rotateV3 d`'s hashSites + ranges exactly.
  simpa using hr

/-- **The nullifier weld holds on a satisfying first row**: a row satisfying `noteSpendV3`
carries the spend row's folded nullifier (`prmCol 0`) EQUAL to the published rotated PI[46].
This is the rotated re-statement of the v1 D5 cross-binding (`param0 == PI[NOTESPEND_NULLIFIER]`),
now a first-row pin of the rotated descriptor. -/
theorem noteSpendV3_pins_nullifier (hash : List ℤ → ℤ)
    (env : VmRowEnv) (isLast : Bool)
    (h : satisfiedVm hash (rotateV3WithNullifierPin
      EffectVmEmitNoteSpend.noteSpendVmDescriptor) env true isLast) :
    env.loc NULLIFIER_PARAM_COL = env.pub ROT_NULLIFIER_PI := by
  have hpin := h.1 (.piBinding .first NULLIFIER_PARAM_COL ROT_NULLIFIER_PI)
    (by rw [rotateV3WithNullifierPin_constraints]; exact List.mem_append_right _ List.mem_cons_self)
  simpa only [VmConstraint.holdsVm] using hpin rfl

/-- **ANTI-GHOST (nullifier tamper ⇒ UNSAT)** — the C4 soundness tooth. A first row whose
folded nullifier `param0` does NOT equal the published rotated PI[46] does NOT satisfy
`noteSpendV3`: the appended pin REJECTS it. This is the rotated boundary's analog of the v1
`test_notespend_nullifier_cross_binding_rejects_swap` ("prove N, spend M" ⇒ STARK rejects):
the rotated leg can no longer publish a nullifier different from the one the spend row carries,
so the off-row freshness cross-check (`verify_full_turn` step 8) binds THIS turn's nullifier. -/
theorem noteSpendV3_rejects_nullifier_tamper (hash : List ℤ → ℤ)
    (env : VmRowEnv) (isLast : Bool)
    (htamper : env.loc NULLIFIER_PARAM_COL ≠ env.pub ROT_NULLIFIER_PI) :
    ¬ satisfiedVm hash (rotateV3WithNullifierPin
      EffectVmEmitNoteSpend.noteSpendVmDescriptor) env true isLast :=
  fun h => htamper (noteSpendV3_pins_nullifier hash env isLast h)

/-- The v1 denotation still survives the added pin (the per-effect noteSpend faithfulness /
anti-ghost theorems compose through, exactly as for bare `rotateV3`). -/
theorem noteSpendV3_satisfiedVm_v1 (hash : List ℤ → ℤ)
    (env : VmRowEnv) (isFirst isLast : Bool)
    (h : satisfiedVm hash (rotateV3WithNullifierPin
      EffectVmEmitNoteSpend.noteSpendVmDescriptor) env isFirst isLast) :
    satisfiedVm hash EffectVmEmitNoteSpend.noteSpendVmDescriptor env isFirst isLast := by
  apply rotateV3_satisfiedVm_v1 hash EffectVmEmitNoteSpend.noteSpendVmDescriptor env isFirst isLast
  -- `rotateV3WithNullifierPin` = `rotateV3` with one extra constraint + the same sites; a
  -- satisfier of the former satisfies the latter (constraints are a superset, sites identical).
  obtain ⟨hc, hsites, hr⟩ := h
  refine ⟨fun c hc' => hc c ?_, hsites, hr⟩
  rw [rotateV3WithNullifierPin_constraints]
  exact List.mem_append_left _ hc'

#assert_axioms graduable_rotateV3WithNullifierPin
#assert_axioms noteSpendV3_pins_nullifier
#assert_axioms noteSpendV3_rejects_nullifier_tamper
#assert_axioms noteSpendV3_satisfiedVm_v1

-- The nullifier pin lands at PI slot 46 (one past the four rotated commit pins 34..37) and
-- the rotated note-spend publishes 39 PIs.
#guard ROT_NULLIFIER_PI == 42 + 4
#guard NULLIFIER_PARAM_COL == 68          -- PARAM_BASE (54+14) + param::NULLIFIER (0)
#guard noteSpendV3.piCount == 47
#guard (rotateV3WithNullifierPin EffectVmEmitNoteSpend.noteSpendVmDescriptor).piCount == 47
-- Graduation survives the appended pin.
#guard graduable (rotateV3WithNullifierPin EffectVmEmitNoteSpend.noteSpendVmDescriptor)
-- The rotated commit pins are UNDISTURBED at 34..37 (the fifth pin is strictly appended);
-- `noteSpendV3` carries the four rotated commit pins PLUS one more PI pin (the nullifier weld)
-- PLUS the two KERNEL-SET grow-gate map-ops (`nullifierFreshOp` `.absent` + `nullifierInsertOp`
-- `.insert` — the deployment-real set-insert + double-spend tooth) = +3 constraints in total.
#guard noteSpendV3.constraints.length == (v3Of EffectVmEmitNoteSpend.noteSpendVmDescriptor).constraints.length + 1 + 2
-- The grow-gate map-ops ARE present on `noteSpendV3` (the live wire now carries the set-insert).
#guard (mapOpsOf noteSpendV3).length == 2
-- BOTH POLARITIES of the soundness tooth, executable on the toy environment: a row whose
-- param0 equals PI[46] PASSES the pin; a tampered one FAILS it. (`decEnv` toy: param col 68
-- carries `n`, PI 46 carries `p`.)
#guard (let env : VmRowEnv := ⟨fun c => if c == 68 then 5 else 0, fun _ => 0, fun k => if k == 46 then 5 else 0⟩;
        decide (env.loc NULLIFIER_PARAM_COL = env.pub ROT_NULLIFIER_PI))   -- match ⇒ pin holds
#guard (let env : VmRowEnv := ⟨fun c => if c == 68 then 5 else 0, fun _ => 0, fun k => if k == 46 then 9 else 0⟩;
        decide (env.loc NULLIFIER_PARAM_COL ≠ env.pub ROT_NULLIFIER_PI))   -- mismatch ⇒ pin REJECTS

/-! ## §5.NC — the noteCreate KERNEL-SET GROW-GATE (the deployment-real COMMITMENTS set-insert).

The `commitments_root` flag-day limb (in-block offset `B_COMMITMENTS_ROOT = 27`, the NEW committed
shielded-set root the widening NUM_PRE_LIMBS 31→32 added) gives the note COMMITMENT set a committed
home. Before the widening there was NO `commitments_root` limb at all, so
`kernel_set_insert_is_not_forced_by_the_live_descriptor` proved a noteCreate turn whose commitments
set was NOT grown still verified — the ONE remaining named residual of the kernel-set family.

This `MapOp` CLOSES it on the live wire, CLONING the noteSpend grow-gate onto limb 27. `NoteCreate`
is append-only (`NoteCreateASpec` has NO guard — `noteCreateAdmit = True`), so unlike noteSpend there
is NO freshness `.absent` tooth: just the SET-INSERT. The inserted KEY is the published note
commitment `param0` (`generate_effect_vm_trace`'s `Effect::NoteCreate` arm lays
`param0 = commitment`), cross-bound to a published PI slot by `rotateV3WithCommitmentKeyPin` so the
apex reads the SAME commitment the gate forces:

  * **`commitmentsInsertOp`** (`.insert`) — the SET-INSERT (the deployed `gNoteGrow` face): the
    AFTER commitments root (limb 27 of the after block) IS the genuine sorted insert of `param0`
    into the BEFORE root. Under CR (`writesTo_functional`) the after-root column cannot be frozen or
    forged — it is pinned to the real grown commitments tree. This is the deployed realization of
    `RotatedKernelRefinementNotes.noteCreate_commitments_forced` against the NOW-LIVE limb 27.

Gated by the noteCreate selector (`SEL_NOTE_CREATE = 5`), so non-create / NoOp pad rows contribute
nothing. The note value (`param::NOTE_VALUE_LO = param1`) rides as the leaf value so a created
commitment carries its note datum. -/

/-- The rotated published-PI slot the note commitment (`param0`) welds to — the FIRST slot past the
four rotated commit pins (`piCount = 42 + 4 = 46`), the same arithmetic as `ROT_NULLIFIER_PI`
(noteCreate and noteSpend never co-occur on one row, so sharing slot 46 is sound). -/
def ROT_COMMITMENT_KEY_PI : Nat := 46

/-- The note-commitment key parameter column (`param0`, `prmCol 0`) — the noteCreate row's
single published note-commitment felt (`Effect::NoteCreate { commitment }` ⇒ `row[PARAM_BASE+0]`). -/
def COMMITMENT_KEY_PARAM_COL : Nat := prmCol 0

/-- The rotated BEFORE-block `commitments_root` limb column (limb 27 of the before block at
`base = traceWidth`). The deployed commitments accumulator's PRE root. -/
def beforeCommitmentsRootCol (w : Nat) : Nat := w + B_COMMITMENTS_ROOT

/-- The rotated AFTER-block `commitments_root` limb column (limb 27 of the after block at
`base = traceWidth + 91`). The deployed commitments accumulator's POST root — the grow-gate's
`newRoot`. -/
def afterCommitmentsRootCol (w : Nat) : Nat := w + 91 + B_COMMITMENTS_ROOT

/-- **`rotateV3WithCommitmentKeyPin`** — `rotateV3` PLUS the fifth appended PI pin welding the note
commitment (`prmCol 0`) to `ROT_COMMITMENT_KEY_PI = 38` on the FIRST row. Structurally identical to
`rotateV3WithNullifierPin`; every v1 column/constraint/site and the four rotated commit pins are
UNTOUCHED. -/
def rotateV3WithCommitmentKeyPin (d : EffectVmDescriptor) : EffectVmDescriptor :=
  let r := rotateV3 d
  { r with
    piCount     := r.piCount + 1
    constraints := r.constraints ++ [.piBinding .first COMMITMENT_KEY_PARAM_COL ROT_COMMITMENT_KEY_PI] }

/-- The SET-INSERT: the AFTER commitments root (limb 27 of the after block) IS the genuine sorted
write of the note commitment (`param0`) into the BEFORE root, with the note value (`param1`) as the
leaf value. Guarded by the noteCreate selector. -/
def commitmentsInsertOp : MapOp :=
  { guard   := .var EffectVmEmitNoteCreate.SEL_NOTE_CREATE
  , root    := .var (beforeCommitmentsRootCol EFFECT_VM_WIDTH)
  , key     := .var COMMITMENT_KEY_PARAM_COL
  , value   := .var (prmCol EffectVmEmitNoteCreate.param.NOTE_VALUE_LO)
  , newRoot := .var (afterCommitmentsRootCol EFFECT_VM_WIDTH)
  , op      := .insert }

/-- **`noteCreateV3`** — the rotated noteCreate WITH the commitment PI weld AND the KERNEL-SET
GROW-GATE (the deployment-real commitments set-insert). `piCount = 39`. Past the graduated
`rotateV3WithCommitmentKeyPin` descriptor it appends the one map-op that FORCES the commitment
set-insert on the live wire (`commitmentsInsertOp .insert`), repointing limb 27 from a turn-invariant
witness limb into a FORCED, grown commitments root. NoteCreate is append-only — there is no `.absent`
freshness tooth (`NoteCreateASpec` has no guard), so the gate is the single insert. -/
def noteCreateV3 : EffectVmDescriptor2 :=
  let base := graduateV1 (rotateV3WithCommitmentKeyPin EffectVmEmitNoteCreate.noteCreateVmDescriptor)
  { base with
    constraints := base.constraints ++ [.mapOp commitmentsInsertOp] }

/-- **`noteCreateV3_grow_gate_forces_set_insert` — the live descriptor FORCES the commitment
set-insert (the deployment-real tooth).** On a satisfying `noteCreateV3` witness whose create
selector fires, the appended map-op holds: the AFTER commitments root (limb 27 of the after block)
IS the genuine sorted insert of the published note commitment (`param0`) into the BEFORE root
(`writesTo`). Under CR this is FUNCTIONAL (`writesTo_functional`), so a frozen or forged after-root
cannot satisfy the descriptor — exactly the forgery
`kernel_set_insert_is_not_forced_by_the_live_descriptor` documented as the noteCreate residual, now
REJECTED. The map-op is the deployed face of
`RotatedKernelRefinementNotes.noteCreate_commitments_forced` against the live limb 27. -/
theorem noteCreateV3_grow_gate_forces_set_insert (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash noteCreateV3 minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length)
    (hcreate : (envAt t i).loc EffectVmEmitNoteCreate.SEL_NOTE_CREATE = 1) :
    writesTo hash ((envAt t i).loc (beforeCommitmentsRootCol EFFECT_VM_WIDTH))
        ((envAt t i).loc COMMITMENT_KEY_PARAM_COL)
        ((envAt t i).loc (prmCol EffectVmEmitNoteCreate.param.NOTE_VALUE_LO))
        ((envAt t i).loc (afterCommitmentsRootCol EFFECT_VM_WIDTH)) := by
  have hrowc := hsat.rowConstraints i hi
  have hins := hrowc (.mapOp commitmentsInsertOp) (by simp [noteCreateV3])
  exact hins hcreate

#assert_axioms noteCreateV3_grow_gate_forces_set_insert

-- The commitment pin lands at PI slot 46; the rotated noteCreate publishes 39 PIs and carries the
-- single grow-gate map-op on the new commitments_root limb (27).
#guard ROT_COMMITMENT_KEY_PI == 42 + 4
#guard COMMITMENT_KEY_PARAM_COL == 68
#guard noteCreateV3.piCount == 47
#guard (mapOpsOf noteCreateV3).length == 1
#guard beforeCommitmentsRootCol EFFECT_VM_WIDTH == EFFECT_VM_WIDTH + 27
#guard afterCommitmentsRootCol EFFECT_VM_WIDTH == EFFECT_VM_WIDTH + 91 + 27

/-! ## §5.C — the createCell / factory / spawn KERNEL-SET GROW-GATE (the deployment-real
ACCOUNTS set-insert).

`cells_root` (rotated limb 0) is ALREADY an openable sorted-Poseidon2 root, but — exactly as
limb 26 was for noteSpend before §5.N — the createCell/factory/spawn descriptors carried it as a
TURN-INVARIANT witness limb (before == after; no gate), so
`kernel_set_insert_is_not_forced_by_the_live_descriptor` proved a frozen/forged cells_root still
verifies and the new cell's account-set growth was unwitnessed (`createCell_offrow_unenforced`).

These two `MapOp`s CLOSE that on the live wire, CLONING the noteSpend grow-gate onto limb 0. The
inserted KEY is the new-cell identity `param0` (`Effect::CreateCell { create_hash }` ⇒
`row[PARAM_BASE+0] = create_hash[0]`; the spawn/factory child-id likewise lands in `param0`),
cross-bound to a published PI slot by `rotateV3WithNewCellKeyPin` so the apex reads the SAME key
the gate forces:

  * **`cellsFreshOp`** (`.absent`) — the FRESHNESS tooth: the new-cell key `param0` is a
    NON-MEMBER of the BEFORE cells tree (limb 0). A re-creation of an existing cell id has no
    bracketing witness and is UNSAT (no account-id collision).
  * **`cellsInsertOp`** (`.insert`) — the SET-INSERT: the AFTER cells root (limb 0 of the after
    block) IS the genuine sorted insert of `param0` into the BEFORE root. Under CR
    (`writesTo_functional`) the after-root column cannot be frozen or forged — it is pinned to the
    real grown accounts tree.

The gate is guarded per-effect by the runtime selector (createCell `31`, factory `13`, spawn `32`),
so non-matching / NoOp pad rows contribute nothing. spawn's cap-handoff (the child cap-root MOVE +
delegation snapshot) is ORTHOGONAL to this accounts-set insert — it rides spawn's existing
`gCapMove`/delegation legs and is NOT closed here (the named spawn residual). -/

/-- The rotated published-PI slot the new-cell key (`param0`) welds to — the FIRST slot past the
four rotated commit pins (`piCount = 42 + 4 = 46`), the same arithmetic as `ROT_NULLIFIER_PI`
(these descriptors and noteSpend never co-occur on one row, so sharing slot 46 is sound). -/
def ROT_NEW_CELL_KEY_PI : Nat := 46

/-- The new-cell key parameter column (`param0`, `prmCol 0`) — the create/factory/spawn row's
single folded new-cell identity felt (`create_hash[0]`). -/
def NEW_CELL_KEY_PARAM_COL : Nat := prmCol 0

/-- The rotated BEFORE-block `cells_root` limb column (limb 0 of the before block at
`base = traceWidth`). The deployed accounts accumulator's PRE root — the openable
sorted-Poseidon2 root the grow-gate opens against. -/
def beforeCellsRootCol (w : Nat) : Nat := w + 0

/-- The rotated AFTER-block `cells_root` limb column (limb 0 of the after block at
`base = traceWidth + 91`). The deployed accounts accumulator's POST root — the grow-gate's
`newRoot`. -/
def afterCellsRootCol (w : Nat) : Nat := w + 91 + 0

/-- **`rotateV3WithNewCellKeyPin`** — `rotateV3` PLUS the fifth appended PI pin welding the
new-cell key (column `keyCol`) to `ROT_NEW_CELL_KEY_PI = 38` on the FIRST row. Structurally identical
to `rotateV3WithNullifierPin`; every v1 column/constraint/site and the four rotated commit pins are
UNTOUCHED. `keyCol` is `param0` for createCell/spawn, `param1` (the derived child VK) for factory. -/
def rotateV3WithNewCellKeyPin (keyCol : Nat) (d : EffectVmDescriptor) : EffectVmDescriptor :=
  let r := rotateV3 d
  { r with
    piCount     := r.piCount + 1
    constraints := r.constraints ++ [.piBinding .first keyCol ROT_NEW_CELL_KEY_PI] }

/-- The FRESHNESS tooth (no account-id collision): the new-cell key (column `keyCol`) is a NON-MEMBER
of the BEFORE cells tree (limb 0); the root is unchanged by an absent read. Guarded by the supplied
runtime selector column `sel`. `keyCol` is `param0` for createCell/spawn (the new-cell id) and `param1`
for factory (the derived child VK). -/
def cellsFreshOp (sel keyCol : Nat) : MapOp :=
  { guard   := .var sel
  , root    := .var (beforeCellsRootCol EFFECT_VM_WIDTH)
  , key     := .var keyCol
  , value   := .const 0
  , newRoot := .var (beforeCellsRootCol EFFECT_VM_WIDTH)
  , op      := .absent }

/-- The SET-INSERT: the AFTER cells root (limb 0 of the after block) IS the genuine sorted write of
the new-cell key (`keyCol`) into the BEFORE root. The key rides as its own leaf value (a born-empty
cell). -/
def cellsInsertOp (sel keyCol : Nat) : MapOp :=
  { guard   := .var sel
  , root    := .var (beforeCellsRootCol EFFECT_VM_WIDTH)
  , key     := .var keyCol
  , value   := .var keyCol
  , newRoot := .var (afterCellsRootCol EFFECT_VM_WIDTH)
  , op      := .insert }

/-- The factory's new-cell key column (`param1`, the derived child VK — `CHILD_VK_DERIVED`); factory's
`param0` carries the factory VK, so the child id is `param1`. -/
def FACTORY_CHILD_KEY_PARAM_COL : Nat := prmCol 1

/-- **`createCellV3`** — the rotated createCell WITH the new-cell-key PI weld AND the ACCOUNTS-SET
GROW-GATE. `piCount = 39`. Past the graduated `rotateV3WithNewCellKeyPin` descriptor it appends the
two map-ops that FORCE the accounts set-insert on the live wire (`cellsFreshOp .absent` +
`cellsInsertOp .insert`), repointing limb 0 from a turn-invariant witness limb into a FORCED, grown,
fresh accounts root. -/
def createCellV3 : EffectVmDescriptor2 :=
  let base := graduateV1 (rotateV3WithNewCellKeyPin NEW_CELL_KEY_PARAM_COL
    EffectVmEmitCreateCell.createCellActorVmDescriptor)
  { base with
    constraints := base.constraints
      ++ [.mapOp (cellsFreshOp EffectVmEmitCreateCell.SEL_CREATE_CELL_RT NEW_CELL_KEY_PARAM_COL),
          .mapOp (cellsInsertOp EffectVmEmitCreateCell.SEL_CREATE_CELL_RT NEW_CELL_KEY_PARAM_COL)] }

/-- **`factoryV3`** — the rotated createCellFromFactory WITH the new-cell-key weld + accounts-set
grow-gate (factory selector `13`). Same shape as `createCellV3`. -/
def factoryV3 : EffectVmDescriptor2 :=
  let base := graduateV1 (rotateV3WithNewCellKeyPin FACTORY_CHILD_KEY_PARAM_COL
    EffectVmEmitCreateCellFromFactory.factoryActorVmDescriptor)
  { base with
    constraints := base.constraints
      ++ [.mapOp (cellsFreshOp EffectVmEmitCreateCellFromFactory.SEL_FACTORY_RT
            FACTORY_CHILD_KEY_PARAM_COL),
          .mapOp (cellsInsertOp EffectVmEmitCreateCellFromFactory.SEL_FACTORY_RT
            FACTORY_CHILD_KEY_PARAM_COL)] }

/-- **`spawnV3`** — the rotated spawn WITH the new-cell-key weld + accounts-set grow-gate (spawn
selector `32`). The cap-handoff (child cap-root MOVE + delegation snapshot) is NOT closed here — it
rides spawn's existing `gCapMove`/delegation legs (the named spawn residual). -/
def spawnV3 : EffectVmDescriptor2 :=
  let base := graduateV1 (rotateV3WithNewCellKeyPin NEW_CELL_KEY_PARAM_COL
    EffectVmEmitSpawn.spawnActorVmDescriptor)
  { base with
    constraints := base.constraints
      ++ [.mapOp (cellsFreshOp EffectVmEmitSpawn.SEL_SPAWN_RT NEW_CELL_KEY_PARAM_COL),
          .mapOp (cellsInsertOp EffectVmEmitSpawn.SEL_SPAWN_RT NEW_CELL_KEY_PARAM_COL)] }

/-- **`rotateV3WithNewCellKeyPinCapWrite`** — `rotateV3CapWrite` PLUS the new-cell-key PI weld (the
fifth appended PI pin binding column `keyCol` to `ROT_NEW_CELL_KEY_PI = 46` on the FIRST row).
Structurally identical to `rotateV3WithNewCellKeyPin` (line 1753) but built over `rotateV3CapWrite`
(the cap-root weld DROPPED — limb 25 freed for `insertWriteOpRot`) instead of `rotateV3`. The cells-tree
limb (limb 0) stays WELDED (`weldsAtNoCapRoot` drops ONLY the cap-root weld), so the accounts grow-gate
coexists with the cap-tree insert — they live on DISTINCT limbs (limb 0 vs limb 25). -/
def rotateV3WithNewCellKeyPinCapWrite (keyCol : Nat) (d : EffectVmDescriptor) : EffectVmDescriptor :=
  let r := rotateV3CapWrite d
  { r with
    piCount     := r.piCount + 1
    constraints := r.constraints ++ [.piBinding .first keyCol ROT_NEW_CELL_KEY_PI] }

/-- **`spawnWriteV3`** — `spawnV3` REBASED onto the cap-WRITE rotation (`rotateV3WithNewCellKeyPinCapWrite`,
cap-root limb 25 freed) PLUS the cap-tree INSERT handoff. The genuine `spawn` confers the parent's held
cap to the child (`spawnCapsMap k actor child target := child ↦ [heldCapTo k.caps actor target]`, the
INSERT into the cap-tree). This descriptor FORCES that handoff in-circuit on TWO limbs that coexist:
- limb 0 (cells-tree): the accounts grow-gate (`cellsFreshOp` + `cellsInsertOp`) — the child id INSERTed
  into accounts, EXACTLY as `spawnV3` (the cells-tree weld is untouched by `weldsAtNoCapRoot`);
- limb 25 (cap-tree): the cap handoff (`anchorReadOpRot` + `insertWriteOpRot`) — the parent's held cap to
  `target` membership-read at a PRESENT anchor, then the conferred edge sorted-INSERTed at the child key.

The cap handoff (the parent→child CAPABILITY confer) was the named PHASE-D residual on `spawnV3` (frozen
`cap_root`/gCapPass); freeing limb 25 and driving the insert FORCES it, exactly as `delegateV3`. -/
def spawnWriteV3 : EffectVmDescriptor2 :=
  let base := graduateV1 (rotateV3WithNewCellKeyPinCapWrite NEW_CELL_KEY_PARAM_COL
    EffectVmEmitSpawn.spawnActorVmDescriptor)
  { base with constraints := base.constraints
      ++ [.mapOp (cellsFreshOp EffectVmEmitSpawn.SEL_SPAWN_RT NEW_CELL_KEY_PARAM_COL),
          .mapOp (cellsInsertOp EffectVmEmitSpawn.SEL_SPAWN_RT NEW_CELL_KEY_PARAM_COL),
          .mapOp (anchorReadOpRot EffectVmEmitSpawn.SEL_SPAWN_RT),
          .mapOp (insertWriteOpRot EffectVmEmitSpawn.SEL_SPAWN_RT)] }

/-- **`createCellV3_grow_gate_forces_set_insert` — the live descriptor FORCES the accounts
set-insert + freshness.** On a satisfying `createCellV3` witness whose createCell selector fires, the
two appended map-ops hold: (1) the published new-cell key is ABSENT from the BEFORE cells tree (limb
0) — the no-collision tooth (`opensTo … none`); and (2) the AFTER cells root IS the genuine sorted
insert of that key into the BEFORE root (`writesTo`). Under CR these are FUNCTIONAL, so a frozen or
forged after-root, or a re-created (present) cell id, cannot satisfy the descriptor — exactly the
forgery `kernel_set_insert_is_not_forced_by_the_live_descriptor` documented, now REJECTED. -/
theorem createCellV3_grow_gate_forces_set_insert (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash createCellV3 minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length)
    (hcreate : (envAt t i).loc EffectVmEmitCreateCell.SEL_CREATE_CELL_RT = 1) :
    (opensTo hash ((envAt t i).loc (beforeCellsRootCol EFFECT_VM_WIDTH))
        ((envAt t i).loc NEW_CELL_KEY_PARAM_COL) none)
    ∧ writesTo hash ((envAt t i).loc (beforeCellsRootCol EFFECT_VM_WIDTH))
        ((envAt t i).loc NEW_CELL_KEY_PARAM_COL)
        ((envAt t i).loc NEW_CELL_KEY_PARAM_COL)
        ((envAt t i).loc (afterCellsRootCol EFFECT_VM_WIDTH)) := by
  have hrowc := hsat.rowConstraints i hi
  have hfresh := hrowc (.mapOp (cellsFreshOp EffectVmEmitCreateCell.SEL_CREATE_CELL_RT
    NEW_CELL_KEY_PARAM_COL)) (by simp [createCellV3])
  have hins := hrowc (.mapOp (cellsInsertOp EffectVmEmitCreateCell.SEL_CREATE_CELL_RT
    NEW_CELL_KEY_PARAM_COL)) (by simp [createCellV3])
  exact ⟨(hfresh hcreate).1, hins hcreate⟩

/-- **`factoryV3_grow_gate_forces_set_insert`** — `createCellV3`'s tooth for the factory descriptor
(selector `13`). -/
theorem factoryV3_grow_gate_forces_set_insert (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash factoryV3 minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length)
    (hfactory : (envAt t i).loc EffectVmEmitCreateCellFromFactory.SEL_FACTORY_RT = 1) :
    (opensTo hash ((envAt t i).loc (beforeCellsRootCol EFFECT_VM_WIDTH))
        ((envAt t i).loc FACTORY_CHILD_KEY_PARAM_COL) none)
    ∧ writesTo hash ((envAt t i).loc (beforeCellsRootCol EFFECT_VM_WIDTH))
        ((envAt t i).loc FACTORY_CHILD_KEY_PARAM_COL)
        ((envAt t i).loc FACTORY_CHILD_KEY_PARAM_COL)
        ((envAt t i).loc (afterCellsRootCol EFFECT_VM_WIDTH)) := by
  have hrowc := hsat.rowConstraints i hi
  have hfresh := hrowc (.mapOp (cellsFreshOp EffectVmEmitCreateCellFromFactory.SEL_FACTORY_RT
    FACTORY_CHILD_KEY_PARAM_COL)) (by simp [factoryV3])
  have hins := hrowc (.mapOp (cellsInsertOp EffectVmEmitCreateCellFromFactory.SEL_FACTORY_RT
    FACTORY_CHILD_KEY_PARAM_COL)) (by simp [factoryV3])
  exact ⟨(hfresh hfactory).1, hins hfactory⟩

/-- **`spawnV3_grow_gate_forces_set_insert`** — `createCellV3`'s tooth for the spawn descriptor
(selector `32`). The accounts set-insert is FORCED; the cap-handoff is the named spawn residual. -/
theorem spawnV3_grow_gate_forces_set_insert (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash spawnV3 minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length)
    (hspawn : (envAt t i).loc EffectVmEmitSpawn.SEL_SPAWN_RT = 1) :
    (opensTo hash ((envAt t i).loc (beforeCellsRootCol EFFECT_VM_WIDTH))
        ((envAt t i).loc NEW_CELL_KEY_PARAM_COL) none)
    ∧ writesTo hash ((envAt t i).loc (beforeCellsRootCol EFFECT_VM_WIDTH))
        ((envAt t i).loc NEW_CELL_KEY_PARAM_COL)
        ((envAt t i).loc NEW_CELL_KEY_PARAM_COL)
        ((envAt t i).loc (afterCellsRootCol EFFECT_VM_WIDTH)) := by
  have hrowc := hsat.rowConstraints i hi
  have hfresh := hrowc (.mapOp (cellsFreshOp EffectVmEmitSpawn.SEL_SPAWN_RT
    NEW_CELL_KEY_PARAM_COL)) (by simp [spawnV3])
  have hins := hrowc (.mapOp (cellsInsertOp EffectVmEmitSpawn.SEL_SPAWN_RT
    NEW_CELL_KEY_PARAM_COL)) (by simp [spawnV3])
  exact ⟨(hfresh hspawn).1, hins hspawn⟩

/-- **`spawnWriteV3_grow_gate_forces_set_insert`** — `spawnV3_grow_gate_forces_set_insert` transported to
the cap-WRITE-rebased `spawnWriteV3`. The accounts set-insert (cells-tree limb 0) STILL fires: the
cells-tree weld is untouched by `weldsAtNoCapRoot` (only cap-root limb 25 was freed), so the
`cellsFreshOp` + `cellsInsertOp` map-ops bind exactly as on `spawnV3`. -/
theorem spawnWriteV3_grow_gate_forces_set_insert (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash spawnWriteV3 minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length)
    (hspawn : (envAt t i).loc EffectVmEmitSpawn.SEL_SPAWN_RT = 1) :
    (opensTo hash ((envAt t i).loc (beforeCellsRootCol EFFECT_VM_WIDTH))
        ((envAt t i).loc NEW_CELL_KEY_PARAM_COL) none)
    ∧ writesTo hash ((envAt t i).loc (beforeCellsRootCol EFFECT_VM_WIDTH))
        ((envAt t i).loc NEW_CELL_KEY_PARAM_COL)
        ((envAt t i).loc NEW_CELL_KEY_PARAM_COL)
        ((envAt t i).loc (afterCellsRootCol EFFECT_VM_WIDTH)) := by
  have hrowc := hsat.rowConstraints i hi
  have hfresh := hrowc (.mapOp (cellsFreshOp EffectVmEmitSpawn.SEL_SPAWN_RT
    NEW_CELL_KEY_PARAM_COL)) (by simp [spawnWriteV3])
  have hins := hrowc (.mapOp (cellsInsertOp EffectVmEmitSpawn.SEL_SPAWN_RT
    NEW_CELL_KEY_PARAM_COL)) (by simp [spawnWriteV3])
  exact ⟨(hfresh hspawn).1, hins hspawn⟩

/-- **`spawnWriteV3_forces_write` — the spawn parent→child cap-tree INSERT is FORCED in-circuit.** On an
active spawn row of a `Satisfied2 spawnWriteV3` witness: the parent's held cap to `target` is
membership-read against the before cap-root (a PRESENT anchor at `param[ANCHOR_KEY]` → `param[ANCHOR_MASK]`),
and the post `cap_root` is the GENUINE sorted insert of the conferred edge (`param[KEEP_MASK]`) at the
child key (`param[CAP_KEY]`). Mirrors `delegateV3_forces_write` EXACTLY over the spawn selector — this is
the cap handoff that was the named PHASE-D residual, now FORCED. -/
theorem spawnWriteV3_forces_write (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hsat : Satisfied2 hash spawnWriteV3 minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length)
    (hactive : (envAt t i).loc EffectVmEmitSpawn.SEL_SPAWN_RT = 1) :
    opensTo hash ((envAt t i).loc (beforeCapRootCol EFFECT_VM_WIDTH))
        ((envAt t i).loc (prmCol ANCHOR_KEY)) (some ((envAt t i).loc (prmCol ANCHOR_MASK)))
    ∧ writesTo hash ((envAt t i).loc (beforeCapRootCol EFFECT_VM_WIDTH))
        ((envAt t i).loc (prmCol CAP_KEY)) ((envAt t i).loc (prmCol KEEP_MASK))
        ((envAt t i).loc (afterCapRootCol EFFECT_VM_WIDTH)) := by
  have hrowc := hsat.rowConstraints i hi
  have hread := hrowc (.mapOp (anchorReadOpRot EffectVmEmitSpawn.SEL_SPAWN_RT))
    (by simp [spawnWriteV3])
  have hwrite := hrowc (.mapOp (insertWriteOpRot EffectVmEmitSpawn.SEL_SPAWN_RT))
    (by simp [spawnWriteV3])
  exact ⟨(hread hactive).1, hwrite hactive⟩

#assert_axioms createCellV3_grow_gate_forces_set_insert
#assert_axioms factoryV3_grow_gate_forces_set_insert
#assert_axioms spawnV3_grow_gate_forces_set_insert
#assert_axioms spawnWriteV3_grow_gate_forces_set_insert
#assert_axioms spawnWriteV3_forces_write

-- The new-cell-key pin lands at PI slot 46; each rotated create-family descriptor publishes 39 PIs.
#guard ROT_NEW_CELL_KEY_PI == 42 + 4
#guard NEW_CELL_KEY_PARAM_COL == 68
#guard createCellV3.piCount == 47
#guard factoryV3.piCount == 47
#guard spawnV3.piCount == 47
-- Each carries the four rotated commit pins + one new-cell-key pin + the two grow-gate map-ops.
#guard createCellV3.constraints.length == (v3Of EffectVmEmitCreateCell.createCellActorVmDescriptor).constraints.length + 1 + 2
#guard (mapOpsOf createCellV3).length == 2
#guard (mapOpsOf factoryV3).length == 2
#guard (mapOpsOf spawnV3).length == 2

/-! ### The SetField + BridgeMint runtime reconcile (the last rotation flip gate, C7).

The model (the end-to-end `effect_vm_rotation_flip` prove) surfaced TWO runtime divergences in
the rotated SetField / BridgeMint descriptors. Both are reconciled here so those turns ROTATE.

**Seam 1 — the nonce tick.** The runtime trace generator (`circuit/src/effect_vm/trace.rs`)
TICKS the per-cell sequence nonce on EVERY non-NoOp row: `Effect::SetField` →
`new_state.nonce += 1`, `Effect::BridgeMint` → `new_state.nonce += 1` (only `Effect::NoOp`
leaves it). `trace_rotated.rs::fill_block` copies that ticked nonce into the rotated `r1` limb
(`row[base+2] = row[state_base + state::NONCE]`, the `weldsAt` r1↔NONCE weld). But the per-effect
descriptors FREEZE it (`EffectVmEmitSetField.gNonceFreeze` / `EffectVmEmitMint.gNonceFix` are
BOTH `after_nonce − before_nonce`), so `after_nonce = before_nonce` is UNSAT on the ticked trace.

**Seam 2 — the value/credit param column.** The runtime puts the EFFECT's payload at `param1`,
not `param0`: `Effect::SetField` writes `param0 = field_index`, `param1 = new_value`
(`trace.rs` + the v1 hand-AIR `air.rs` `new_value = p1`); `Effect::BridgeMint` writes
`param0 = mint_hash`, `param1 = value_lo` and credits `balance += value_lo`. But the per-effect
descriptors read `param0`: `setFieldVmDescriptor`'s write gate reads `prmCol VALUE = prmCol
param.AMOUNT = prmCol 0` (= the runtime's FIELD_INDEX), and `mintVmDescriptor`'s credit reads
`prmCol param.AMOUNT = prmCol 0` (= the runtime's MINT_HASH). So both check the field write /
balance credit against the WRONG column — UNSAT on the honest trace even with the nonce fixed.
(The registry's BridgeMint leg is `mintVmDescriptor`, NOT `EffectVmEmitBridgeMint` — that module
does not build in the shared tree, `EffectVmEmitV2` line 73 — so the param1 fix is applied to the
mint descriptor's credit here rather than swapping descriptors.)

This section builds TICK-faced + param1-corrected variants by REBUILDING each descriptor's
constraint list: the nonce freeze gate becomes the transfer/noteSpend TICK gate
`EffectVmEmitTransfer.gNonce = (after_nonce − before_nonce) − (1 − s_noop)` (the SAME
`−(1 − selector)` term `transferVmDescriptor2R24` / `noteSpendVmDescriptor2R24` carry), and the
field-write / balance-credit gate reads `prmCol 1` (the runtime's NEW_VALUE / value_lo). Every
OTHER gate, transition, boundary pin, hash site, and range tooth is the per-effect descriptor's
verbatim, so `rotateV3`'s parametric keystones (`rotV3_sound_v1`, `rotV3_binds_published`,
`graduable_rotateV3`) compose unchanged (the graduable side conditions read only the unchanged
sites/ranges).

POST-RECONCILE (the source-coherence follow-up): the per-effect `EffectVmEmitSetField` /
`EffectVmEmitMint` SOURCE descriptors have SINCE been corrected to match the runtime themselves
(the SAME three fixes: nonce tick, value/credit at `param1`, setField gated by `sel::SET_FIELD = 2`;
their faithfulness theorems re-proved against the ticked/param1 behaviour, both polarities, on the
active-row premise `IsSetFieldRow` / `IsMintRow` — exactly burn's shape). So these tick-faced
constraint lists now COINCIDE with their source descriptors' (`setFieldTickFace_eq_source` below);
the rebuild is retained so the rotated registry JSON + the `V3_STAGED_REGISTRY_FP` pin are unchanged,
but it is no longer a BYPASS of a buggy source — source and rotated leg agree. The descriptor NAME is
kept (`dregg-effectvm-setfield-v1` / `dregg-effectvm-mint-v1`), exactly as the v1 reconciles kept it.

SOUNDNESS TOOTH (do NOT just make it SAT): the tick gate is ENFORCED — a row whose nonce delta is
NOT the tick (`after_nonce ≠ before_nonce + 1` on a non-NoOp row) FAILS the gate and is UNSAT
(`setFieldTick_rejects_wrong_nonce_delta` / `mintTick_rejects_wrong_nonce_delta`, both polarities
`#guard`'d), and the corrected write/credit gate is ENFORCED — a row whose written field / credited
balance does NOT match `prmCol 1` is UNSAT (`setFieldP1_rejects_wrong_value` /
`mintP1_rejects_wrong_credit`). So the rotated leg binds the per-cell sequence counter AND the
genuine payload column the runtime carries. -/

/-- The runtime's value/credit param column: `param1` (NEW_VALUE for setField, value_lo for
BridgeMint) — NOT `param0` (FIELD_INDEX / MINT_HASH). The v1 hand-AIR (`air.rs`) reads `p1`. -/
def RUNTIME_VALUE_PARAM : Nat := 1

/-- The runtime's SetField SELECTOR column: `sel::SET_FIELD = 2` (the trace generator writes
`row[2] = 1` on the active setField row, `effect_selector` → `trace.rs`). The per-effect
`EffectVmEmitSetField.SEL_SET_FIELD` has SINCE been reconciled to this same value (the source
descriptor was corrected in the cutover — the earlier `54` was `sbCol BALANCE_LO`, NOT a selector).
The corrected write gate gates by THIS column. -/
def SEL_SET_FIELD_COL : Nat := 2

-- The runtime selector column is `sel::SET_FIELD = 2`, distinct from `sbCol BALANCE_LO = 54`.
-- POST-RECONCILE: the per-effect `EffectVmEmitSetField.SEL_SET_FIELD` now AGREES (= 2), and the
-- per-effect value column `VALUE` now reads `param1` (the runtime NEW_VALUE), matching the
-- corrections below — so the rotated tick-face and the source descriptor now COINCIDE (see
-- `setFieldTickFace_eq_source`).
#guard SEL_SET_FIELD_COL == 2
#guard SEL_SET_FIELD_COL ≠ sbCol state.BALANCE_LO
#guard EffectVmEmitSetField.SEL_SET_FIELD == SEL_SET_FIELD_COL   -- source reconciled (was the 54 bug)
#guard EffectVmEmitSetField.VALUE == RUNTIME_VALUE_PARAM         -- source value column reconciled to param1

/-! #### The TICK-faced + param1-corrected SetField (per slot). -/

/-- The field-`slot` WRITE gate reading the RUNTIME value column (`prmCol 1 = NEW_VALUE`),
SELECTOR-GATED by `s_set_field`: `s_set_field · (fields[slot]_after − param1) = 0`.

Two corrections over the per-effect `gFieldWrite` (which is `fields[slot]_after − prmCol 0`,
UNGATED): (1) it reads `param1` (the runtime NEW_VALUE — `air.rs` `new_value = p1`), not `param0`
(FIELD_INDEX); (2) it is gated by `s_set_field`, exactly as the runtime hand-AIR gates every
setField constraint (`air.rs` `c = s_setfield · …`). The gating is LOAD-BEARING for multi-row
traces: the field write PERSISTS into the after-state, so a trailing NoOp PAD row carries
`fields[slot]_after = (the written value)` while its `param1 = 0` — an UNGATED write gate would
fire `written_value − 0 ≠ 0` and the honest 64-row trace would be UNSAT. With the `s_set_field`
factor the gate VANISHES on NoOp rows (`s_set_field = 0`) and binds only the ACTIVE row
(`s_set_field = 1`), matching the runtime. (The freeze gates degenerate naturally on NoOp —
`after − before = frozen − frozen = 0` — so only the write gate needs the factor.) -/
def gFieldWriteP1 (slot : Fin 8) : EmittedExpr :=
  .mul (.var SEL_SET_FIELD_COL)
    (EffectVmEmitTransfer.eSub (EffectVmEmitTransfer.eSA (state.FIELD_BASE + slot.val))
      (EffectVmEmitTransfer.ePrm RUNTIME_VALUE_PARAM))

/-- The setField row gates with (1) the nonce FREEZE gate swapped for the transfer/noteSpend TICK
gate `EffectVmEmitTransfer.gNonce` and (2) the WRITE gate reading the runtime value column
`prmCol 1`. Every OTHER gate (the bal/cap/reserved freezes, the seven other-field passthroughs)
is `EffectVmEmitSetField.setFieldRowGates`'s verbatim. -/
def setFieldRowGatesTick (slot : Fin 8) : List VmConstraint :=
  [ .gate (gFieldWriteP1 slot)
  , .gate EffectVmEmitSetField.gBalLoFreeze
  , .gate EffectVmEmitTransfer.gBalHi
  , .gate EffectVmEmitTransfer.gNonce
  , .gate EffectVmEmitTransfer.gCapPass
  , .gate EffectVmEmitTransfer.gResPass ]
  ++ EffectVmEmitSetField.gOtherFieldsAll slot

/-- **`setFieldTickFace slot`** — `setFieldVmDescriptor slot` with the nonce gate ticked AND the
write gate reading the runtime value column. The name, width, PI count, hash sites, and ranges are
the per-effect descriptor's verbatim; only the constraint list changes those two gates (so
`graduable` — which reads only sites/ranges — is unchanged, and the rotated keystones compose). -/
def setFieldTickFace (slot : Fin 8) : EffectVmDescriptor :=
  { EffectVmEmitSetField.setFieldVmDescriptor slot with
    constraints := setFieldRowGatesTick slot }

/-- The tick-faced setField shares the per-effect descriptor's sites + ranges (both slot-FREE:
`transferHashSites` and the two balance-limb range teeth), so it is graduable (the parametric
`graduable_rotateV3` premise). `graduable` reads only `hashSites`/`ranges`, invisible to the
constraint swap, so this is the constant `transferHashSites`-graduability — `rfl`. -/
theorem graduable_setFieldTickFace (slot : Fin 8) :
    graduable (setFieldTickFace slot) = true := rfl

/-- **SOURCE-COHERENCE: the tick-face now COINCIDES with the (reconciled) source descriptor.** After
the per-effect `EffectVmEmitSetField` source was corrected (nonce tick, value at `param1`, gated by
`sel::SET_FIELD = 2`), its `setFieldRowGates` IS this section's `setFieldRowGatesTick` (gate-for-gate
definitionally — `gFieldWriteP1 = gFieldWrite`, both `.mul (.var 2) (·_after − param1)`; the tick gate
is the same `EffectVmEmitTransfer.gNonce`), so the tick-faced descriptor equals the source descriptor.
The rotated registry routing through `setFieldV3` is therefore NOT a bypass of a buggy source — they
are the same circuit. -/
theorem setFieldTickFace_eq_source (slot : Fin 8) :
    setFieldTickFace slot = EffectVmEmitSetField.setFieldVmDescriptor slot := rfl

/-- In-block offset of the `lifecycle` limb (limb 29 in `preLimbsAt`, shifted +1 by the
`commitments_root` flag-day): the per-cell lifecycle felt the producer witness carries
(`rotation_witness.rs::lifecycle_felt`, `pre_limbs[29]`). The forced limb for `cellSeal` /
`cellUnseal` / `cellDestroy`. -/
def B_LIFECYCLE : Nat := 29

/-- In-block offset of the `authority_digest` / `record_digest` limb (limb 24 = r23 in `preLimbsAt`):
the single felt folding ALL authority-bearing cell state including the `permissions` / `verification_key`
slots (`trace_rotated.rs::B_AUTHORITY_DIGEST`). The forced limb for `setPermissions` / `setVK`. -/
def B_RECORD_DIGEST : Nat := 24

/-- The rotated AFTER-block base offset (past the v1 layout + the BEFORE block, `B_SPAN = 91`). -/
def AFTER_BLOCK_OFF : Nat := 91

/-- **H1: the 7 headroom authority limb offsets** (offsets 12..=18 = r11..r17) carrying limb-1..7 of
the faithful 8-felt authority digest (`compute_authority_digest_8`), beside limb-0 at
`B_RECORD_DIGEST = 24`. These previously-unwelded headroom limbs now ride the absorption chain and are
WELDED (continuity freeze for value effects / record-pin8 for movers) so all 8 limbs are forced. -/
def authorityHeadroomOffs : List Nat := [12, 13, 14, 15, 16, 17, 18]

/-- The 7 continuity `colEq` freezes welding each headroom authority limb BEFORE↔AFTER (value cohort). -/
def authorityHeadroomFreezes (w : Nat) : List VmConstraint :=
  authorityHeadroomOffs.map (fun off => colEq (w + off) (w + AFTER_BLOCK_OFF + off))

/-- **v10: the 14 faithful-8-felt completion-limb offsets** — the 7 perms extras (pre-iroot limbs
37..=43 = `permsHash[1..7]`) and the 7 vk extras (44..=50 = `vkHash[1..7]`). For a VALUE turn the
permissions / VK are UNCHANGED, so each completion limb is frozen BEFORE↔AFTER — closing the GENTIAN
fail-open for the perms/vk halves (no unwelded wide-open limb can smuggle a ~31-bit-colliding authority
into NEW_COMMIT during an innocuous value move). -/
def permsVKCompletionOffs : List Nat :=
  [37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50]

/-- The 14 continuity `colEq` freezes welding each v10 perms/vk completion limb BEFORE↔AFTER. -/
def permsVKCompletionFreezes (w : Nat) : List VmConstraint :=
  permsVKCompletionOffs.map (fun off => colEq (w + off) (w + AFTER_BLOCK_OFF + off))

/-- The full appended authority-continuity weld list: the six dedicated-sub-limb freezes (r23 ·
lifecycle · perms · vk · mode · fields-root) PLUS the seven H1 headroom freezes — ONE right-operand of
the single `++` so the v1 constraints stay the left operand (the keystones compose verbatim). -/
def frozenAuthorityColEqs (w : Nat) : List VmConstraint :=
  [ colEq (w + B_RECORD_DIGEST) (w + AFTER_BLOCK_OFF + B_RECORD_DIGEST)
  , colEq (w + B_LIFECYCLE)     (w + AFTER_BLOCK_OFF + B_LIFECYCLE)
  , colEq (w + B_PERMS)         (w + AFTER_BLOCK_OFF + B_PERMS)
  , colEq (w + B_VK)            (w + AFTER_BLOCK_OFF + B_VK)
  , colEq (w + B_MODE)          (w + AFTER_BLOCK_OFF + B_MODE)
  , colEq (w + B_FIELDS_ROOT)   (w + AFTER_BLOCK_OFF + B_FIELDS_ROOT) ]
  ++ authorityHeadroomFreezes w
  ++ permsVKCompletionFreezes w

/-! ### THE AUTHORITY-FROZEN CONTINUITY WELD (the value cohort's light-client close, #1 WAVE 0).

The deployed commitment now binds the authority residue `r23` (`B_RECORD_DIGEST`, the concrete
realization of the Lean `StateCommit.RH` rest-hash) and `B_LIFECYCLE` into `state_commit`
(`recompute_block_commit`). But `weldsAt` welds ONLY balance/nonce/fields[0..7]/cap_root — NOT `r23`
or lifecycle. So for a VALUE effect (transfer/burn/mint/bridgeMint/incrementNonce/emitEvent/setField on
slots 0..7) the BEFORE `r23` and AFTER `r23` are independent free felts: a malicious prover witnesses an
AFTER `r23` folding ARBITRARY permissions/VK/lifecycle/mode, the value gate is satisfied, and
`state_commit`/NEW_COMMIT binds the forged authority — a ledgerless light client cannot tell. That is a
LIVE, publishable forgery (silently rewriting the authority half during an innocuous value move).

The kernel leaves the WHOLE authority residue UNCHANGED for these effects, so the honest after-`r23`
EQUALS the before. `rotateV3FrozenAuthority` forces exactly that — two same-row `colEq` welds tying the
AFTER `r23`/lifecycle to the BEFORE. By `StateCommit.RestHashIffFrame` (`RH k = RH k' ↔` the 16 non-cell
authority components agree), this FORCES the authority frame the apex previously CARRIED
(`rotatedEncodes.frCaps`/`frLifecycle`). It mirrors the `rotateV3WithRecordPin` append shape — every v1
column/constraint/hash-site/range is untouched, so the keystones compose verbatim. NOT for the authority
MOVERS (setPermissions/setVK/seal/unseal/destroy/refusal/receiptArchive/makeSovereign/setField[8..15]),
which legitimately change `r23`/lifecycle and keep their record-pin / future in-circuit recompute. -/
def rotateV3FrozenAuthority (d : EffectVmDescriptor) : EffectVmDescriptor :=
  let r := rotateV3 d
  -- The six dedicated-sub-limb freezes PLUS the seven H1 headroom freezes (all 8 authority limbs
  -- WELDED for a VALUE turn — the GENTIAN law: no unwelded limb can smuggle a 31-bit-colliding
  -- wide-open authority into NEW_COMMIT). ONE appended right-operand so v1 stays the left operand.
  { r with constraints := r.constraints ++ frozenAuthorityColEqs d.traceWidth }

/-- The continuity welds (r23 · lifecycle · perms · vk · mode · fields-root + the seven H1 headroom
authority limbs) are the only constraints past `rotateV3`'s — the WAVE-2/3 sub-limb welds + the H1
8-felt headroom welds so a VALUE turn cannot smuggle an authority-shape change into NEW_COMMIT. -/
theorem rotateV3FrozenAuthority_constraints (d : EffectVmDescriptor) :
    (rotateV3FrozenAuthority d).constraints
      = (rotateV3 d).constraints ++ frozenAuthorityColEqs d.traceWidth := rfl

/-- Continuity welds are CONSTRAINTS; `graduable` reads only sites/ranges (`rotateV3`'s verbatim). -/
theorem graduable_rotateV3FrozenAuthority {d : EffectVmDescriptor}
    (h : graduable d = true) : graduable (rotateV3FrozenAuthority d) = true := by
  have hr := graduable_rotateV3 h
  unfold rotateV3FrozenAuthority
  unfold graduable at hr ⊢
  simpa using hr

/-- **The authority residue is FROZEN on a satisfying TRANSITION row** (`isLast = false`): a row
satisfying `rotateV3FrozenAuthority d` carries AFTER `r23` = BEFORE `r23` AND AFTER lifecycle = BEFORE
lifecycle. The freezes are `.gate`s (deployed `when_transition()`), so they bind at the active row. -/
theorem rotateV3FrozenAuthority_freezes (hash : List ℤ → ℤ) (d : EffectVmDescriptor)
    (env : VmRowEnv) (isFirst isLast : Bool) (hlast : isLast = false)
    (h : satisfiedVm hash (rotateV3FrozenAuthority d) env isFirst isLast) :
    env.loc (d.traceWidth + B_RECORD_DIGEST)
        = env.loc (d.traceWidth + AFTER_BLOCK_OFF + B_RECORD_DIGEST)
    ∧ env.loc (d.traceWidth + B_LIFECYCLE)
        = env.loc (d.traceWidth + AFTER_BLOCK_OFF + B_LIFECYCLE) := by
  obtain ⟨hc, _, _⟩ := h
  refine ⟨?_, ?_⟩
  · have hmem : colEq (d.traceWidth + B_RECORD_DIGEST)
        (d.traceWidth + AFTER_BLOCK_OFF + B_RECORD_DIGEST) ∈ (rotateV3FrozenAuthority d).constraints := by
      rw [rotateV3FrozenAuthority_constraints]
      exact List.mem_append_right _ (by simp [frozenAuthorityColEqs])
    exact (colEq_holds_iff env isFirst isLast _ _ hlast).mp (hc _ hmem)
  · have hmem : colEq (d.traceWidth + B_LIFECYCLE)
        (d.traceWidth + AFTER_BLOCK_OFF + B_LIFECYCLE) ∈ (rotateV3FrozenAuthority d).constraints := by
      rw [rotateV3FrozenAuthority_constraints]
      exact List.mem_append_right _ (by simp [frozenAuthorityColEqs])
    exact (colEq_holds_iff env isFirst isLast _ _ hlast).mp (hc _ hmem)

/-- **(authority drift ⇒ UNSAT)** — the NEGATIVE TOOTH: a row whose AFTER `r23` differs from the BEFORE
`r23` (a value turn smuggling an authority change into NEW_COMMIT) does NOT satisfy
`rotateV3FrozenAuthority d`. This is the light-client bite: `verify_vm_descriptor2` alone rejects it,
no trusted post-cell needed. -/
theorem rotateV3FrozenAuthority_rejects_drift (hash : List ℤ → ℤ) (d : EffectVmDescriptor)
    (env : VmRowEnv) (isFirst isLast : Bool) (hlast : isLast = false)
    (hdrift : env.loc (d.traceWidth + B_RECORD_DIGEST)
        ≠ env.loc (d.traceWidth + AFTER_BLOCK_OFF + B_RECORD_DIGEST)) :
    ¬ satisfiedVm hash (rotateV3FrozenAuthority d) env isFirst isLast :=
  fun h => hdrift (rotateV3FrozenAuthority_freezes hash d env isFirst isLast hlast h).1

/-- The v1 denotation survives the added continuity welds (the per-effect faithfulness theorems
compose through, exactly as for the record / nullifier pins). -/
theorem rotateV3FrozenAuthority_satisfiedVm_v1 (hash : List ℤ → ℤ) (d : EffectVmDescriptor)
    (env : VmRowEnv) (isFirst isLast : Bool)
    (h : satisfiedVm hash (rotateV3FrozenAuthority d) env isFirst isLast) :
    satisfiedVm hash d env isFirst isLast := by
  apply rotateV3_satisfiedVm_v1 hash d env isFirst isLast
  obtain ⟨hc, hsites, hr⟩ := h
  refine ⟨fun c hc' => hc c ?_, hsites, hr⟩
  rw [rotateV3FrozenAuthority_constraints]
  exact List.mem_append_left _ hc'

/-- **`v3OfFrozen d`** — the graduated rotated descriptor of a value-cohort member WITH the authority
continuity weld. Identical SHAPE to `v3Of d` (same width/piCount — the weld is two appended `colEq`
constraints, no new column), so every width/graduability `#guard` and the per-effect value theorems
lift verbatim (via `rotV3Frozen_sound_v1` below); it ADDS the authority-frame forcing. -/
def v3OfFrozen (d : EffectVmDescriptor) : EffectVmDescriptor2 := graduateV1 (rotateV3FrozenAuthority d)

-- The fee pin lands at PI slot 46 (one past the four rotated commit pins 34..37) and the rotated
-- fee'd transfer publishes 39 PIs over the SAME rotated width as the unfee'd transfer.
#guard (rotateV3WithFeePin (rotateV3FrozenAuthority EffectVmEmitTransfer.transferFeeVmDescriptor)).piCount == 47
#guard (rotateV3WithFeePin (rotateV3FrozenAuthority EffectVmEmitTransfer.transferFeeVmDescriptor)).traceWidth
        == EffectVmEmitTransfer.transferVmDescriptor.traceWidth + APPENDIX_SPAN

/-- **`transferFeeV3`** — the graduated rotated fee'd transfer descriptor (the deployed fee'd cohort
member; the frozen-authority + fee-pinned analog of `transferVmDescriptor2R24 = v3OfFrozen
transferVmDescriptor`). `piCount = 39`: the four rotated commit pins + the appended fee pin. The fee
column (`feeCol = saCol state.RESERVED`) is forced equal to the published fee PI on the last row, and
the augmented balance-lo gate forces the fee debit into the proven balance flow (`new = old −
transfer − fee`), so NEW_COMMIT binds the POST-fee balance and a ledgerless client needs no trusted
`+ fee` reconstruction. -/
def transferFeeV3 : EffectVmDescriptor2 :=
  graduateV1 (rotateV3WithFeePin (rotateV3FrozenAuthority EffectVmEmitTransfer.transferFeeVmDescriptor))

#guard transferFeeV3.piCount == 47
-- Phase B-GATE: graduation appends `7 · n_sites` lane columns past the rotated width
-- (`graduateV1 g` width = `g.traceWidth + 7·g.hashSites.length`).
#guard transferFeeV3.traceWidth ==
  EFFECT_VM_WIDTH + APPENDIX_SPAN + (CHIP_OUT_LANES - 1) *
    (rotateV3WithFeePin (rotateV3FrozenAuthority
      EffectVmEmitTransfer.transferFeeVmDescriptor)).hashSites.length
#guard graduable (rotateV3WithFeePin (rotateV3FrozenAuthority EffectVmEmitTransfer.transferFeeVmDescriptor))

/-- A `Satisfied2` witness of the FROZEN graduation yields the full v1 denotation of the original
descriptor on every row — so the per-effect VALUE soundness chains (`*_pins_value`, etc.) lift to the
frozen descriptor exactly as `rotV3_sound_v1` lifts them to `v3Of`. -/
theorem rotV3Frozen_sound_v1 (permOut : List ℤ → List ℤ) (hash : List ℤ → ℤ)
    (d : EffectVmDescriptor)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hgrad : graduable d = true)
    (hf : Satisfied2Faithful permOut hash (v3OfFrozen d) minit mfin maddrs t) :
    ∀ i, i < t.rows.length →
      satisfiedVm hash d (envAt t i) (i == 0) (i + 1 == t.rows.length) := by
  intro i hi
  exact rotateV3FrozenAuthority_satisfiedVm_v1 hash d _ _ _
    (satisfied2Faithful_satisfiedVm permOut hash (rotateV3FrozenAuthority d) minit mfin maddrs t
      (graduable_rotateV3FrozenAuthority hgrad) hf i hi)

/-- **`setFieldV3 slot`** — the rotated tick-faced setField (the registry member). setField[0..7] is a
VALUE effect, so it carries the authority-frame freeze (`v3OfFrozen`): AFTER-r23 == BEFORE-r23 (+ lifecycle). -/
def setFieldV3 (slot : Fin 8) : EffectVmDescriptor2 := v3OfFrozen (setFieldTickFace slot)

/-- **The nonce TICK holds on a satisfying non-NoOp setField row.** A row satisfying the rotated
tick-faced setField, with `s_noop = 0`, carries `after_nonce = before_nonce + 1` (the runtime
tick) — the rotated re-statement of the transfer/noteSpend nonce gate, now on setField. -/
theorem setFieldV3_pins_nonce_tick (slot : Fin 8) (hash : List ℤ → ℤ) (env : VmRowEnv)
    (isFirst isLast : Bool) (hlast : isLast = false) (hnoop : env.loc sel.NOOP = 0)
    (h : satisfiedVm hash (rotateV3 (setFieldTickFace slot)) env isFirst isLast) :
    env.loc (saCol state.NONCE) = env.loc (sbCol state.NONCE) + 1 := by
  subst hlast
  have hmem : VmConstraint.gate EffectVmEmitTransfer.gNonce ∈ (rotateV3 (setFieldTickFace slot)).constraints := by
    apply List.mem_append_left
    show _ ∈ setFieldRowGatesTick slot
    simp [setFieldRowGatesTick]
  have hg := h.1 _ hmem
  simp only [VmConstraint.holdsVm, EffectVmEmitTransfer.gNonce, EffectVmEmitTransfer.eSub,
    EffectVmEmitTransfer.eSA, EffectVmEmitTransfer.eSB, EffectVmEmitTransfer.eSelNoop,
    EmittedExpr.eval] at hg
  rw [hnoop] at hg
  linarith [hg]

/-- **ANTI-GHOST (wrong nonce delta ⇒ UNSAT)** — the C7 soundness tooth for setField. A non-NoOp
row whose nonce delta is NOT the tick (`after_nonce ≠ before_nonce + 1`) does NOT satisfy the
rotated tick-faced setField: the swapped tick gate REJECTS it. A forged passthrough
(`after = before`) is the special case the FREEZE descriptor wrongly accepted; it is now UNSAT. -/
theorem setFieldTick_rejects_wrong_nonce_delta (slot : Fin 8) (hash : List ℤ → ℤ) (env : VmRowEnv)
    (isFirst isLast : Bool) (hlast : isLast = false) (hnoop : env.loc sel.NOOP = 0)
    (hwrong : env.loc (saCol state.NONCE) ≠ env.loc (sbCol state.NONCE) + 1) :
    ¬ satisfiedVm hash (rotateV3 (setFieldTickFace slot)) env isFirst isLast :=
  fun h => hwrong (setFieldV3_pins_nonce_tick slot hash env isFirst isLast hlast hnoop h)

/-- **The corrected WRITE binds the runtime value column on the ACTIVE row.** A row satisfying the
rotated param1-corrected setField with `s_set_field = 1` (the active setField row) carries
`fields[slot]_after = param1` (the runtime NEW_VALUE) — the selector-gated write gate, on the
active row, reads the column the trace generator wrote the value to. (On NoOp rows
`s_set_field = 0` the gate vanishes, so the binding is exactly the runtime's gated semantics.) -/
theorem setFieldV3_pins_value (slot : Fin 8) (hash : List ℤ → ℤ) (env : VmRowEnv)
    (isFirst isLast : Bool) (hlast : isLast = false) (hactive : env.loc SEL_SET_FIELD_COL = 1)
    (h : satisfiedVm hash (rotateV3 (setFieldTickFace slot)) env isFirst isLast) :
    env.loc (saCol (state.FIELD_BASE + slot.val)) = env.loc (prmCol RUNTIME_VALUE_PARAM) := by
  subst hlast
  have hmem : VmConstraint.gate (gFieldWriteP1 slot) ∈ (rotateV3 (setFieldTickFace slot)).constraints := by
    apply List.mem_append_left
    show _ ∈ setFieldRowGatesTick slot
    simp [setFieldRowGatesTick]
  have hg := h.1 _ hmem
  simp only [VmConstraint.holdsVm, gFieldWriteP1, EffectVmEmitTransfer.eSub,
    EffectVmEmitTransfer.eSA, EffectVmEmitTransfer.ePrm, EmittedExpr.eval] at hg
  rw [hactive] at hg
  linarith [hg]

/-- **ANTI-GHOST (wrong written value ⇒ UNSAT)** — the C7 param-column soundness tooth for
setField. An ACTIVE setField row (`s_set_field = 1`) whose written field does NOT equal `param1`
(the runtime value column) does NOT satisfy the corrected descriptor: the gated write gate, on the
active row, REJECTS it. -/
theorem setFieldP1_rejects_wrong_value (slot : Fin 8) (hash : List ℤ → ℤ) (env : VmRowEnv)
    (isFirst isLast : Bool) (hlast : isLast = false) (hactive : env.loc SEL_SET_FIELD_COL = 1)
    (hwrong : env.loc (saCol (state.FIELD_BASE + slot.val)) ≠ env.loc (prmCol RUNTIME_VALUE_PARAM)) :
    ¬ satisfiedVm hash (rotateV3 (setFieldTickFace slot)) env isFirst isLast :=
  fun h => hwrong (setFieldV3_pins_value slot hash env isFirst isLast hlast hactive h)

/-! #### The TICK-faced + param1-corrected BridgeMint (= the `mintVmDescriptor2R24` member). -/

/-- Balance-lo CREDIT body reading the RUNTIME value column (`prmCol 1 = value_lo`):
`new_bal_lo − old_bal_lo − param1` (so `new = old + value_lo`). (The per-effect `gBalLoCredit`
reads `prmCol 0 = MINT_HASH` on a BridgeMint row; the runtime credits `param1 = value_lo`.) -/
def gBalLoCreditP1 : EmittedExpr :=
  .add (EffectVmEmitTransfer.eSub (EffectVmEmitTransfer.eSA state.BALANCE_LO)
          (EffectVmEmitTransfer.eSB state.BALANCE_LO))
    (.mul (.const (-1)) (EffectVmEmitTransfer.ePrm RUNTIME_VALUE_PARAM))

/-- The mint row gates with (1) the nonce FREEZE gate (`gNonceFix`) swapped for the TICK gate and
(2) the balance credit reading the runtime value column `prmCol 1`. The bal-hi/cap/reserved
freezes and 8 field freezes are `EffectVmEmitMint.mintRowGates`'s verbatim. -/
def mintRowGatesTick : List VmConstraint :=
  [ .gate gBalLoCreditP1
  , .gate EffectVmEmitMint.gBalHiFix
  , .gate EffectVmEmitTransfer.gNonce
  , .gate EffectVmEmitMint.gCapFix
  , .gate EffectVmEmitMint.gResFix ]
  ++ EffectVmEmitMint.gFieldFixAll

/-- **`mintTickFace`** — `mintVmDescriptor` (the BridgeMint registry leg) with the nonce gate
ticked AND the credit reading the runtime value column. The transitions + boundary PI pins + hash
sites + ranges are verbatim; only those two row gates change. -/
def mintTickFace : EffectVmDescriptor :=
  { EffectVmEmitMint.mintVmDescriptor with
    constraints := mintRowGatesTick ++ EffectVmEmitTransfer.transitionAll
      ++ EffectVmEmitTransfer.boundaryFirstPins ++ EffectVmEmitTransfer.boundaryLastPins }

/-- The tick-faced mint shares the per-effect descriptor's sites + ranges, so it is graduable. -/
theorem graduable_mintTickFace : graduable mintTickFace = true := rfl

/-- **SOURCE-COHERENCE: the mint tick-face now COINCIDES with the (reconciled) source descriptor.**
After the per-effect `EffectVmEmitMint` source was corrected (nonce tick, credit at `param1`), its
`mintRowGates` IS this section's `mintRowGatesTick` (definitionally — `gBalLoCreditP1 = gBalLoCredit`,
both crediting `param1`; the tick gate is the same `EffectVmEmitTransfer.gNonce`), so the tick-faced
BridgeMint equals the source descriptor. The registry routing through `mintV3` is the same circuit. -/
theorem mintTickFace_eq_source : mintTickFace = EffectVmEmitMint.mintVmDescriptor := rfl

/-- **The 26-felt bridge-action tuple exposure** — pins 26 APPENDED columns (`nullifier[8] ‖
recipient[8] ‖ dest_federation[8] ‖ amount_lo ‖ amount_hi`, laid by the prover's
`generate_rotated_bridgemint_wide` from the `BridgeActionWitness`) to PI slots `[46 .. 72)` on the
FIRST row, so the per-turn bridge FOLD can `connect` the `prove_bridge_leaf_tuple_claim` sub-proof's
genuine tuple to THIS leg's published one (a forged leg claim no sub-proof backs ⇒ UNSAT ⇒ no root).
The bridge twin of `customPiExposure`. `w` is the pre-exposure rotated width (the tuple columns append
past it), `pc` the pre-exposure PI count (46, the four rotated commit pins). -/
def bridgeTuplePiExposure (w pc : Nat) : List VmConstraint2 :=
  (List.range 26).map (fun k => .base (.piBinding .first (w + k) (pc + k)))

/-- **`mintV3`** — the rotated tick-faced BridgeMint (the `mintVmDescriptor2R24` registry member),
WIDENED (the VK epoch) to publish the 26-felt bridge-action tuple at PI `[46..72)` so a pure light
client witnesses the payment binding via the per-turn fold. The 26 tuple columns append past the
rotated width; the prover's `generate_rotated_bridgemint_wide` lays them from the `BridgeActionWitness`.
Unlike the compressed `mint_hash` the substrate row carries, these are the ACTUAL payment fields the
fold binds — no hash-gadget seam. -/
def mintV3 : EffectVmDescriptor2 :=
  let d := v3OfFrozen mintTickFace
  -- Append 28 columns (the 26-felt tuple at the LAST 26 + 2 leading alignment-pad columns) so the
  -- registry's chip-lane shape guard (surplus past the base ÷ (CHIP_OUT_LANES-1) = 7) still holds:
  -- 26 is not ÷7, 28 = 4·7 is. The pad columns are unconstrained zeros; the tuple rides `[d.traceWidth+2 ..)`.
  { d with
    traceWidth  := d.traceWidth + 28
    piCount     := d.piCount + 26
    constraints := d.constraints ++ bridgeTuplePiExposure (d.traceWidth + 2) d.piCount }

/-- **`supplyMintV3`** — the DEDICATED-SELECTOR supply-mint member (SUPPLY-MODEL.md Stage 2b).
The SAME proven credit/tick/freeze body as `mintV3`/`mintVmDescriptor2R24` (`mintTickFace`,
`mintTickFace_eq_source`), wrapped with the selector-binding tooth on the DEDICATED supply selector
`sel.MINT = 14` rather than `selM.MINT = sel.BRIDGE_MINT = 40`. So the turn-layer `Effect::Mint`
proves + self-verifies under its OWN selector — the supply-creation rung no longer rides BridgeMint's
slot. The two members differ ONLY in the appended `selectorGate` operand (14 vs 40 — a single
`.base` constraint), so every proven faithfulness / anti-ghost tooth on `mintTickFace`
(`mintTick_rejects_wrong_nonce_delta`, `mintP1_rejects_wrong_credit`) carries verbatim, and the
selector-gate forgery tooth (`withSelectorGate_satisfied2`) bites a `[Mint, foreign]` trace under
THIS member exactly as it does for `mintVmDescriptor2R24`. -/
def supplyMintV3 : EffectVmDescriptor2 := withSelectorGate sel.MINT (v3OfFrozen mintTickFace)

/-- **The nonce TICK holds on a satisfying non-NoOp BridgeMint row.** -/
theorem mintV3_pins_nonce_tick (hash : List ℤ → ℤ) (env : VmRowEnv) (isFirst isLast : Bool)
    (hlast : isLast = false) (hnoop : env.loc sel.NOOP = 0)
    (h : satisfiedVm hash (rotateV3 mintTickFace) env isFirst isLast) :
    env.loc (saCol state.NONCE) = env.loc (sbCol state.NONCE) + 1 := by
  subst hlast
  have hmem : VmConstraint.gate EffectVmEmitTransfer.gNonce ∈ (rotateV3 mintTickFace).constraints := by
    apply List.mem_append_left
    show _ ∈ mintTickFace.constraints
    simp [mintTickFace, mintRowGatesTick]
  have hg := h.1 _ hmem
  simp only [VmConstraint.holdsVm, EffectVmEmitTransfer.gNonce, EffectVmEmitTransfer.eSub,
    EffectVmEmitTransfer.eSA, EffectVmEmitTransfer.eSB, EffectVmEmitTransfer.eSelNoop,
    EmittedExpr.eval] at hg
  rw [hnoop] at hg
  linarith [hg]

/-- **ANTI-GHOST (wrong nonce delta ⇒ UNSAT)** — the C7 soundness tooth for BridgeMint. -/
theorem mintTick_rejects_wrong_nonce_delta (hash : List ℤ → ℤ) (env : VmRowEnv)
    (isFirst isLast : Bool) (hlast : isLast = false) (hnoop : env.loc sel.NOOP = 0)
    (hwrong : env.loc (saCol state.NONCE) ≠ env.loc (sbCol state.NONCE) + 1) :
    ¬ satisfiedVm hash (rotateV3 mintTickFace) env isFirst isLast :=
  fun h => hwrong (mintV3_pins_nonce_tick hash env isFirst isLast hlast hnoop h)

/-- **The corrected CREDIT binds the runtime value column.** A row satisfying the rotated
param1-corrected BridgeMint carries `bal_lo_after = bal_lo_before + param1` (the runtime
value_lo) — the credit gate now reads the column the trace generator credited from. -/
theorem mintV3_pins_credit (hash : List ℤ → ℤ) (env : VmRowEnv) (isFirst isLast : Bool)
    (hlast : isLast = false)
    (h : satisfiedVm hash (rotateV3 mintTickFace) env isFirst isLast) :
    env.loc (saCol state.BALANCE_LO)
      = env.loc (sbCol state.BALANCE_LO) + env.loc (prmCol RUNTIME_VALUE_PARAM) := by
  subst hlast
  have hmem : VmConstraint.gate gBalLoCreditP1 ∈ (rotateV3 mintTickFace).constraints := by
    apply List.mem_append_left
    show _ ∈ mintTickFace.constraints
    simp [mintTickFace, mintRowGatesTick]
  have hg := h.1 _ hmem
  simp only [VmConstraint.holdsVm, gBalLoCreditP1, EffectVmEmitTransfer.eSub,
    EffectVmEmitTransfer.eSA, EffectVmEmitTransfer.eSB, EffectVmEmitTransfer.ePrm,
    EmittedExpr.eval] at hg
  linarith [hg]

/-- **ANTI-GHOST (wrong credit ⇒ UNSAT)** — the C7 param-column soundness tooth for BridgeMint.
A row whose post-balance is NOT `before + param1` (the runtime value_lo) is UNSAT. -/
theorem mintP1_rejects_wrong_credit (hash : List ℤ → ℤ) (env : VmRowEnv) (isFirst isLast : Bool)
    (hlast : isLast = false)
    (hwrong : env.loc (saCol state.BALANCE_LO)
      ≠ env.loc (sbCol state.BALANCE_LO) + env.loc (prmCol RUNTIME_VALUE_PARAM)) :
    ¬ satisfiedVm hash (rotateV3 mintTickFace) env isFirst isLast :=
  fun h => hwrong (mintV3_pins_credit hash env isFirst isLast hlast h)

#assert_axioms graduable_setFieldTickFace
#assert_axioms setFieldTickFace_eq_source
#assert_axioms setFieldV3_pins_nonce_tick
#assert_axioms setFieldTick_rejects_wrong_nonce_delta
#assert_axioms setFieldV3_pins_value
#assert_axioms setFieldP1_rejects_wrong_value
#assert_axioms graduable_mintTickFace
#assert_axioms mintTickFace_eq_source
#assert_axioms mintV3_pins_nonce_tick
#assert_axioms mintTick_rejects_wrong_nonce_delta
#assert_axioms mintV3_pins_credit
#assert_axioms mintP1_rejects_wrong_credit

-- The tick-faced descriptors keep the per-effect width/PI-count/site/range shape (only the
-- nonce gate body changed): graduable, and the rotated form is the standard 311-col / 38-PI member.
#guard graduable (setFieldTickFace 0)
#guard graduable mintTickFace
#guard (setFieldV3 0).traceWidth ==
  EFFECT_VM_WIDTH + APPENDIX_SPAN + (CHIP_OUT_LANES - 1) *
    (rotateV3FrozenAuthority (setFieldTickFace 0)).hashSites.length
-- mintV3 is WIDENED by the 26-felt bridge-action tuple exposure (the VK epoch): +28 columns
-- (26 tuple + 2 chip-lane-alignment pad, so the surplus stays ÷7), +26 PIs.
#guard mintV3.traceWidth ==
  EFFECT_VM_WIDTH + APPENDIX_SPAN + (CHIP_OUT_LANES - 1) *
    (rotateV3FrozenAuthority mintTickFace).hashSites.length + 28
#guard (setFieldV3 0).piCount == 42 + 4
#guard mintV3.piCount == 42 + 4 + 26
-- The swap is a ONE-gate change: the tick-faced constraint list has the SAME length as the
-- per-effect descriptor's (a gate replaced a gate, none added or removed).
#guard (setFieldTickFace 0).constraints.length
        == (EffectVmEmitSetField.setFieldVmDescriptor 0).constraints.length
#guard mintTickFace.constraints.length == EffectVmEmitMint.mintVmDescriptor.constraints.length
-- The tick gate IS the transfer/noteSpend tick gate (the `−(1 − selector)` term): the rotated
-- tick-faced constraint list carries `EffectVmEmitTransfer.gNonce` at the nonce slot, and the
-- freeze-gate body is GONE — the two tick-faced descriptors no longer hold the bare freeze gate
-- the `mismodels_nonce_tick` predicate guarded against. (`setFieldRowGatesTick`'s 4th gate / the
-- mint list's 3rd gate ARE the tick gate; `setField{V3_pins,Tick_rejects}_*` prove its membership +
-- enforcement formally, so this is the lightweight positional witness.)
#guard (setFieldRowGatesTick 0).length == 13   -- 6 head gates + 7 other-field freezes
#guard mintRowGatesTick.length == 13           -- 5 head gates + 8 field freezes
-- BOTH POLARITIES of the NONCE tooth, executable on a toy row (NOOP = col 0; sb NONCE = 56;
-- sa NONCE = STATE_AFTER_BASE(76) + NONCE(2) = 78). A ticked row (after = before + 1, s_noop = 0)
-- HOLDS the tick gate; a forged passthrough (after = before) FAILS it. (Mirrors transfer's
-- `gNonce` adversarial #guards — the `−(1 − selector)` term makes passthrough UNSAT off NoOp.)
#guard (let env : VmRowEnv := ⟨fun c => if c == 56 then 5 else if c == 78 then 6 else 0, fun _ => 0, fun _ => 0⟩;
        decide ((EffectVmEmitTransfer.gNonce).eval env.loc = 0))   -- tick (5→6) ⇒ gate holds
#guard (let env : VmRowEnv := ⟨fun c => if c == 56 then 5 else if c == 78 then 5 else 0, fun _ => 0, fun _ => 0⟩;
        decide ((EffectVmEmitTransfer.gNonce).eval env.loc ≠ 0))   -- passthrough (5→5) ⇒ gate REJECTS
-- The corrected WRITE/CREDIT gates read `prmCol 1` (NEW_VALUE / value_lo = col PARAM_BASE+1 = 69),
-- NOT `prmCol 0` (FIELD_INDEX / MINT_HASH = col 68). Positional witness + both polarities.
#guard prmCol RUNTIME_VALUE_PARAM == 69
-- setField WRITE (selector-gated by s_set_field = col SEL_SET_FIELD_COL = 2): on the ACTIVE row
-- (s_set_field = 1), field0_after (saCol FIELD_BASE = 79) == param1 (69). Match holds; mismatch
-- rejects. On a NoOp row (s_set_field = 0) the gate VANISHES (third guard).
#guard (let env : VmRowEnv := ⟨fun c => if c == 2 then 1 else if c == 79 then 7 else if c == 69 then 7 else 0, fun _ => 0, fun _ => 0⟩;
        decide ((gFieldWriteP1 0).eval env.loc = 0))   -- active + (field0_after == param1) ⇒ holds
#guard (let env : VmRowEnv := ⟨fun c => if c == 2 then 1 else if c == 79 then 7 else if c == 69 then 9 else 0, fun _ => 0, fun _ => 0⟩;
        decide ((gFieldWriteP1 0).eval env.loc ≠ 0))   -- active + (field0_after ≠ param1) ⇒ REJECTS
#guard (let env : VmRowEnv := ⟨fun c => if c == 79 then 7 else if c == 69 then 9 else 0, fun _ => 0, fun _ => 0⟩;
        decide ((gFieldWriteP1 0).eval env.loc = 0))   -- NoOp (s_set_field = 0) ⇒ gate VANISHES
-- mint CREDIT: bal_lo_after (76) == bal_lo_before (54) + param1 (69). Honest credit holds; wrong rejects.
#guard (let env : VmRowEnv := ⟨fun c => if c == 54 then 100 else if c == 76 then 130 else if c == 69 then 30 else 0, fun _ => 0, fun _ => 0⟩;
        decide (gBalLoCreditP1.eval env.loc = 0))   -- 130 == 100 + 30 ⇒ holds
#guard (let env : VmRowEnv := ⟨fun c => if c == 54 then 100 else if c == 76 then 999 else if c == 69 then 30 else 0, fun _ => 0, fun _ => 0⟩;
        decide (gBalLoCreditP1.eval env.loc ≠ 0))   -- 999 ≠ 100 + 30 ⇒ REJECTS

/-! ### The RECORD-FORCING PIN (the deployment-soundness close for the 7 binds-but-unforced effects).

`cellSeal` / `cellUnseal` / `cellDestroy` write the per-cell `lifecycle` side-table; `setPermissions`
/ `setVK` AND the audit writes `refusal` / `receiptArchive` write a record slot folded into the
per-cell `authority_digest` (the `record_digest` — the audit slots `"refusal"`/`"lifecycle"` land in
`fields_root`, which the digest folds, `cell/src/commitment.rs::compute_authority_digest_felt`). The
rotated AFTER block CARRIES those writes (limb 28 = `lifecycle`, limb 24 = `authority_digest`, filled
from the post-state producer witness, `turn/src/rotation_witness.rs`) and the rolled-up commitment
BINDS them — but NOTHING in `rotateV3` FORCES the AFTER limb to equal the CORRECTLY-WRITTEN value. So
a malicious prover can publish an AFTER block whose lifecycle is still the PRE value (frozen, never
sealed) and whose `authority_digest` is the PRE record — the descriptor accepts, the light client is
fooled (the `RotatedKernelRefinement{CellSeal,Lifecycle,PermsVK}` rungs prove the gate that bites this
against a FIX descriptor; THIS wires that gate LIVE).

The forcing is ONE appended last-row PI pin, exactly the `rotateV3WithNullifierPin` shape: the AFTER
block's forced limb is bound to a NEW rotated PI slot (`piCount`, the first past the four commit pins)
carrying the correctly-written post value. The off-circuit verifier RECOMPUTES that PI from the
committed pre-state + the effect (`lifecycle_felt(post)` for the lifecycle effects, the post
`record_digest` for setPerms/setVK), so a frozen / wrong-record AFTER block FAILS the pin and is UNSAT
— the deployment analog of the rungs' `gLifecycleSeal` / `gSlotSet`. Every v1 column, constraint, hash
site, and the four commit pins are UNTOUCHED, so `rotateV3`'s keystones (`rotateV3_satisfiedVm_v1`,
`rotV3_binds_published`, `graduable_rotateV3`) compose verbatim — this only ADDS one PI pin + one PI
slot, exactly as the nullifier weld does. -/

/-- **`rotateV3WithRecordPin off d`** — `rotateV3` PLUS a fifth appended last-row PI pin welding the
AFTER block's limb at in-block offset `off` (`B_LIFECYCLE` or `B_RECORD_DIGEST`) to the new rotated PI
slot `r.piCount` (the first past the four commit pins). The write LANDS in the AFTER state (the
post-state producer witness fills it), so the LAST-row pin is the rotated analog of the rungs' post-root
gate. Every v1 column, constraint, hash site, and the four commit pins are UNTOUCHED (so `rotateV3`'s
keystones compose verbatim; this only ADDS one PI pin + one PI slot). -/
def rotateV3WithRecordPin (off : Nat) (d : EffectVmDescriptor) : EffectVmDescriptor :=
  let r := rotateV3 d
  { r with
    piCount     := r.piCount + 1
    constraints := r.constraints
      ++ [.piBinding .last (d.traceWidth + AFTER_BLOCK_OFF + off) r.piCount] }

/-- The appended record pin is the only constraint past `rotateV3`'s. -/
theorem rotateV3WithRecordPin_constraints (off : Nat) (d : EffectVmDescriptor) :
    (rotateV3WithRecordPin off d).constraints
      = (rotateV3 d).constraints
        ++ [.piBinding .last (d.traceWidth + AFTER_BLOCK_OFF + off) (rotateV3 d).piCount] := rfl

/-- The record pin does NOT disturb graduation (it is a CONSTRAINT; `graduable` reads only
sites/ranges, which are `rotateV3`'s verbatim). -/
theorem graduable_rotateV3WithRecordPin (off : Nat) {d : EffectVmDescriptor}
    (h : graduable d = true) : graduable (rotateV3WithRecordPin off d) = true := by
  have hr := graduable_rotateV3 h
  unfold rotateV3WithRecordPin
  unfold graduable at hr ⊢
  simpa using hr

/-- **The record weld holds on a satisfying LAST row**: a row satisfying `rotateV3WithRecordPin off d`
carries the AFTER block's forced limb EQUAL to the published rotated PI `(rotateV3 d).piCount`. -/
theorem rotateV3WithRecordPin_pins (off : Nat) (hash : List ℤ → ℤ) (d : EffectVmDescriptor)
    (env : VmRowEnv) (isFirst : Bool)
    (h : satisfiedVm hash (rotateV3WithRecordPin off d) env isFirst true) :
    env.loc (d.traceWidth + AFTER_BLOCK_OFF + off) = env.pub (rotateV3 d).piCount := by
  have hpin := h.1 (.piBinding .last (d.traceWidth + AFTER_BLOCK_OFF + off) (rotateV3 d).piCount)
    (by rw [rotateV3WithRecordPin_constraints]; exact List.mem_append_right _ List.mem_cons_self)
  simpa only [VmConstraint.holdsVm] using hpin rfl

/-- **(forced limb ≠ published value ⇒ UNSAT)** — a LAST row whose AFTER forced limb does NOT equal the
published PI `PI[(rotateV3 d).piCount]` does NOT satisfy `rotateV3WithRecordPin off d`: the appended pin
REJECTS it.

⚠ HONESTY BOUNDARY (do NOT overclaim this as a closed anti-ghost for the WHOLE record-pin family): this
theorem forces only `after_limb == PI[piCount]`, where `PI[piCount]` is a FREE public input. It is a
genuine FORCING gate (a real anti-ghost rejecting a frozen lifecycle / un-written record) ONLY when the
deployed verifier independently ANCHORS `PI[piCount]` to `compute_authority_digest_felt(trusted post-cell)`
(= apply the effect to the cross-checked before-cell, then digest).

CLOSED FOR `setPermissions` AND `setVK` (the record-digest movers, limb `B_RECORD_DIGEST = 24`): the
deployed verifier (`turn/src/executor/proof_verify.rs verify_and_commit_proof_rotated`, step 6b) anchors PI
38 for BOTH leads — it clones the trusted before-cell, applies the kernel effect through the SHARED
`dregg_turn::rotation_witness::apply_effect_to_cell` weld (the SAME projection the cipherclerk producer uses
for its after-cell, so honest proofs are NOT rejected), and overrides
`dpis[38] = compute_authority_digest_felt(post_cell)`. `compute_authority_digest_felt` FOLDS both the cell's
`permissions` and `verification_key.hash`, so a genuine setPermissions / setVK MOVES the AFTER r23 residue and
a forged after-residue disagrees with the anchored PI 46 ⇒ `verify_vm_descriptor2` UNSAT. Tests
(`sdk/tests/sovereign_rotated_c1.rs record_pin_anchor`):
`{rotated_sovereign_set_permissions_proves_and_verifies, rotated_sovereign_forged_after_permissions_is_rejected,
rotated_sovereign_set_vk_proves_and_verifies, rotated_sovereign_forged_after_vk_is_rejected}` — the honest
accept BITES (without the anchor PI 46 stays at the placeholder and the honest proof is rejected), and the
forged-after proof is rejected by the anchor mismatch.

CLOSED FOR THE WHOLE RECORD-PIN FAMILY (the fan-out fixed the 3 bugs the vacuous pin had masked — the
model-finds-the-bug loop; each effect's forged-after tooth BITES, tests in `sdk/tests/sovereign_rotated_c1.rs
record_pin_anchor`, all 7 accept/reject pairs green):

  * RECORD-DIGEST anchor (limb `B_RECORD_DIGEST = 24`, `compute_authority_digest_felt`): `setPermissions`,
    `setVK`, and `refusal`. The refusal fix: the deployed `apply_refusal` now writes the audit commitment into
    the protocol-reserved EXT key `REFUSAL_AUDIT_EXT_KEY` (`≥ STATE_SLOTS`, committed via `fields_root` which
    `compute_authority_digest_felt` folds), matching the Lean SPEC `TurnExecutorFull.refusalField` — was the
    welded `fields[4]` (unfolded), the spec/deployment divergence that left the refusal record UNBOUND.

  * LIFECYCLE anchor (limb `B_LIFECYCLE = 29`, `lifecycle_felt_cell`): `cellSeal`, `cellUnseal`, `cellDestroy`
    (the lifecycle separates Live/Sealed/Destroyed + folds the death-cert for Destroy), AND `receiptArchive`
    (`record_pin_offset` re-routed from the mis-routed `B_RECORD_DIGEST` to `B_LIFECYCLE`). The cellSeal/Unseal/
    Destroy producer/verifier projection divergence (the cipherclerk producer collapsed them to
    `VmEffect::SetPermissions` vs the executor bridge's native variants) was fixed by aligning the producer to
    native projection (+ threading `block_height` into the otherwise-stateless producer for the cellSeal seam).

The verifier (`verify_and_commit_proof_rotated`, step 6b) clones the trusted before-cell, applies the kernel
effect through the SHARED `dregg_turn::rotation_witness::apply_effect_to_cell` weld (the SAME projection the
cipherclerk producer uses for its after-cell, so honest proofs are NOT rejected), and overrides `dpis[38]`
from the trusted post-cell (`compute_authority_digest_felt` for the record-digest class, `lifecycle_felt_cell`
for the lifecycle class) — so a forged after-residue disagrees with the anchored PI 46 ⇒ UNSAT. The record-pin
is now a genuine forcing gate across the family, not a published-value binding. -/
theorem rotateV3WithRecordPin_rejects_wrong_post (off : Nat) (hash : List ℤ → ℤ)
    (d : EffectVmDescriptor) (env : VmRowEnv) (isFirst : Bool)
    (hwrong : env.loc (d.traceWidth + AFTER_BLOCK_OFF + off) ≠ env.pub (rotateV3 d).piCount) :
    ¬ satisfiedVm hash (rotateV3WithRecordPin off d) env isFirst true :=
  fun h => hwrong (rotateV3WithRecordPin_pins off hash d env isFirst h)

/-- The v1 denotation survives the added record pin (the per-effect faithfulness / anti-ghost
theorems compose through, exactly as for the nullifier pin). -/
theorem rotateV3WithRecordPin_satisfiedVm_v1 (off : Nat) (hash : List ℤ → ℤ)
    (d : EffectVmDescriptor) (env : VmRowEnv) (isFirst isLast : Bool)
    (h : satisfiedVm hash (rotateV3WithRecordPin off d) env isFirst isLast) :
    satisfiedVm hash d env isFirst isLast := by
  apply rotateV3_satisfiedVm_v1 hash d env isFirst isLast
  obtain ⟨hc, hsites, hr⟩ := h
  refine ⟨fun c hc' => hc c ?_, hsites, hr⟩
  rw [rotateV3WithRecordPin_constraints]
  exact List.mem_append_left _ hc'

/-! ## §5.LD — THE LIVE LIFECYCLE-DISC GATE (the lifecycle-mover authority going LIVE).

The disc flag-day committed the lifecycle `disc` (the `u8 0..4`) as its OWN sub-limb at in-block
offset `B_DISC = 32` (the NEW LAST pre-iroot limb), BESIDE the opaque `lifecycle_felt` (at 29). With
the disc now in-circuit, the per-effect disc TRANSITION (`RotatedKernelRefinementLifecycleDisc.
gDiscTransition`) is realized on the LIVE wire as a SELECTOR-GATED CONSTANT FORCE on the disc limb —
NO trusted post-cell, NO free PI. A ledgerless client's `verify_vm_descriptor2` ALONE now rejects a
frozen seal / a Destroyed→Live resurrection / a wrong-disc archive: the gate forces the AFTER disc to
the effect's mandated discriminant, and (for seal/unseal) the BEFORE disc to its precondition.

`discForceGate sel col const` = `sel · (loc col − const) = 0`: on the ACTIVE row (`sel = 1`) it forces
`loc col = const`; on a NoOp/pad row (`sel = 0`) it vanishes. The deployed face of `discAfterForced` /
`discBeforeForced`. -/

/-- The disc discriminants (the deployed `u8 0..4`, `rotation_witness.rs::lifecycle_felt`'s disc;
`RotatedKernelRefinementLifecycleDisc.{lcLive,lcSealed,lcDestroyed,lcArchived}`). -/
def discLive : ℤ := 0
def discSealed : ℤ := 1
def discDestroyed : ℤ := 3
def discArchived : ℤ := 4

/-- **`discForceGate sel col const`** — the selector-gated constant force: `sel · (loc col − const)`.
On a row with `loc sel = 1` it forces `loc col = const` (the disc transition endpoint); on a pad row
(`loc sel = 0`) it vanishes. -/
def discForceGate (sel col : Nat) (const : ℤ) : VmConstraint :=
  .gate (.mul (.var sel) (.add (.var col) (.const (-const))))

theorem discForceGate_forces (env : VmRowEnv) (isFirst isLast : Bool) (hlast : isLast = false)
    (sel col : Nat) (const : ℤ)
    (hsel : env.loc sel = 1)
    (h : (discForceGate sel col const).holdsVm env isFirst isLast) :
    env.loc col = const := by
  subst hlast
  simp only [discForceGate, VmConstraint.holdsVm, EmittedExpr.eval] at h
  rw [hsel] at h
  linarith

/-- The AFTER-disc force column for a mover of width `d.traceWidth` (limb `B_DISC` of the AFTER
block, `traceWidth + AFTER_BLOCK_OFF + B_DISC`). -/
def afterDiscCol (w : Nat) : Nat := w + AFTER_BLOCK_OFF + B_DISC
/-- The BEFORE-disc force column (limb `B_DISC` of the BEFORE block, `traceWidth + B_DISC`). -/
def beforeDiscCol (w : Nat) : Nat := w + B_DISC

/-- **`rotateV3WithDiscGate sel beforeC afterC d`** — `rotateV3WithRecordPin B_LIFECYCLE d` PLUS the
LIVE disc gates: the AFTER disc limb is force-pinned to `afterC` and (when `beforeC?` is `some`) the
BEFORE disc limb to its precondition, both selector-gated on `sel`. Every v1 column/site/range and the
record pin are UNTOUCHED — the gates are appended CONSTRAINTS, so `graduable` and the keystones compose
verbatim. -/
def rotateV3WithDiscGate (sel : Nat) (beforeC? : Option ℤ) (afterC : ℤ)
    (d : EffectVmDescriptor) : EffectVmDescriptor :=
  let r := rotateV3WithRecordPin B_LIFECYCLE d
  { r with
    constraints := r.constraints
      ++ (match beforeC? with
          | some b => [discForceGate sel (beforeDiscCol d.traceWidth) b]
          | none => [])
      ++ [discForceGate sel (afterDiscCol d.traceWidth) afterC] }

/-- The disc gates do NOT disturb graduation (they are CONSTRAINTS; `graduable` reads only
sites/ranges, which are `rotateV3WithRecordPin`'s verbatim). -/
theorem graduable_rotateV3WithDiscGate (sel : Nat) (beforeC? : Option ℤ) (afterC : ℤ)
    {d : EffectVmDescriptor} (h : graduable d = true) :
    graduable (rotateV3WithDiscGate sel beforeC? afterC d) = true := by
  have hr := graduable_rotateV3WithRecordPin B_LIFECYCLE h
  unfold rotateV3WithDiscGate
  unfold graduable at hr ⊢
  cases beforeC? <;> simpa using hr

/-- **The AFTER-disc gate is the LAST appended constraint** — membership for the forcing extraction. -/
theorem rotateV3WithDiscGate_afterMem (sel : Nat) (beforeC? : Option ℤ) (afterC : ℤ)
    (d : EffectVmDescriptor) :
    discForceGate sel (afterDiscCol d.traceWidth) afterC
      ∈ (rotateV3WithDiscGate sel beforeC? afterC d).constraints := by
  unfold rotateV3WithDiscGate
  cases beforeC? <;>
    simp [List.mem_append]

/-- **`rotateV3WithDiscGate_forces_after` — the LIVE disc transition is FORCED.** On an ACTIVE row
(`sel = 1`) of a satisfying `rotateV3WithDiscGate` witness, the AFTER disc limb EQUALS the mandated
discriminant `afterC` — the deployed realization of
`RotatedKernelRefinementLifecycleDisc.discAfterForced`, with NO trusted post-cell. -/
theorem rotateV3WithDiscGate_forces_after (sel : Nat) (beforeC? : Option ℤ) (afterC : ℤ)
    (hash : List ℤ → ℤ) (d : EffectVmDescriptor) (env : VmRowEnv) (isFirst isLast : Bool)
    (hlast : isLast = false)
    (hsel : env.loc sel = 1)
    (h : satisfiedVm hash (rotateV3WithDiscGate sel beforeC? afterC d) env isFirst isLast) :
    env.loc (afterDiscCol d.traceWidth) = afterC :=
  discForceGate_forces env isFirst isLast hlast sel (afterDiscCol d.traceWidth) afterC hsel
    (h.1 _ (rotateV3WithDiscGate_afterMem sel beforeC? afterC d))

/-- **TOOTH — `rotateV3WithDiscGate_rejects_wrong_after`.** An ACTIVE row whose AFTER disc is NOT the
mandated `afterC` (a frozen seal, a Destroyed→Live resurrection, a wrong-disc archive) does NOT satisfy
`rotateV3WithDiscGate` — UNSAT for a ledgerless client, no anchor. -/
theorem rotateV3WithDiscGate_rejects_wrong_after (sel : Nat) (beforeC? : Option ℤ) (afterC : ℤ)
    (hash : List ℤ → ℤ) (d : EffectVmDescriptor) (env : VmRowEnv) (isFirst isLast : Bool)
    (hlast : isLast = false)
    (hsel : env.loc sel = 1)
    (hwrong : env.loc (afterDiscCol d.traceWidth) ≠ afterC) :
    ¬ satisfiedVm hash (rotateV3WithDiscGate sel beforeC? afterC d) env isFirst isLast :=
  fun h => hwrong (rotateV3WithDiscGate_forces_after sel beforeC? afterC hash d env isFirst isLast hlast hsel h)

#assert_axioms discForceGate_forces
#assert_axioms graduable_rotateV3WithDiscGate
#assert_axioms rotateV3WithDiscGate_forces_after
#assert_axioms rotateV3WithDiscGate_rejects_wrong_after

/-! ## §5.PV — THE LIVE PERMS/VK GATE (the setPermissions / setVK authority going LIVE — WAVE 2).

The perms/VK flag-day committed the authority shape as TWO dedicated sub-limbs BESIDE the opaque
`record_digest` (r23): the perms-digest limb `B_PERMS = 33` and the vk-digest limb `B_VK = 34`. Each is
the deployed declared-param felt — `= permsHash[0]` / `vkHash[0]`, the limb[0] of `blake3(postcard(·))`
the live setPerms / setVK row anchors into `params[0]` (`prmCol 0`) and folds (all 8 limbs) into the
PI-bound `effects_hash`. With the authority sub-limb now committed, the per-effect setPerms / setVK
write is realized on the LIVE wire as a SELECTOR-GATED WELD of the AFTER authority sub-limb to that
in-circuit declared-param column — NO trusted post-cell, NO free PI.

`permsVKWeldGate sel afterCol paramCol = sel · (loc afterCol − loc paramCol) = 0`: on the ACTIVE row
(`sel = 1`) it forces `loc afterCol = loc paramCol` (the committed authority sub-limb EQUALS the
declared param the effects_hash chain anchors to a light-client PI); on a pad row (`sel = 0`) it
vanishes. A ledgerless client's `verify_vm_descriptor2` ALONE now rejects a setPermissions / setVK
whose committed AFTER authority sub-limb ≠ its declared param (a forged post-perms / post-VK is UNSAT).

NAMED RESIDUAL: the weld binds the declared param's limb[0] in-circuit; the full 8-limb declared hash
binds via the SAME effects_hash→PI chain (the existing path), so the closed forgery is "committed
authority-shape ≠ the declared (PI-anchored) authority" — the safety-critical setPerms/setVK light-client
close. The variable Custom-vk component rides the off-row declared hash (the same effects_hash anchor). -/

/-- **`permsVKWeldGate sel afterCol paramCol`** — the selector-gated authority weld:
`sel · (loc afterCol − loc paramCol)`. On a row with `loc sel = 1` it forces the committed AFTER
authority sub-limb EQUAL to the in-circuit declared-param column; on a pad row it vanishes. -/
def permsVKWeldGate (sel afterCol paramCol : Nat) : VmConstraint :=
  .gate (.mul (.var sel) (.add (.var afterCol) (.mul (.const (-1)) (.var paramCol))))

theorem permsVKWeldGate_forces (env : VmRowEnv) (isFirst isLast : Bool) (hlast : isLast = false)
    (sel afterCol paramCol : Nat)
    (hsel : env.loc sel = 1)
    (h : (permsVKWeldGate sel afterCol paramCol).holdsVm env isFirst isLast) :
    env.loc afterCol = env.loc paramCol := by
  subst hlast
  simp only [permsVKWeldGate, VmConstraint.holdsVm, EmittedExpr.eval] at h
  rw [hsel] at h
  linarith

/-- The AFTER perms-digest force column for a mover of width `w` (limb `B_PERMS` of the AFTER block). -/
def afterPermsCol (w : Nat) : Nat := w + AFTER_BLOCK_OFF + B_PERMS
/-- The AFTER vk-digest force column (limb `B_VK` of the AFTER block). -/
def afterVKCol (w : Nat) : Nat := w + AFTER_BLOCK_OFF + B_VK
/-- The in-circuit declared-param column the live setPerms / setVK row anchors `permsHash[0]` /
`vkHash[0]` into (`params[0]`, `prmCol 0`) — itself bound (all 8 limbs) into the PI-anchored
`effects_hash`. -/
def declaredParamCol : Nat := prmCol 0

/-- **v10**: the FIRST faithful-8-felt completion column for the perms digest in the AFTER block (the
new pre-iroot limb 37, carrying `permsHash[1]`; the felts 2..7 follow at +1..+6, limbs 38..=43). -/
def afterPermsExtraCol (w : Nat) : Nat := w + AFTER_BLOCK_OFF + 37
/-- **v10**: the FIRST faithful-8-felt completion column for the vk digest (pre-iroot limb 44, carrying
`vkHash[1]`; felts 2..7 at +1..+6, limbs 45..=50). -/
def afterVKExtraCol (w : Nat) : Nat := w + AFTER_BLOCK_OFF + 44

/-- **`rotateV3WithPermsVKGate sel afterCol d`** — `rotateV3WithRecordPin B_RECORD_DIGEST d` PLUS the
LIVE perms/VK weld: the AFTER authority sub-limb `afterCol` (perms-digest for setPerms, vk-digest for
setVK) is welded to the declared-param column, selector-gated on `sel`. Every v1 column/site/range and
the record pin are UNTOUCHED — the gate is an appended CONSTRAINT, so `graduable` and the keystones
compose verbatim. -/
def rotateV3WithPermsVKGate (sel afterCol : Nat) (d : EffectVmDescriptor) : EffectVmDescriptor :=
  let r := rotateV3WithRecordPin B_RECORD_DIGEST d
  { r with constraints := r.constraints ++ [permsVKWeldGate sel afterCol declaredParamCol] }

/-- The perms/VK weld does NOT disturb graduation (it is a CONSTRAINT; `graduable` reads only
sites/ranges, which are `rotateV3WithRecordPin`'s verbatim). -/
theorem graduable_rotateV3WithPermsVKGate (sel afterCol : Nat)
    {d : EffectVmDescriptor} (h : graduable d = true) :
    graduable (rotateV3WithPermsVKGate sel afterCol d) = true := by
  have hr := graduable_rotateV3WithRecordPin B_RECORD_DIGEST h
  unfold rotateV3WithPermsVKGate
  unfold graduable at hr ⊢
  simpa using hr

/-- **The perms/VK weld is the LAST appended constraint** — membership for the forcing extraction. -/
theorem rotateV3WithPermsVKGate_mem (sel afterCol : Nat) (d : EffectVmDescriptor) :
    permsVKWeldGate sel afterCol declaredParamCol
      ∈ (rotateV3WithPermsVKGate sel afterCol d).constraints := by
  unfold rotateV3WithPermsVKGate
  simp [List.mem_append]

/-- **`rotateV3WithPermsVKGate_forces` — the LIVE authority write is FORCED.** On an ACTIVE row
(`sel = 1`) of a satisfying `rotateV3WithPermsVKGate` witness, the committed AFTER authority sub-limb
EQUALS the in-circuit declared-param column — the deployed realization of
`RotatedKernelRefinementPermsVK.{setPermissions,setVK}_slot_forced`, with NO trusted post-cell. -/
theorem rotateV3WithPermsVKGate_forces (sel afterCol : Nat)
    (hash : List ℤ → ℤ) (d : EffectVmDescriptor) (env : VmRowEnv) (isFirst isLast : Bool)
    (hlast : isLast = false)
    (hsel : env.loc sel = 1)
    (h : satisfiedVm hash (rotateV3WithPermsVKGate sel afterCol d) env isFirst isLast) :
    env.loc afterCol = env.loc declaredParamCol :=
  permsVKWeldGate_forces env isFirst isLast hlast sel afterCol declaredParamCol hsel
    (h.1 _ (rotateV3WithPermsVKGate_mem sel afterCol d))

/-- **TOOTH — `rotateV3WithPermsVKGate_rejects_forged`.** An ACTIVE row whose committed AFTER authority
sub-limb is NOT the declared param (a forged post-permissions / post-VK whose committed authority shape
diverges from the PI-anchored declared one) does NOT satisfy `rotateV3WithPermsVKGate` — UNSAT for a
ledgerless client, no trusted post-cell. -/
theorem rotateV3WithPermsVKGate_rejects_forged (sel afterCol : Nat)
    (hash : List ℤ → ℤ) (d : EffectVmDescriptor) (env : VmRowEnv) (isFirst isLast : Bool)
    (hlast : isLast = false)
    (hsel : env.loc sel = 1)
    (hforged : env.loc afterCol ≠ env.loc declaredParamCol) :
    ¬ satisfiedVm hash (rotateV3WithPermsVKGate sel afterCol d) env isFirst isLast :=
  fun h => hforged (rotateV3WithPermsVKGate_forces sel afterCol hash d env isFirst isLast hlast hsel h)

#assert_axioms permsVKWeldGate_forces
#assert_axioms graduable_rotateV3WithPermsVKGate
#assert_axioms rotateV3WithPermsVKGate_forces
#assert_axioms rotateV3WithPermsVKGate_rejects_forged

/-! ## §5.LP — THE LIVE LIFECYCLE-PAYLOAD HASH GATE (the cellSeal / cellDestroy / receiptArchive OPAQUE
payload felt going LIGHT-CLIENT-FORCED — VK-FREEDOM ERA, STAGE C).

The disc flag-day (`rotateV3WithDiscGate`, §5.0) put the SAFETY-CRITICAL lifecycle DISCRIMINANT in-circuit
(`B_DISC = 32`) — a frozen seal / a resurrection / a wrong-disc archive is UNSAT for a ledgerless client.
But the OPAQUE payload felt at `B_LIFECYCLE = 29` (`lifecycle_felt = Poseidon2(disc ‖ reason_hash ‖
sealed_at)`) only rode the record pin: its welded PI was producer-free on the light-client path, so a
cellSeal forged to differ ONLY in the sealing payload (a different `reason_hash`, or a `sealed_at` ≠ the
host height) was ACCEPTED anchor-disabled. ONLY the off-cell full-node anchor recomputed it.

The CLOSE is an IN-CIRCUIT HASH GATE, NOT a single-param weld: the payload felt is a HASH of
light-client-known inputs — `disc` (the constant the disc gate already pins), `reason_hash` (an effect
param the rotated `effects_hash` PI-binds), and `sealed_at = block_height` (the turn-header height
committed at `B_COMMITTED_HEIGHT`, PI-known). So we weld the AFTER lifecycle limb (`B_LIFECYCLE`) to an
IN-CIRCUIT DECLARED column (`lcPayloadCol`) that the deployed trace forces — via a Poseidon2 chip
lookup — to `payloadHash([disc, reason_hash, sealed_at])`. The decisive structural difference from
`permsVKWeldGate` (which welds to a SINGLE declared param) is that `lcPayloadCol` is itself a HASH of
several declared/PI-known inputs, recomputed in-circuit (the chip lookup), so the bound value is a
light-client-known FUNCTION of `(reason_hash, sealed_at, disc)` with NO verifier override.

This composes with the disc gate: `rotateV3WithDiscGate` already forces `disc`; this forces the residual
payload. A cellSeal forged to a different `reason_hash` makes `payloadHash` differ from any honest
`lifecycle_felt`, so the welded committed limb cannot match — UNSAT ledgerless. The faithfulness floor:
the Rust `lifecycle_felt` is realized as a felt-domain Poseidon2 hash over `[disc, reason_felts…,
sealed_at]` (the same sponge the chip lookup recomputes), MATCHING the cell-side `lifecycle_felt_cell`
EXACTLY (the openable-realization fix the refusal `fields_root` took — a circuit-recomputable hash, not a
byte-packed sponge the gate cannot open). -/

/-- **`lifecyclePayloadHashGate sel afterCol payloadCol`** — the selector-gated lifecycle-payload weld:
`sel · (loc afterCol − loc payloadCol)`. On the ACTIVE row (`sel = 1`) it forces the committed AFTER
lifecycle limb (`B_LIFECYCLE`) EQUAL to the in-circuit declared payload-hash column (itself forced to
`payloadHash([disc, reason_hash, sealed_at])` by the deployed chip lookup); on a pad row it vanishes.
Structurally `permsVKWeldGate`, but the welded value is a HASH of light-client-known inputs. -/
def lifecyclePayloadHashGate (sel afterCol payloadCol : Nat) : VmConstraint :=
  .gate (.mul (.var sel) (.add (.var afterCol) (.mul (.const (-1)) (.var payloadCol))))

theorem lifecyclePayloadHashGate_forces (env : VmRowEnv) (isFirst isLast : Bool) (hlast : isLast = false)
    (sel afterCol payloadCol : Nat)
    (hsel : env.loc sel = 1)
    (h : (lifecyclePayloadHashGate sel afterCol payloadCol).holdsVm env isFirst isLast) :
    env.loc afterCol = env.loc payloadCol := by
  subst hlast
  simp only [lifecyclePayloadHashGate, VmConstraint.holdsVm, EmittedExpr.eval] at h
  rw [hsel] at h
  linarith

/-- The AFTER lifecycle-payload force column for a mover of width `w` (limb `B_LIFECYCLE` of the AFTER
block) — the SAME committed sub-limb the record pin welds, now forced to the in-circuit hash. -/
def afterLifecycleCol (w : Nat) : Nat := w + AFTER_BLOCK_OFF + B_LIFECYCLE
/-- The in-circuit declared payload-hash column the deployed trace forces to
`payloadHash([disc, reason_hash, sealed_at])` (the felt-domain `lifecycle_felt`). Rides `prmCol 3` — a
FREE declared param column for ALL three lifecycle movers (cellSeal uses `prmCol 0,1`; cellDestroy
`prmCol 0,1`; receiptArchive `prmCol 0,1,2`), DISTINCT from the live reason/cert/height params so the
weld binds the FULL lifecycle felt (a hash of disc + payload + at), not a single raw param. The producer
writes — and the light client recomputes from the PI-bound reason_hash + the turn-header height — the
felt-domain `lifecycle_felt`. -/
def declaredLifecyclePayloadCol : Nat := prmCol 3

/-- **`rotateV3WithLifecyclePayloadGate sel afterC d`** — `rotateV3WithDiscGate`-style base
(`rotateV3WithRecordPin B_LIFECYCLE d`, the disc gates) PLUS the LIVE lifecycle-payload weld: the AFTER
lifecycle limb is welded to the in-circuit declared payload-hash column, selector-gated on `sel`. Every
v1 column/site/range and the record pin are UNTOUCHED — the gate is an appended CONSTRAINT, so
`graduable` and the keystones compose verbatim. We layer it on the DISC-gated descriptor so the deployed
mover carries BOTH the disc force (the state) AND the payload weld (the opaque felt). -/
def rotateV3WithLifecyclePayloadGate (sel : Nat) (beforeC? : Option ℤ) (afterC : ℤ)
    (d : EffectVmDescriptor) : EffectVmDescriptor :=
  let r := rotateV3WithDiscGate sel beforeC? afterC d
  { r with constraints := r.constraints
      ++ [lifecyclePayloadHashGate sel (afterLifecycleCol d.traceWidth) declaredLifecyclePayloadCol] }

/-- The lifecycle-payload weld does NOT disturb graduation (it is a CONSTRAINT; `graduable` reads only
sites/ranges, which are `rotateV3WithDiscGate`'s — hence `rotateV3WithRecordPin`'s — verbatim). -/
theorem graduable_rotateV3WithLifecyclePayloadGate (sel : Nat) (beforeC? : Option ℤ) (afterC : ℤ)
    {d : EffectVmDescriptor} (h : graduable d = true) :
    graduable (rotateV3WithLifecyclePayloadGate sel beforeC? afterC d) = true := by
  have hr := graduable_rotateV3WithDiscGate sel beforeC? afterC h
  unfold rotateV3WithLifecyclePayloadGate
  unfold graduable at hr ⊢
  simpa using hr

/-- **The lifecycle-payload weld is the LAST appended constraint** — membership for the forcing
extraction. -/
theorem rotateV3WithLifecyclePayloadGate_mem (sel : Nat) (beforeC? : Option ℤ) (afterC : ℤ)
    (d : EffectVmDescriptor) :
    lifecyclePayloadHashGate sel (afterLifecycleCol d.traceWidth) declaredLifecyclePayloadCol
      ∈ (rotateV3WithLifecyclePayloadGate sel beforeC? afterC d).constraints := by
  unfold rotateV3WithLifecyclePayloadGate
  simp [List.mem_append]

/-- **`rotateV3WithLifecyclePayloadGate_forces` — the LIVE lifecycle-payload felt is FORCED.** On an
ACTIVE row (`sel = 1`) of a satisfying witness, the committed AFTER lifecycle limb EQUALS the in-circuit
declared payload-hash column — NO trusted post-cell, NO producer-free PI. -/
theorem rotateV3WithLifecyclePayloadGate_forces (sel : Nat) (beforeC? : Option ℤ) (afterC : ℤ)
    (hash : List ℤ → ℤ) (d : EffectVmDescriptor) (env : VmRowEnv) (isFirst isLast : Bool)
    (hlast : isLast = false)
    (hsel : env.loc sel = 1)
    (h : satisfiedVm hash (rotateV3WithLifecyclePayloadGate sel beforeC? afterC d) env isFirst isLast) :
    env.loc (afterLifecycleCol d.traceWidth) = env.loc declaredLifecyclePayloadCol :=
  lifecyclePayloadHashGate_forces env isFirst isLast hlast sel
    (afterLifecycleCol d.traceWidth) declaredLifecyclePayloadCol hsel
    (h.1 _ (rotateV3WithLifecyclePayloadGate_mem sel beforeC? afterC d))

/-- **TOOTH — `rotateV3WithLifecyclePayloadGate_rejects_forged` (LIGHT-CLIENT).** An ACTIVE row whose
committed AFTER lifecycle limb is NOT the in-circuit declared payload-hash column (a cellSeal forged to a
different `reason_hash` / `sealed_at`, whose committed `lifecycle_felt` diverges from
`payloadHash([disc, reason_hash, block_height])`) does NOT satisfy the gate — UNSAT for a LEDGERLESS
client, NO off-cell anchor. This is the §6 lifecycle-payload residual (`RotatedKernelRefinementLifecycleDisc`)
CONVERTED: the forged payload that the bare record pin accepted (producer-free PI) is now REJECTED. -/
theorem rotateV3WithLifecyclePayloadGate_rejects_forged (sel : Nat) (beforeC? : Option ℤ) (afterC : ℤ)
    (hash : List ℤ → ℤ) (d : EffectVmDescriptor) (env : VmRowEnv) (isFirst isLast : Bool)
    (hlast : isLast = false)
    (hsel : env.loc sel = 1)
    (hforged : env.loc (afterLifecycleCol d.traceWidth) ≠ env.loc declaredLifecyclePayloadCol) :
    ¬ satisfiedVm hash (rotateV3WithLifecyclePayloadGate sel beforeC? afterC d) env isFirst isLast :=
  fun h => hforged
    (rotateV3WithLifecyclePayloadGate_forces sel beforeC? afterC hash d env isFirst isLast hlast hsel h)

/-- The AFTER-disc gate is STILL forced under the payload-gate layer (the payload weld is appended past
the disc gates, so the disc-gate membership survives) — the composed mover forces BOTH the disc (state)
AND the payload felt. -/
theorem rotateV3WithLifecyclePayloadGate_forces_disc (sel : Nat) (beforeC? : Option ℤ) (afterC : ℤ)
    (hash : List ℤ → ℤ) (d : EffectVmDescriptor) (env : VmRowEnv) (isFirst isLast : Bool)
    (hlast : isLast = false)
    (hsel : env.loc sel = 1)
    (h : satisfiedVm hash (rotateV3WithLifecyclePayloadGate sel beforeC? afterC d) env isFirst isLast) :
    env.loc (afterDiscCol d.traceWidth) = afterC := by
  have hmem : discForceGate sel (afterDiscCol d.traceWidth) afterC
      ∈ (rotateV3WithLifecyclePayloadGate sel beforeC? afterC d).constraints := by
    unfold rotateV3WithLifecyclePayloadGate
    have := rotateV3WithDiscGate_afterMem sel beforeC? afterC d
    simp only [List.mem_append]
    exact Or.inl this
  exact discForceGate_forces env isFirst isLast hlast sel (afterDiscCol d.traceWidth) afterC hsel
    (h.1 _ hmem)

#assert_axioms lifecyclePayloadHashGate_forces
#assert_axioms graduable_rotateV3WithLifecyclePayloadGate
#assert_axioms rotateV3WithLifecyclePayloadGate_forces
#assert_axioms rotateV3WithLifecyclePayloadGate_rejects_forged
#assert_axioms rotateV3WithLifecyclePayloadGate_forces_disc

/-! ## §5.MF — THE LIVE MODE / FIELDS-ROOT GATES (the makeSovereign / setFieldDyn / refusal movers
going LIVE — WAVE 3, the mover tail).

The mode/fields-root flag-day committed TWO dedicated authority sub-limbs BESIDE the opaque
`record_digest` (r23): the cell-MODE byte limb `B_MODE = 35` and the `fields_root` digest limb
`B_FIELDS_ROOT = 36`. With them in-circuit, the remaining mover-authority forgeries close LIVE:

  * **makeSovereign** — the deployed runtime row sets `new_state.mode_flag = 1` (a CONSTANT, no param).
    So the AFTER mode sub-limb is FORCED to `Sovereign(1)` as a CONSTANT, selector-gated on
    `SEL_MAKE_SOVEREIGN_RT` (the `discForceGate` shape — WAVE 1's constant force, NO trusted post-cell).
    A ledgerless client's `verify_vm_descriptor2` ALONE rejects a makeSovereign whose committed AFTER
    mode stays `Hosted(0)` (an un-promoted sovereign claim).

  * **setFieldDyn / refusal** — both move the cell's `fields_root` (setFieldDyn writes a dynamic ext
    field; refusal writes the `REFUSAL_AUDIT_EXT_KEY` audit slot — both land in `fields_root`, which
    `compute_authority_digest_felt` folds). The AFTER `fields_root` sub-limb is WELDED to the in-circuit
    declared post-`fields_root` param column (the perms/VK weld shape), so a forged post-`fields_root`
    (committed ≠ declared) is UNSAT. NAMED RESIDUAL (the WAVE-2 declared-param shape): the declared
    post-`fields_root` felt rides `prmCol 0`, which the deployed producer fills with `fields_root_felt`
    and the verifier ANCHORS to `hash_bytes(fields_root_of(post_cell))` (the SAME anchor mechanism the
    record-pin PI-38 already runs for this exact effect family, `proof_verify.rs` step 6b), now binding
    the SPECIFIC committed `fields_root` sub-limb in-circuit instead of the opaque r23 residue. -/

/-- The mode discriminants (the deployed `mode_flag`, `commitment.rs` `Hosted=0 / Sovereign=1`). -/
def modeHosted : ℤ := 0
def modeSovereign : ℤ := 1

/-- The AFTER-mode force column for a mover of width `w` (limb `B_MODE` of the AFTER block). -/
def afterModeCol (w : Nat) : Nat := w + AFTER_BLOCK_OFF + B_MODE
/-- The BEFORE-mode column (limb `B_MODE` of the BEFORE block). -/
def beforeModeCol (w : Nat) : Nat := w + B_MODE

/-- **`rotateV3WithModeGate sel afterC d`** — `rotateV3WithRecordPin B_RECORD_DIGEST d` PLUS the LIVE
mode gate: the AFTER mode limb is force-pinned to the CONSTANT `afterC` (`Sovereign(1)` for the
makeSovereign mover), selector-gated on `sel` (the `discForceGate` constant-force shape). Every v1
column/site/range and the record pin are UNTOUCHED — the gate is an appended CONSTRAINT, so `graduable`
and the keystones compose verbatim. -/
def rotateV3WithModeGate (sel : Nat) (afterC : ℤ) (d : EffectVmDescriptor) : EffectVmDescriptor :=
  let r := rotateV3WithRecordPin B_RECORD_DIGEST d
  { r with constraints := r.constraints ++ [discForceGate sel (afterModeCol d.traceWidth) afterC] }

theorem graduable_rotateV3WithModeGate (sel : Nat) (afterC : ℤ)
    {d : EffectVmDescriptor} (h : graduable d = true) :
    graduable (rotateV3WithModeGate sel afterC d) = true := by
  have hr := graduable_rotateV3WithRecordPin B_RECORD_DIGEST h
  unfold rotateV3WithModeGate
  unfold graduable at hr ⊢
  simpa using hr

/-- **The mode gate is the LAST appended constraint** — membership for the forcing extraction. -/
theorem rotateV3WithModeGate_mem (sel : Nat) (afterC : ℤ) (d : EffectVmDescriptor) :
    discForceGate sel (afterModeCol d.traceWidth) afterC
      ∈ (rotateV3WithModeGate sel afterC d).constraints := by
  unfold rotateV3WithModeGate
  simp [List.mem_append]

/-- **`rotateV3WithModeGate_forces_after` — the LIVE mode promotion is FORCED.** On an ACTIVE row
(`sel = 1`) of a satisfying `rotateV3WithModeGate` witness, the committed AFTER mode limb EQUALS the
mandated constant `afterC` (`Sovereign(1)`), with NO trusted post-cell. -/
theorem rotateV3WithModeGate_forces_after (sel : Nat) (afterC : ℤ)
    (hash : List ℤ → ℤ) (d : EffectVmDescriptor) (env : VmRowEnv) (isFirst isLast : Bool)
    (hlast : isLast = false)
    (hsel : env.loc sel = 1)
    (h : satisfiedVm hash (rotateV3WithModeGate sel afterC d) env isFirst isLast) :
    env.loc (afterModeCol d.traceWidth) = afterC :=
  discForceGate_forces env isFirst isLast hlast sel (afterModeCol d.traceWidth) afterC hsel
    (h.1 _ (rotateV3WithModeGate_mem sel afterC d))

/-- **TOOTH — `rotateV3WithModeGate_rejects_unpromoted`.** An ACTIVE row whose committed AFTER mode is
NOT the mandated `afterC` (a makeSovereign whose committed mode stays `Hosted(0)` — an un-promoted
sovereign) does NOT satisfy `rotateV3WithModeGate` — UNSAT for a ledgerless client, no anchor. -/
theorem rotateV3WithModeGate_rejects_unpromoted (sel : Nat) (afterC : ℤ)
    (hash : List ℤ → ℤ) (d : EffectVmDescriptor) (env : VmRowEnv) (isFirst isLast : Bool)
    (hlast : isLast = false)
    (hsel : env.loc sel = 1)
    (hwrong : env.loc (afterModeCol d.traceWidth) ≠ afterC) :
    ¬ satisfiedVm hash (rotateV3WithModeGate sel afterC d) env isFirst isLast :=
  fun h => hwrong (rotateV3WithModeGate_forces_after sel afterC hash d env isFirst isLast hlast hsel h)

#assert_axioms graduable_rotateV3WithModeGate
#assert_axioms rotateV3WithModeGate_forces_after
#assert_axioms rotateV3WithModeGate_rejects_unpromoted

/-- The AFTER fields-root force column for a mover of width `w` (limb `B_FIELDS_ROOT` of the AFTER
block). -/
def afterFieldsRootCol (w : Nat) : Nat := w + AFTER_BLOCK_OFF + B_FIELDS_ROOT
/-- The in-circuit declared-param column the live setFieldDyn / refusal row anchors the post
`fields_root_felt` into (`params[0]`, `prmCol 0`) — itself PI-anchored via the record-pin verifier
(`proof_verify.rs` step 6b: `hash_bytes(fields_root_of(post_cell))`). -/
def declaredFieldsRootCol : Nat := prmCol 0

/-- **`rotateV3WithFieldsRootGate sel afterCol d`** — `rotateV3WithRecordPin B_RECORD_DIGEST d` PLUS
the LIVE fields-root weld: the AFTER `fields_root` sub-limb `afterCol` is welded to the declared-param
column (`permsVKWeldGate` shape), selector-gated on `sel`. Every v1 column/site/range and the record
pin are UNTOUCHED — the gate is an appended CONSTRAINT, so `graduable` and the keystones compose
verbatim. -/
def rotateV3WithFieldsRootGate (sel afterCol : Nat) (d : EffectVmDescriptor) : EffectVmDescriptor :=
  let r := rotateV3WithRecordPin B_RECORD_DIGEST d
  { r with constraints := r.constraints ++ [permsVKWeldGate sel afterCol declaredFieldsRootCol] }

theorem graduable_rotateV3WithFieldsRootGate (sel afterCol : Nat)
    {d : EffectVmDescriptor} (h : graduable d = true) :
    graduable (rotateV3WithFieldsRootGate sel afterCol d) = true := by
  have hr := graduable_rotateV3WithRecordPin B_RECORD_DIGEST h
  unfold rotateV3WithFieldsRootGate
  unfold graduable at hr ⊢
  simpa using hr

/-- **The fields-root weld is the LAST appended constraint** — membership for the forcing extraction. -/
theorem rotateV3WithFieldsRootGate_mem (sel afterCol : Nat) (d : EffectVmDescriptor) :
    permsVKWeldGate sel afterCol declaredFieldsRootCol
      ∈ (rotateV3WithFieldsRootGate sel afterCol d).constraints := by
  unfold rotateV3WithFieldsRootGate
  simp [List.mem_append]

/-- **`rotateV3WithFieldsRootGate_forces` — the LIVE fields-root write is FORCED.** On an ACTIVE row
(`sel = 1`) of a satisfying `rotateV3WithFieldsRootGate` witness, the committed AFTER `fields_root`
sub-limb EQUALS the in-circuit declared-param column — NO trusted post-cell at the gate (the declared
column is verifier-anchored). -/
theorem rotateV3WithFieldsRootGate_forces (sel afterCol : Nat)
    (hash : List ℤ → ℤ) (d : EffectVmDescriptor) (env : VmRowEnv) (isFirst isLast : Bool)
    (hlast : isLast = false)
    (hsel : env.loc sel = 1)
    (h : satisfiedVm hash (rotateV3WithFieldsRootGate sel afterCol d) env isFirst isLast) :
    env.loc afterCol = env.loc declaredFieldsRootCol :=
  permsVKWeldGate_forces env isFirst isLast hlast sel afterCol declaredFieldsRootCol hsel
    (h.1 _ (rotateV3WithFieldsRootGate_mem sel afterCol d))

/-- **TOOTH — `rotateV3WithFieldsRootGate_rejects_forged`.** An ACTIVE row whose committed AFTER
`fields_root` sub-limb is NOT the declared param (a forged post-`fields_root` whose committed overflow
map diverges from the declared one) does NOT satisfy `rotateV3WithFieldsRootGate` — UNSAT for a
ledgerless client. -/
theorem rotateV3WithFieldsRootGate_rejects_forged (sel afterCol : Nat)
    (hash : List ℤ → ℤ) (d : EffectVmDescriptor) (env : VmRowEnv) (isFirst isLast : Bool)
    (hlast : isLast = false)
    (hsel : env.loc sel = 1)
    (hforged : env.loc afterCol ≠ env.loc declaredFieldsRootCol) :
    ¬ satisfiedVm hash (rotateV3WithFieldsRootGate sel afterCol d) env isFirst isLast :=
  fun h => hforged (rotateV3WithFieldsRootGate_forces sel afterCol hash d env isFirst isLast hlast hsel h)

#assert_axioms graduable_rotateV3WithFieldsRootGate
#assert_axioms rotateV3WithFieldsRootGate_forces
#assert_axioms rotateV3WithFieldsRootGate_rejects_forged

/-! ## §5.PC — THE VERIFIER-ANCHORED DECLARED-PAYLOAD COLUMN (the genuinely-new primitive: the
refusal / lifecycle-payload / effects_hash residuals going LIGHT-CLIENT-FORCED — VK-FREEDOM ERA).

The record pin (`rotateV3WithRecordPin off d`) welds the AFTER payload sub-limb (limb `off`:
`B_RECORD_DIGEST` for refusal's `fields_root` audit, `B_LIFECYCLE` for cellSeal/cellUnseal/cellDestroy/
receiptArchive) to a NEW rotated PI slot `(rotateV3 d).piCount` — call it the PAYLOAD slot. On the
FULL-NODE leg the verifier RECOMPUTES that PI from the trusted post-cell (`proof_verify.rs` step 6b:
`compute_authority_digest_felt(post)` / `lifecycle_felt_cell(post)`), so a forged payload is rejected.
But the LIGHT-CLIENT verifier (`verify_vm_descriptor2` over `sub_public_inputs`) takes the PI
PRODUCER-FREE: `generate_rotated_effect_vm_trace` fills it from the producer's own AFTER limb
(`trace_rotated.rs:394`), so the record pin holds VACUOUSLY for any self-consistent forged post-cell.
THAT is the residual the VK-epoch family-2 discriminator names.

The decisive structural difference from `permsVKWeldGate` (which IS light-client-forced): perms/VK weld
the AFTER sub-limb to `prmCol 0`, an IN-CIRCUIT declared-param column the v1 `effects_hash` pi-binds —
so the bound value is a LIGHT-CLIENT-KNOWN function of the effect, checked through the proof's own
carriers with NO verifier override. The refusal/lifecycle payload felt is a HASH FOLD (a Merkle insert /
a `reason_hash ⊕ sealed_at` fold), NOT carried by any single declared param, so no `permsVKWeldGate`
exists for it. The fix is a DECLARED-PAYLOAD COLUMN: the producer publishes the post-payload felt into a
dedicated declared column, the AFTER sub-limb is welded to it (so NEW_COMMIT binds the declared payload),
AND the declared column is PI-bound to the payload slot — but the slot is now VERIFIER-ANCHORED:

  * **effect-param-derivable** payloads (refusal `fields_root_felt`, the effects_hash topic/payload):
    the light client recomputes the payload from the published effect params it ALREADY knows via the
    PI-anchored `effects_hash` (PI[16..20], INSIDE the rotated dpis window) — the SAME chain perms/VK
    ride. The anchor is `payloadOf(effect) = hash_bytes(fields_root_of(apply effect to before))`.

  * **turn-context** payloads (cellSeal `sealed_at = block_height`): the light client recomputes
    `lifecycle_felt` from the effect's `reason_hash` AND the TURN-HEADER `block_height` it independently
    holds (the same height committed at `B_COMMITTED_HEIGHT`/PI 44, light-client-known). The anchor is
    `lifecycle_felt(reason_hash, committed_height)`.

The Lean side states the forcing RELATIVE to a verifier-supplied anchor `anchor : ℤ` (the value the
light-client verifier writes into the payload slot before `verify_vm_descriptor2`): a satisfying witness
FORCES `after_payload_limb = anchor`, so a forged `after_payload_limb ≠ anchor` is UNSAT — NO trusted
post-cell, NO producer-free PI. The genuinely-new content vs the record pin is the predicate
`PayloadAnchored` capturing "the verifier set the payload slot to the recomputed anchor" and the
two-pole theorems forcing the limb to the ANCHOR (not to the producer's published PI). The Rust verifier
wiring that supplies `anchor` on the LIGHT-CLIENT path is enumerated in
`vk_epoch_refusal_lifecycle_light_client_binding.rs` (the discriminator anchors the payload slot exactly
as the deployed light-client verifier must). -/

/-- **`payloadSlot d`** — the rotated PI slot the record pin welds the AFTER payload sub-limb to
(`(rotateV3 d).piCount`, the first past the four commit pins). The declared-payload column rides this
slot; the verifier ANCHORS it (vs the producer-free fill of the bare record pin). -/
def payloadSlot (d : EffectVmDescriptor) : Nat := (rotateV3 d).piCount

/-- **`PayloadAnchored env d anchor`** — the LIGHT-CLIENT verifier supplied the payload slot from a
RECOMPUTED anchor (effect-param-derivable: `hash_bytes(fields_root_of(apply effect))`; or turn-context:
`lifecycle_felt(reason_hash, committed_height)`), NOT producer-free. This is the deployed
`verify_vm_descriptor2(..., dpis)` precondition `dpis[payloadSlot] = anchor` — the seam the Rust
light-client verifier closes (see the discriminator). Stated as a HYPOTHESIS, never an axiom: the Lean
forcing is CONDITIONAL on the verifier honoring it, exactly as `permsVKWeldGate`'s soundness is
conditional on `effects_hash` anchoring `prmCol 0`. -/
def PayloadAnchored (env : VmRowEnv) (d : EffectVmDescriptor) (anchor : ℤ) : Prop :=
  env.pub (payloadSlot d) = anchor

/-- **`rotateV3WithPayloadColumn off d`** — DEFINITIONALLY `rotateV3WithRecordPin off d` (the record pin
IS the declared-payload weld `after_payload_limb == PI[payloadSlot]`). The new content is the
VERIFIER-ANCHORED reading of the payload slot: `rotateV3WithRecordPin` proved the limb equals the
PUBLISHED PI; this layer proves it equals the verifier-supplied ANCHOR (under `PayloadAnchored`), which
is the light-client force. Width / piCount / hashSites / ranges are `rotateV3WithRecordPin`'s verbatim. -/
def rotateV3WithPayloadColumn (off : Nat) (d : EffectVmDescriptor) : EffectVmDescriptor :=
  rotateV3WithRecordPin off d

theorem rotateV3WithPayloadColumn_eq (off : Nat) (d : EffectVmDescriptor) :
    rotateV3WithPayloadColumn off d = rotateV3WithRecordPin off d := rfl

/-- The payload column does NOT disturb graduation (it IS the record pin). -/
theorem graduable_rotateV3WithPayloadColumn (off : Nat) {d : EffectVmDescriptor}
    (h : graduable d = true) : graduable (rotateV3WithPayloadColumn off d) = true :=
  graduable_rotateV3WithRecordPin off h

/-- **`rotateV3WithPayloadColumn_forces_anchor` — the LIGHT-CLIENT close.** On a satisfying LAST row,
WHEN the verifier anchored the payload slot (`PayloadAnchored env d anchor`), the committed AFTER payload
sub-limb EQUALS the verifier-recomputed `anchor` — NO trusted post-cell at the gate, NO producer-free PI.
This is the deployed face: `verify_vm_descriptor2` with the verifier-anchored payload slot forces the
post-payload to the light-client-recomputed value. -/
theorem rotateV3WithPayloadColumn_forces_anchor (off : Nat) (hash : List ℤ → ℤ)
    (d : EffectVmDescriptor) (env : VmRowEnv) (isFirst : Bool) (anchor : ℤ)
    (hanchor : PayloadAnchored env d anchor)
    (h : satisfiedVm hash (rotateV3WithPayloadColumn off d) env isFirst true) :
    env.loc (d.traceWidth + AFTER_BLOCK_OFF + off) = anchor := by
  have hpin := rotateV3WithRecordPin_pins off hash d env isFirst h
  rw [hpin]
  exact hanchor

/-- **TOOTH — `rotateV3WithPayloadColumn_rejects_forged` (LIGHT-CLIENT).** A LAST row whose committed
AFTER payload sub-limb is NOT the verifier-recomputed `anchor` (a refusal forged to a different
`fields_root` audit; a cellSeal forged to a different `reason_hash`/`sealed_at`; an emitEvent forged to a
different topic/payload) does NOT satisfy `rotateV3WithPayloadColumn off d` once the verifier anchors the
slot — UNSAT for a LEDGERLESS client, no trusted post-cell. This is the residual CONVERTED: the forged
payload that the bare record pin accepted (producer-free PI) is now REJECTED (verifier-anchored PI). -/
theorem rotateV3WithPayloadColumn_rejects_forged (off : Nat) (hash : List ℤ → ℤ)
    (d : EffectVmDescriptor) (env : VmRowEnv) (isFirst : Bool) (anchor : ℤ)
    (hanchor : PayloadAnchored env d anchor)
    (hforged : env.loc (d.traceWidth + AFTER_BLOCK_OFF + off) ≠ anchor) :
    ¬ satisfiedVm hash (rotateV3WithPayloadColumn off d) env isFirst true :=
  fun h => hforged (rotateV3WithPayloadColumn_forces_anchor off hash d env isFirst anchor hanchor h)

/-- The v1 denotation survives the payload column (it IS the record pin). -/
theorem rotateV3WithPayloadColumn_satisfiedVm_v1 (off : Nat) (hash : List ℤ → ℤ)
    (d : EffectVmDescriptor) (env : VmRowEnv) (isFirst isLast : Bool)
    (h : satisfiedVm hash (rotateV3WithPayloadColumn off d) env isFirst isLast) :
    satisfiedVm hash d env isFirst isLast :=
  rotateV3WithRecordPin_satisfiedVm_v1 off hash d env isFirst isLast h

#assert_axioms graduable_rotateV3WithPayloadColumn
#assert_axioms rotateV3WithPayloadColumn_forces_anchor
#assert_axioms rotateV3WithPayloadColumn_rejects_forged
#assert_axioms rotateV3WithPayloadColumn_satisfiedVm_v1

/-- **`refusalPayloadV3`** — the LIVE rotated refusal WITH the verifier-anchored declared-payload column
on the `fields_root` audit limb (`B_RECORD_DIGEST = 24`). The deployed `apply_refusal` writes the audit
commitment into the `REFUSAL_AUDIT_EXT_KEY` slot of `fields_root`, which `compute_authority_digest_felt`
folds into r23 — so a genuine refusal MOVES limb 24. The payload column welds that limb to the payload
slot; the light-client verifier ANCHORS the slot to `compute_authority_digest_felt(apply refusal to
before)`, a value it recomputes from the EFFECT (the `offered_action_commitment` + `reason` carried in
the published refusal params, bound via `effects_hash`). A refusal forged to a DIFFERENT audit payload
(committed r23 ≠ the anchored digest) is now UNSAT for a ledgerless client
(`rotateV3WithPayloadColumn_rejects_forged`) — the family-2 residual CLOSED, light-client-forced. -/
def refusalPayloadV3 : EffectVmDescriptor2 :=
  graduateV1 (rotateV3WithPayloadColumn B_RECORD_DIGEST EffectVmEmitRefusal.refusalVmDescriptor)

/-- **`cellSealV3` carries the lifecycle payload column** — `rotateV3WithDiscGate` is built on
`rotateV3WithRecordPin B_LIFECYCLE`, so the lifecycle payload limb (`B_LIFECYCLE = 29`) is ALREADY welded
to the payload slot. The light-client force is the verifier ANCHOR of that slot to
`lifecycle_felt(reason_hash, committed_height)` (the effect's `reason_hash` param + the turn-header
height the light client holds). This theorem exposes the payload-column forcing for cellSeal as the
specialization of the general primitive — a forged sealing payload (committed limb 29 ≠ the anchored
lifecycle felt) is UNSAT once the verifier anchors the slot. -/
theorem cellSealV3_payload_rejects_forged (hash : List ℤ → ℤ) (env : VmRowEnv) (isFirst : Bool)
    (anchor : ℤ)
    (hanchor : PayloadAnchored env EffectVmEmitCellSeal.cellSealVmDescriptor anchor)
    (hforged : env.loc (EffectVmEmitCellSeal.cellSealVmDescriptor.traceWidth + AFTER_BLOCK_OFF + B_LIFECYCLE)
      ≠ anchor) :
    ¬ satisfiedVm hash (rotateV3WithPayloadColumn B_LIFECYCLE EffectVmEmitCellSeal.cellSealVmDescriptor)
      env isFirst true :=
  rotateV3WithPayloadColumn_rejects_forged B_LIFECYCLE hash _ env isFirst anchor hanchor hforged

#assert_axioms cellSealV3_payload_rejects_forged

/-! ### §5.PC.EH — THE effects_hash SUB-CASE (emitEvent / pipelinedSend / exercise) — ALREADY
LIGHT-CLIENT-BOUND, NO declared-payload column needed.

The third family the VK-epoch swept (`emitEvent` / `pipelinedSend` / `exercise`) declares a HASH
(topic/payload for emitEvent; send_hash for pipelinedSend; exercise_hash for exercise) — NOT a post-cell
STATE payload. These effects are STATELESS / FREEZE-ALL (`emitEvent` rides `v3OfFrozen =
rotateV3FrozenAuthority`: every authority limb r23/lifecycle/perms/vk/mode/fields-root is FROZEN to the
BEFORE, the topic/payload digests ride the row's params OFF-trace, `EffectVmEmitEmitEvent` §intro). So
there is NO AFTER payload SUB-LIMB to forge — the declared hash IS the `effects_hash` the row folds via
`compute_effects_hash`.

And `effects_hash` is ALREADY light-client-bound IN-WINDOW: it lands at PI slots `[16..20)`
(`pi.rs::EFFECTS_HASH_BASE = NEW_COMMIT_BASE(8) + NEW_COMMIT_LEN(8) = 16`), which is INSIDE the rotated PI
window (`V1_PI_COUNT = 42`, so `pis[..42]` carries it into the rotated dpis). The v1 descriptor pi-binds
that slot to the row's `compute_effects_hash` of the declared params — the SAME perms/VK chain
(`prmCol i → effects_hash → PI`) that makes setPerms/setVK light-client-forced. So `verify_vm_descriptor2`
ALONE already checks the declared hash against a producer-non-free PI: a forged topic/payload/send/exercise
hash that disagrees with the bound `effects_hash` is UNSAT on the light-client path.

THE PRECISE RESIDUE (named, not laundered): the RAW per-effect emit topic/payload slots (`pi.rs` index
174+) ride PAST the rotated window and bind only at the full-node v1 hand-AIR — but those are the
PRE-fold OPERANDS, redundant with the in-window folded `effects_hash` PI[16..20] that the rotated path
DOES carry and DOES bind. The light-client-forced quantity for these three is the declared HASH (the
folded `effects_hash`), which is in-window. No declared-payload column is required: the effects_hash
sub-case is light-client-forced by the EXISTING in-window `effects_hash` pin (the perms/VK-shaped
chain), not by a new primitive. (`vk_epoch_misc_light_client_binding.rs` carries the emitEvent
discriminator.) -/

/-- **`cellSealV3`** — the LIVE rotated cellSeal WITH the lifecycle-forcing pin AND the LIVE disc gate:
the BEFORE disc limb is force-pinned to `Live(0)` and the AFTER disc limb to `Sealed(1)` (selector
`SEL_CELLSEAL`). A frozen-lifecycle (un-sealed, after-disc stays Live) AFTER block is now UNSAT via the
in-circuit disc gate ALONE — no trusted post-cell (`rotateV3WithDiscGate_rejects_wrong_after`), the LIVE
realization of `RotatedKernelRefinementLifecycleDisc.cellSeal_disc_rejects_frozen`. AND (STAGE C, §5.LP)
the OPAQUE payload felt at `B_LIFECYCLE` is now LIGHT-CLIENT-FORCED: the AFTER lifecycle limb is welded to
the in-circuit declared payload-hash column (`payloadHash([disc, reason_hash, sealed_at])`), so a cellSeal
forged to a different `reason_hash` / `sealed_at` is UNSAT ledgerless
(`rotateV3WithLifecyclePayloadGate_rejects_forged`). The record pin on `B_LIFECYCLE` (PI 46) stays as
belt-and-suspenders. -/
def cellSealV3 : EffectVmDescriptor2 :=
  graduateV1 (rotateV3WithLifecyclePayloadGate EffectVmEmitCellSeal.SEL_CELLSEAL (some discLive) discSealed
    EffectVmEmitCellSeal.cellSealVmDescriptor)

/-- **`cellUnsealV3`** — the LIVE rotated cellUnseal WITH the lifecycle-forcing pin AND the LIVE disc
gate: BEFORE disc = `Sealed(1)`, AFTER disc = `Live(0)` (selector `SEL_CELLUNSEAL`). An un-revived unseal
(after-disc stays Sealed) is UNSAT (`RotatedKernelRefinementLifecycleDisc.cellUnseal_disc_rejects_unrevived`). -/
def cellUnsealV3 : EffectVmDescriptor2 :=
  graduateV1 (rotateV3WithDiscGate EffectVmEmitCellUnseal.SEL_CELLUNSEAL (some discSealed) discLive
    EffectVmEmitCellUnseal.cellUnsealVmDescriptor)

/-- **`cellDestroyV3`** — the LIVE rotated cellDestroy WITH the lifecycle-forcing pin AND the LIVE disc
gate: AFTER disc = `Destroyed(3)` (selector `SEL_CELLDESTROY`; NO before-pin — destroy is admissible from
any non-Destroyed disc, and the no-resurrection tooth is the AFTER force). A Destroyed→Live resurrection
forgery (after-disc published as Live) is UNSAT via the disc gate ALONE
(`RotatedKernelRefinementLifecycleDisc.cellDestroy_disc_rejects_resurrection`). AND (STAGE C, §5.LP) the
death-cert payload folded into `lifecycle_felt` is now LIGHT-CLIENT-FORCED via the in-circuit payload-hash
weld: a cellDestroy forged to a different `death_certificate_hash` / `destroyed_at` is UNSAT ledgerless
(`rotateV3WithLifecyclePayloadGate_rejects_forged`). -/
def cellDestroyV3 : EffectVmDescriptor2 :=
  graduateV1 (rotateV3WithLifecyclePayloadGate EffectVmEmitCellDestroy.SEL_CELLDESTROY none discDestroyed
    EffectVmEmitCellDestroy.cellDestroyVmDescriptor)

/-- **H1 MOVER WELD — `withRecordPin8Headroom2` (post-graduation).** A record-digest mover's EXISTING
limb-0 record pin (`B_RECORD_DIGEST` → PI 46) forces ONLY limb-0; this appends 7 last-row PI pins binding
the 7 HEADROOM authority limbs (AFTER-block offsets 12..=18 = limb-1..7 of the faithful 8-felt
`compute_authority_digest_8`) to the next 7 PIs (47..53), bumping `piCount 47→54`. The deployed verifier
anchors `PI[46..53] = compute_authority_digest_8(post_cell)[0..7]` (step-6b, the 8-felt generalization of
the single-felt anchor), so a mover that forges a 31-bit-colliding wide-open authority into ANY of the 8
limbs is UNSAT — the GENTIAN fail-open ("a wider-but-unwelded limb") is CLOSED for movers, just as the
value cohort's continuity freeze closed it for value turns. Additive (mirrors the `refusalFieldsWriteV3`
/ Custom-exposure post-graduation append): every existing column/site/range and constraint is untouched,
so the per-mover forcing keystones compose verbatim (the limb-0 pin + the gate weld stay members). -/
def withRecordPin8Headroom2 (g : EffectVmDescriptor2) : EffectVmDescriptor2 :=
  { g with
    piCount := g.piCount + 7
    constraints := g.constraints ++ (List.range 7).map (fun i =>
      VmConstraint2.base (.piBinding .last (EFFECT_VM_WIDTH + AFTER_BLOCK_OFF + (12 + i)) (g.piCount + i))) }

/-- The 7 H1 headroom pins are the ONLY constraints past the inner descriptor's; the inner descriptor's
constraints stay the left operand of the single `++` (so every per-mover membership / forcing lemma lifts
verbatim — `List.mem_append_left`). -/
theorem withRecordPin8Headroom2_constraints (g : EffectVmDescriptor2) :
    (withRecordPin8Headroom2 g).constraints
      = g.constraints ++ (List.range 7).map (fun i =>
          VmConstraint2.base (.piBinding .last (EFFECT_VM_WIDTH + AFTER_BLOCK_OFF + (12 + i)) (g.piCount + i))) :=
  rfl

/-- The 7 H1 headroom pins are `.piBinding`s, so they contribute NO mem-op (the mem log is unchanged). -/
theorem memOpsOf_withRecordPin8Headroom2 (g : EffectVmDescriptor2) :
    memOpsOf (withRecordPin8Headroom2 g) = memOpsOf g := by
  simp [memOpsOf, withRecordPin8Headroom2, List.filterMap_append, List.filterMap_map]

/-- The 7 H1 headroom pins contribute NO map-op (the map log is unchanged). -/
theorem mapOpsOf_withRecordPin8Headroom2 (g : EffectVmDescriptor2) :
    mapOpsOf (withRecordPin8Headroom2 g) = mapOpsOf g := by
  simp [mapOpsOf, withRecordPin8Headroom2, List.filterMap_append, List.filterMap_map]

/-- **THE PEEL — `Satisfied2 (withRecordPin8Headroom2 g) ⟹ Satisfied2 g`.** The H1 mover wrap only
APPENDS `.piBinding` constraints (and bumps `piCount`): the inner descriptor's constraints stay members
(`List.mem_append_left`), the hash sites / ranges are unchanged, and the mem/map logs are unchanged (the
pins are not mem/map ops). So every existing per-mover soundness lemma (which consumes `Satisfied2` of the
graduated GATE) lifts to the wrapped deployed descriptor by peeling the wrap first. -/
theorem satisfied2_of_withRecordPin8Headroom2 (hash : List ℤ → ℤ) (g : EffectVmDescriptor2)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (h : Satisfied2 hash (withRecordPin8Headroom2 g) minit mfin maddrs t) :
    Satisfied2 hash g minit mfin maddrs t := by
  have hmem : memLog (withRecordPin8Headroom2 g) t = memLog g t := by
    simp [memLog, memOpsOf_withRecordPin8Headroom2]
  have hmap : mapLog (withRecordPin8Headroom2 g) t = mapLog g t := by
    simp [mapLog, mapOpsOf_withRecordPin8Headroom2]
  exact
    { rowConstraints := fun i hi c hc => h.rowConstraints i hi c (by
        rw [withRecordPin8Headroom2_constraints]; exact List.mem_append_left _ hc)
    , rowHashes := h.rowHashes
    , rowRanges := h.rowRanges
    , memAddrsNodup := h.memAddrsNodup
    , memClosed := fun op hop => h.memClosed op (by rw [hmem]; exact hop)
    , memDisciplined := by rw [← hmem]; exact h.memDisciplined
    , memBalanced := by rw [← hmem]; exact h.memBalanced
    , memTableFaithful := by rw [← hmem]; exact h.memTableFaithful
    , mapTableFaithful := by rw [← hmap]; exact h.mapTableFaithful }

/-- **v10 PERMS/VK FAITHFUL-8-FELT WELD — `withPermsVK8Weld` (post-graduation).** The limb-0 perms/vk
weld (`rotateV3WithPermsVKGate`) forces ONLY `B_PERMS`/`B_VK` (limb-0 of the deployed `hash_to_8`
`permissions_hash`/`vk_hash`) to `prmCol 0`. This appends the SEVEN completion-felt welds: the AFTER-block
faithful-8-felt extras (`extra0 .. extra0+6`, the new pre-iroot limbs 37..=43 for perms / 44..=50 for vk,
carrying `permsHash[1..7]` / `vkHash[1..7]`) are EACH welded to `prmCol 1..7` — the remaining 7 felts of
the deployed 8-felt declared param, ALL already PI-anchored through the SAME `effects_hash` chain (so
`piCount` is UNCHANGED — NO new verifier PI, which is why perms/vk are the TRACTABLE pair). With the
limb-0 weld this forces the FULL 8-felt faithful digest, so a mover that forges a ~31-bit-colliding
wide-open authority into ANY of the 8 perms/vk limbs is UNSAT — the GENTIAN fail-open ("a wider-but-
unwelded limb") is CLOSED for the perms/vk movers. Additive (mirrors `withRecordPin8Headroom2`): every
existing column/site/range/constraint is untouched, so the per-mover keystones compose verbatim
(`List.mem_append_left`). -/
def withPermsVK8Weld (sel extra0 : Nat) (g : EffectVmDescriptor2) : EffectVmDescriptor2 :=
  { g with
    constraints := g.constraints ++ (List.range 7).map (fun i =>
      VmConstraint2.base (permsVKWeldGate sel (extra0 + i) (prmCol (i + 1)))) }

/-- The 7 completion-felt welds are the ONLY constraints past the inner descriptor's — the inner stays
the left operand of the single `++` (every per-mover membership / forcing lemma lifts verbatim). -/
theorem withPermsVK8Weld_constraints (sel extra0 : Nat) (g : EffectVmDescriptor2) :
    (withPermsVK8Weld sel extra0 g).constraints
      = g.constraints ++ (List.range 7).map (fun i =>
          VmConstraint2.base (permsVKWeldGate sel (extra0 + i) (prmCol (i + 1)))) :=
  rfl

/-- The 7 completion-felt welds are `.gate`s, so they contribute NO mem-op (the mem log is unchanged). -/
theorem memOpsOf_withPermsVK8Weld (sel extra0 : Nat) (g : EffectVmDescriptor2) :
    memOpsOf (withPermsVK8Weld sel extra0 g) = memOpsOf g := by
  simp [memOpsOf, withPermsVK8Weld, List.filterMap_append, List.filterMap_map]

/-- The 7 completion-felt welds contribute NO map-op (the map log is unchanged). -/
theorem mapOpsOf_withPermsVK8Weld (sel extra0 : Nat) (g : EffectVmDescriptor2) :
    mapOpsOf (withPermsVK8Weld sel extra0 g) = mapOpsOf g := by
  simp [mapOpsOf, withPermsVK8Weld, List.filterMap_append, List.filterMap_map]

/-- **THE PEEL — `Satisfied2 (withPermsVK8Weld sel extra0 g) ⟹ Satisfied2 g`.** The v10 weld only
APPENDS `.gate` constraints: the inner constraints stay members (`List.mem_append_left`), hash sites /
ranges and the mem/map logs are unchanged. So every existing per-mover soundness lemma (consuming
`Satisfied2` of the inner descriptor) lifts to the deployed descriptor by peeling this wrap first. -/
theorem satisfied2_of_withPermsVK8Weld (hash : List ℤ → ℤ) (g : EffectVmDescriptor2)
    {sel extra0 : Nat} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (h : Satisfied2 hash (withPermsVK8Weld sel extra0 g) minit mfin maddrs t) :
    Satisfied2 hash g minit mfin maddrs t := by
  have hmem : memLog (withPermsVK8Weld sel extra0 g) t = memLog g t := by
    simp [memLog, memOpsOf_withPermsVK8Weld]
  have hmap : mapLog (withPermsVK8Weld sel extra0 g) t = mapLog g t := by
    simp [mapLog, mapOpsOf_withPermsVK8Weld]
  exact
    { rowConstraints := fun i hi c hc => h.rowConstraints i hi c (by
        rw [withPermsVK8Weld_constraints]; exact List.mem_append_left _ hc)
    , rowHashes := h.rowHashes
    , rowRanges := h.rowRanges
    , memAddrsNodup := h.memAddrsNodup
    , memClosed := fun op hop => h.memClosed op (by rw [hmem]; exact hop)
    , memDisciplined := by rw [← hmem]; exact h.memDisciplined
    , memBalanced := by rw [← hmem]; exact h.memBalanced
    , memTableFaithful := by rw [← hmem]; exact h.memTableFaithful
    , mapTableFaithful := by rw [← hmap]; exact h.mapTableFaithful }

/-- **`withPermsVK8Weld_forces` — the SEVEN completion-felt welds BITE.** On a TRANSITION row
(`row + 1 ≠ t.rows.length`) of a `Satisfied2 hash (withPermsVK8Weld sel extra0 g)` witness whose `sel` is
hot, EACH AFTER completion-felt limb `extra0 + i` (`i < 7`) EQUALS `prmCol (i + 1)`. Combined with the
limb-0 weld (the inner `rotateV3WithPermsVKGate`) this forces all 8 felts of the faithful digest. -/
theorem withPermsVK8Weld_forces (hash : List ℤ → ℤ) (sel extra0 : Nat) (g : EffectVmDescriptor2)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (h : Satisfied2 hash (withPermsVK8Weld sel extra0 g) minit mfin maddrs t)
    (row : Nat) (hrow : row < t.rows.length) (hnotlast : row + 1 ≠ t.rows.length)
    (hsel : (envAt t row).loc sel = 1)
    (i : Nat) (hi : i < 7) :
    (envAt t row).loc (extra0 + i) = (envAt t row).loc (prmCol (i + 1)) := by
  have hmemc : VmConstraint2.base (permsVKWeldGate sel (extra0 + i) (prmCol (i + 1)))
      ∈ (withPermsVK8Weld sel extra0 g).constraints := by
    rw [withPermsVK8Weld_constraints]
    exact List.mem_append_right _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)
  have hgate : (permsVKWeldGate sel (extra0 + i) (prmCol (i + 1))).holdsVm
      (envAt t row) (row == 0) (row + 1 == t.rows.length) :=
    h.rowConstraints row hrow _ hmemc
  have hlastf : (row + 1 == t.rows.length) = false := by
    simp only [beq_eq_false_iff_ne]; exact hnotlast
  rw [hlastf] at hgate
  exact permsVKWeldGate_forces (envAt t row) (row == 0) false rfl _ _ _ hsel hgate

/-- **TOOTH — `withPermsVK8Weld_rejects_forged`.** A TRANSITION row whose committed AFTER completion-felt
limb `extra0 + i` is NOT the declared `prmCol (i + 1)` (a forge whose faithful 8-felt diverges from the
PI-anchored declared one in ANY of the 7 completion felts) does NOT satisfy the weld — UNSAT for a
ledgerless client, no trusted post-cell. -/
theorem withPermsVK8Weld_rejects_forged (hash : List ℤ → ℤ) (sel extra0 : Nat) (g : EffectVmDescriptor2)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (row : Nat) (hrow : row < t.rows.length) (hnotlast : row + 1 ≠ t.rows.length)
    (hsel : (envAt t row).loc sel = 1)
    (i : Nat) (hi : i < 7)
    (hforged : (envAt t row).loc (extra0 + i) ≠ (envAt t row).loc (prmCol (i + 1))) :
    ¬ Satisfied2 hash (withPermsVK8Weld sel extra0 g) minit mfin maddrs t :=
  fun h => hforged (withPermsVK8Weld_forces hash sel extra0 g h row hrow hnotlast hsel i hi)

#assert_axioms withPermsVK8Weld_forces
#assert_axioms satisfied2_of_withPermsVK8Weld
#assert_axioms withPermsVK8Weld_rejects_forged

/-- **`setPermsV3`** — the LIVE rotated setPermissions WITH the record-digest-forcing pin AND the LIVE
perms gate (WAVE 2): the AFTER block's committed PERMS-DIGEST sub-limb (`B_PERMS = 33`) is welded to the
in-circuit declared-param column `prmCol 0` (= `permsHash[0]`, anchored to a light-client PI via
`effects_hash`), selector-gated on `SEL_SET_PERMS`. A forged post-permissions (committed perms-digest ≠
declared param) is now UNSAT via the in-circuit weld ALONE — no trusted post-cell
(`rotateV3WithPermsVKGate_rejects_forged`), the LIVE realization of
`RotatedKernelRefinementPermsVK.setPermissions_slot_forced`. The record pin on `B_RECORD_DIGEST` (PI 46)
stays as belt-and-suspenders for the opaque full authority residue. -/
def setPermsV3 : EffectVmDescriptor2 :=
  withPermsVK8Weld EffectVmEmitSetPermissions.SEL_SET_PERMS
    (afterPermsExtraCol EffectVmEmitSetPermissions.setPermsVmDescriptor.traceWidth)
    (withRecordPin8Headroom2 (graduateV1 (rotateV3WithPermsVKGate EffectVmEmitSetPermissions.SEL_SET_PERMS
      (afterPermsCol EffectVmEmitSetPermissions.setPermsVmDescriptor.traceWidth)
      EffectVmEmitSetPermissions.setPermsVmDescriptor)))

/-- **`setVKV3`** — the LIVE rotated setVK WITH the record-digest-forcing pin AND the LIVE vk gate
(WAVE 2): the AFTER block's committed VK-DIGEST sub-limb (`B_VK = 34`) is welded to the in-circuit
declared-param column `prmCol 0` (= `vkHash[0]`, PI-anchored via `effects_hash`), selector-gated on
`SEL_SET_VK`. A forged post-VK (the upgrade-safety forgery — committed vk-digest ≠ declared param) is
UNSAT via the in-circuit weld ALONE, no trusted post-cell — the LIVE realization of
`RotatedKernelRefinementPermsVK.setVK_slot_forced`. -/
def setVKV3 : EffectVmDescriptor2 :=
  withPermsVK8Weld EffectVmEmitSetVK.SEL_SET_VK
    (afterVKExtraCol EffectVmEmitSetVK.setVKVmDescriptor.traceWidth)
    (withRecordPin8Headroom2 (graduateV1 (rotateV3WithPermsVKGate EffectVmEmitSetVK.SEL_SET_VK
      (afterVKCol EffectVmEmitSetVK.setVKVmDescriptor.traceWidth)
      EffectVmEmitSetVK.setVKVmDescriptor)))

/-- **FORCE-LEMMA #1 (perms) — `setPermsV3_forces8_extras`.** On an ACTIVE TRANSITION setPermissions row
of a `Satisfied2 hash setPermsV3` witness, EACH of the 7 committed AFTER perms COMPLETION limbs
(`afterPermsExtraCol … + i` = limb 37..=43, the faithful `permsHash[1..7]`) EQUALS its declared param
`prmCol (i + 1)`. With the limb-0 weld (`setPermissions_forced_sat`) this is the full 8-felt close: a
forge with the wrong faithful 8-felt is UNSAT. -/
theorem setPermsV3_forces8_extras (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (h : Satisfied2 hash setPermsV3 minit mfin maddrs t)
    (row : Nat) (hrow : row < t.rows.length) (hnotlast : row + 1 ≠ t.rows.length)
    (hsel : (envAt t row).loc EffectVmEmitSetPermissions.SEL_SET_PERMS = 1)
    (i : Nat) (hi : i < 7) :
    (envAt t row).loc
        (afterPermsExtraCol EffectVmEmitSetPermissions.setPermsVmDescriptor.traceWidth + i)
      = (envAt t row).loc (prmCol (i + 1)) :=
  withPermsVK8Weld_forces hash _ _ _ h row hrow hnotlast hsel i hi

/-- **FORCE-LEMMA #2 (vk) — `setVKV3_forces8_extras`.** On an ACTIVE TRANSITION setVK row of a
`Satisfied2 hash setVKV3` witness, EACH of the 7 committed AFTER vk COMPLETION limbs
(`afterVKExtraCol … + i` = limb 44..=50, the faithful `vkHash[1..7]`) EQUALS its declared param
`prmCol (i + 1)` — the full 8-felt close for setVK. -/
theorem setVKV3_forces8_extras (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (h : Satisfied2 hash setVKV3 minit mfin maddrs t)
    (row : Nat) (hrow : row < t.rows.length) (hnotlast : row + 1 ≠ t.rows.length)
    (hsel : (envAt t row).loc EffectVmEmitSetVK.SEL_SET_VK = 1)
    (i : Nat) (hi : i < 7) :
    (envAt t row).loc (afterVKExtraCol EffectVmEmitSetVK.setVKVmDescriptor.traceWidth + i)
      = (envAt t row).loc (prmCol (i + 1)) :=
  withPermsVK8Weld_forces hash _ _ _ h row hrow hnotlast hsel i hi

#assert_axioms setPermsV3_forces8_extras
#assert_axioms setVKV3_forces8_extras

/-- **`refusalV3`** — the LIVE rotated refusal WITH the record-digest-forcing pin. The `.refusalA`
arm sets the cell record's `"refusal"` audit slot to `1` (`TurnExecutorFull.refusalField`,
`Spec.CellStateAudit.RefusalSpec`). That named record slot lands in the deployed cell's `fields_root`
(the named-field map — NOT one of the welded `fields[0..7]` indexed slots), which
`compute_authority_digest_felt` FOLDS into the r23 authority residue (`B_RECORD_DIGEST = 24`). So a
genuine refusal MOVES the AFTER `record_digest` limb. The record pin (`rotateV3WithRecordPin
B_RECORD_DIGEST`) welds that limb to PI 46; the verifier anchors PI 46 to
`compute_authority_digest_felt(post_cell)` (`cipherclerk`/`full_turn_proof`), so a frozen-audit-slot
refusal forgery (the AFTER `record_digest` unchanged from the PRE) FAILS the pin and is UNSAT for a
ledgerless client — the field-NOT-bound deployment gap is closed via the verifier-anchored pin.

The deployed refusal row's declared params are `param0 = REFUSAL_TARGET`, `param1 =
REFUSAL_REASON_HASH` (`effect_vm/trace.rs`, `columns::param`); NEITHER carries the post-`fields_root`
digest, so the `fields_root`-sub-limb (`B_FIELDS_ROOT = 36`) has NO in-circuit declared-param weld for
refusal — the record-digest pin on `B_RECORD_DIGEST` is the single in-circuit close, and it folds the
`fields_root` audit write through the r23 residue. (Contrast `setPermsV3`/`setVKV3`, whose deployed
`param0` IS the declared perms/vk hash, so their `permsVKWeldGate` weld on `param0` is genuine.) -/
def refusalV3 : EffectVmDescriptor2 :=
  graduateV1 (rotateV3WithRecordPin B_RECORD_DIGEST EffectVmEmitRefusal.refusalVmDescriptor)

/-- **`refusalPayloadV3` IS `refusalV3`** — the verifier-anchored declared-payload column is the record
pin (`rotateV3WithPayloadColumn = rotateV3WithRecordPin` definitionally), so the LIVE deployed refusal
descriptor ALREADY carries the payload weld; the light-client force is the verifier ANCHOR of PI 46, NOT
a new constraint (same width / piCount / wire JSON — NO VK change). -/
theorem refusalPayloadV3_eq_refusalV3 : refusalPayloadV3 = refusalV3 := rfl

#assert_axioms refusalPayloadV3_eq_refusalV3

/-! ## §5.RF — the refusal FIELDS-ROOT MAP-OP WRITE GATE (the deployment-real audit-slot WRITE,
mirroring the noteSpend nullifier-tree grow-gate exactly — `.write` not `.insert`).

`refusalV3` closes the refusal forgery on the FULL-NODE leg (the record-digest PI 46 anchor folds the
`fields_root` audit write through the r23 residue, verifier-recomputed from the trusted post-cell). But
on the LIGHT-CLIENT leg the verifier takes PI 46 PRODUCER-FREE, so a forged post-`fields_root` (one whose
audit slot was NOT written) holds the record pin vacuously — the SAME light-client gap §5.N closed for
noteSpend's limb 26 by repointing it from a turn-invariant witness limb into a FORCED map-op write.

This `MapOp` CLOSES the refusal `fields_root` (limb `B_FIELDS_ROOT = 36`) on the live wire, CLONING the
noteSpend grow-gate onto limb 36 but with `op := .write` (a sorted insert-or-update at an EXISTING,
RESERVED key — the `"refusal"` audit slot is a position-stable reserved key in the named-field map, so a
refusal is a value WRITE, not a fresh insert):

  * **`refusalFieldsWriteOp`** (`.write`) — the AUDIT-SLOT WRITE: the AFTER `fields_root` (limb 36 of the
    after block) IS the genuine sorted write of `(refusalAuditKeyFelt → auditFelt)` into the BEFORE
    `fields_root`. Under CR (`writesTo_functional`) the after-root column cannot be frozen or forged — a
    frozen-audit-slot refusal (AFTER `fields_root` == PRE, the slot un-written) has NO `writesTo` witness
    that produces an UNCHANGED root for a non-trivial write, so the light-client descriptor is UNSAT.

Gated by the refusal selector (`SEL_REFUSAL = 52`), so non-refusal / NoOp pad rows contribute nothing. -/

/-- The rotated BEFORE-block `fields_root` limb column (limb `B_FIELDS_ROOT = 36` of the before block at
`base = traceWidth`). The deployed named-field map's PRE root — the openable sorted-Poseidon2 root the
write-gate opens against. (The AFTER analog `afterFieldsRootCol` is defined in §5.MF.) -/
def beforeFieldsRootCol (w : Nat) : Nat := w + B_FIELDS_ROOT

/-- **`refusalAuditKeyFelt`** — the sort-key felt of the `"refusal"` audit slot in the named-field map.
OPAQUE in Lean: its concrete value is the Rust `field_key_hash(REFUSAL_AUDIT_EXT_KEY)` (with
`REFUSAL_AUDIT_EXT_KEY = 2^32`), PINNED by the trace differential, NOT recomputed here. The light-client
recomputes the SAME constant from the protocol's fixed audit-key schema, so the key is a CONSTANT column,
not a producer-supplied one. -/
def refusalAuditKeyFelt : ℤ := 529176517  -- = Rust `field_key_hash(REFUSAL_AUDIT_EXT_KEY)`; differential-pinned (`fields_root_key_felt_matches_lean`).

/-- The in-circuit declared-param column carrying the refusal AUDIT FELT (the leaf value the audit slot
is written to — light-client-recomputable from the refusal params `offered_action_commitment` + `reason`).
The deployed refusal row uses ONLY `param0 = REFUSAL_TARGET` and `param1 = REFUSAL_REASON_HASH`; `param2`
(`prmCol 2 = 70`) is a SPARE param slot. The rotated trace generator must fill `row[PARAM_BASE + 2]` with
`auditFelt(params)` for the refusal row — that is the value the map-op write inserts. -/
def REFUSAL_AUDIT_FELT_COL : Nat := prmCol 2

/-- **`refusalFieldsWriteOp`** — the AUDIT-SLOT WRITE map-op (mirrors `nullifierInsertOp` but `.write`,
since the audit slot is a RESERVED, present key — an update, not a fresh insert). The AFTER `fields_root`
(limb 36 of the after block) IS the genuine sorted write of `(refusalAuditKeyFelt → REFUSAL_AUDIT_FELT_COL)`
into the BEFORE `fields_root`. -/
def refusalFieldsWriteOp : MapOp :=
  { guard   := .var EffectVmEmitRefusal.SEL_REFUSAL
  , root    := .var (beforeFieldsRootCol EFFECT_VM_WIDTH)
  , key     := .const refusalAuditKeyFelt
  , value   := .var REFUSAL_AUDIT_FELT_COL
  , newRoot := .var (afterFieldsRootCol EFFECT_VM_WIDTH)
  , op      := .write }

/-- **`refusalFieldsWriteV3`** — the LIVE rotated refusal WITH the record-digest pin (belt) AND the
FIELDS-ROOT WRITE GATE (suspenders): the deployment-real audit-slot WRITE forced on the live wire. Past
the graduated `rotateV3WithRecordPin` descriptor (the `refusalV3` base) it appends the single map-op that
FORCES the audit write on limb 36, repointing it from a record-pin-only (light-client-vacuous) limb into a
FORCED, written `fields_root`. -/
def refusalFieldsWriteV3 : EffectVmDescriptor2 :=
  let base := withRecordPin8Headroom2
    (graduateV1 (rotateV3WithRecordPin B_RECORD_DIGEST EffectVmEmitRefusal.refusalVmDescriptor))
  { base with
    constraints := base.constraints ++ [.mapOp refusalFieldsWriteOp] }

/-- **`refusalFieldsWriteV3_forces_write` — the live descriptor FORCES the audit-slot write (the
deployment-real tooth).** On a satisfying `refusalFieldsWriteV3` witness whose refusal selector fires, the
appended map-op holds: the AFTER `fields_root` (limb 36 of the after block) IS the genuine sorted write of
`(refusalAuditKeyFelt → auditFelt)` into the BEFORE `fields_root` (`writesTo`). Under CR this is FUNCTIONAL
(`writesTo_functional`), so a frozen or forged after-`fields_root` cannot satisfy the descriptor — the
light-client refusal forgery the record pin held only vacuously is now REJECTED in-circuit. -/
theorem refusalFieldsWriteV3_forces_write (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash refusalFieldsWriteV3 minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length)
    (hrefuse : (envAt t i).loc EffectVmEmitRefusal.SEL_REFUSAL = 1) :
    writesTo hash ((envAt t i).loc (beforeFieldsRootCol EFFECT_VM_WIDTH))
        refusalAuditKeyFelt
        ((envAt t i).loc REFUSAL_AUDIT_FELT_COL)
        ((envAt t i).loc (afterFieldsRootCol EFFECT_VM_WIDTH)) := by
  have hrowc := hsat.rowConstraints i hi
  have hwrite := hrowc (.mapOp refusalFieldsWriteOp) (by simp [refusalFieldsWriteV3])
  exact hwrite hrefuse

/-- The audit-write gate does NOT disturb graduation: the hash sites + ranges are the record-pinned
descriptor's verbatim (the map-op is a CONSTRAINT, and `graduable` reads only sites/ranges). -/
theorem graduable_rotateV3WithRecordPin_refusal :
    graduable (rotateV3WithRecordPin B_RECORD_DIGEST EffectVmEmitRefusal.refusalVmDescriptor) = true :=
  graduable_rotateV3WithRecordPin B_RECORD_DIGEST (by decide)

/-- The v1 denotation survives the record pin (the per-effect refusal faithfulness / anti-ghost theorems
compose through, exactly as for bare `rotateV3`). -/
theorem refusalFieldsWriteV3_satisfiedVm_v1 (hash : List ℤ → ℤ)
    (env : VmRowEnv) (isFirst isLast : Bool)
    (h : satisfiedVm hash (rotateV3WithRecordPin B_RECORD_DIGEST
      EffectVmEmitRefusal.refusalVmDescriptor) env isFirst isLast) :
    satisfiedVm hash EffectVmEmitRefusal.refusalVmDescriptor env isFirst isLast :=
  rotateV3WithRecordPin_satisfiedVm_v1 B_RECORD_DIGEST hash
    EffectVmEmitRefusal.refusalVmDescriptor env isFirst isLast h

#assert_axioms refusalFieldsWriteV3_forces_write
#assert_axioms graduable_rotateV3WithRecordPin_refusal
#assert_axioms refusalFieldsWriteV3_satisfiedVm_v1

-- The audit-write gate is the ONLY constraint past `refusalV3`'s, and it is a `.write` map-op on limb 36.
#guard refusalFieldsWriteV3.constraints.length == refusalV3.constraints.length + 8
#guard (mapOpsOf refusalFieldsWriteV3).length == 1
#guard refusalFieldsWriteOp.op == MapOpKind.write
#guard REFUSAL_AUDIT_FELT_COL == 70                          -- PARAM_BASE (68) + param2 (spare)
#guard beforeFieldsRootCol EFFECT_VM_WIDTH == EFFECT_VM_WIDTH + 36
#guard afterFieldsRootCol EFFECT_VM_WIDTH == EFFECT_VM_WIDTH + 91 + 36
-- BOTH POLARITIES of the write tooth's GUARD on the toy environment: the write fires under the refusal
-- selector (col 52 = 1) and is inert without it (the gate contributes nothing on a non-refusal pad row).
#guard (let env : VmRowEnv := ⟨fun c => if c == 52 then 1 else 0, fun _ => 0, fun _ => 0⟩;
        decide (refusalFieldsWriteOp.guard.eval env.loc = 1))    -- selector fires ⇒ write asserted
#guard (let env : VmRowEnv := ⟨fun _ => 0, fun _ => 0, fun _ => 0⟩;
        decide (refusalFieldsWriteOp.guard.eval env.loc ≠ 1))    -- no selector ⇒ map-op inert

/-- **`setProgramV3`** — the LIVE rotated SetProgram (the ordered mid-session program-install effect, the
genesis-reframe escape hatch) WITH the record-digest-forcing pin (the record-pin shape, `refusalV3`'s
family). The DEPLOYED `apply_set_program` (`turn/src/executor/apply.rs apply_set_program`) writes the
cell's `program` slot (`c.program = program`). The cell's `program` (a `CellProgram` / caveat table) is
NOT carried by any dedicated committed sub-limb — it is FOLDED, with permissions/VK/delegate/mode, into
`compute_authority_digest_felt` (`cell/src/commitment.rs` `compute_authority_digest_felt`, the `---
Program ---` arm), which is committed into the opaque authority residue register r23
(`B_RECORD_DIGEST = 24`). So a GENUINE program install MOVES the AFTER `record_digest` limb, exactly the
`setPermissions`/`setVK`-residue / `refusal` shape (a distinct authority surface from VK: the caveat
table, not the upgrade key). The record pin (`rotateV3WithRecordPin B_RECORD_DIGEST`) welds that AFTER
limb to the rotated PI; the verifier anchors PI 46 to `compute_authority_digest_felt(post_cell)` (the
SAME step-6b anchor `setPermissions`/`setVK`/`refusal` already run for this exact residue, so honest
proofs are NOT rejected), so a frozen-record-digest program forgery (claiming a program install that did
NOT move the authority residue) FAILS the pin and is UNSAT for a ledgerless client
(`rotateV3WithRecordPin_rejects_wrong_post`).

SetProgram rides the DEPLOYED setVK runtime row (`trace.rs` maps it to `sel::SET_VERIFICATION_KEY`, the
frozen-economic-frame + nonce-TICK passthrough — SetProgram ticks the nonce, it does NOT inherit a
freeze), so its v1 face is `EffectVmEmitSetVK.setVKVmDescriptor`. (The deployed runtime carries no
own `sel::SET_PROGRAM`; giving SetProgram its OWN runtime selector + its own actionTag is the named
executor-side residual — see `Dregg2.Circuit.Spec.cellstateprogram` / the
`RotatedKernelRefinementProgram` rung.) -/
-- H1 NOTE: setProgram rides the setVK runtime FACE (`trace.rs` maps it to `sel::SET_VERIFICATION_KEY`)
-- and is the named actionTag residual — the rotated record-pin PRODUCER (`record_pin_offset`) does NOT
-- yet pin it, so it stays limb-0-pinned (the record-pin8 headroom wrap lands when its producer path goes
-- live, alongside setFieldDyn). No regression: limb-0 ~31-bit, exactly its pre-H1 strength.
def setProgramV3 : EffectVmDescriptor2 :=
  graduateV1 (rotateV3WithRecordPin B_RECORD_DIGEST EffectVmEmitSetVK.setVKVmDescriptor)

/-- **`makeSovereignV3`** — the LIVE rotated makeSovereign WITH the LIVE mode gate (WAVE 3): the AFTER
block's committed MODE sub-limb (`B_MODE = 35`) is force-pinned to `Sovereign(1)` as a CONSTANT,
selector-gated on `SEL_MAKE_SOVEREIGN_RT`. A makeSovereign whose committed AFTER mode stays `Hosted(0)`
(an un-promoted sovereign) is now UNSAT via the in-circuit mode gate ALONE — no trusted post-cell
(`rotateV3WithModeGate_rejects_unpromoted`). The record pin on `B_RECORD_DIGEST` (PI 46) stays as
belt-and-suspenders for the opaque authority residue. -/
def makeSovereignV3 : EffectVmDescriptor2 :=
  withRecordPin8Headroom2 (graduateV1 (rotateV3WithModeGate EffectVmEmitMakeSovereign.SEL_MAKE_SOVEREIGN_RT
    modeSovereign EffectVmEmitMakeSovereign.makeSovereignRuntimeVmDescriptor))

/-- **`setFieldDynForcedV3`** — the LIVE rotated DYNAMIC setField WITH its memory ops AND the LIVE
fields-root weld (WAVE 3): the AFTER block's committed `fields_root` sub-limb (`B_FIELDS_ROOT = 36`) is
welded to the declared post-`fields_root` param column, selector-gated on `SEL_SET_FIELD`. A forged
post-`fields_root` (committed ≠ declared) is now UNSAT via the in-circuit weld ALONE
(`rotateV3WithFieldsRootGate_rejects_forged`). The Blum write→read transport (`setFieldDynV3`) rides
unchanged. -/
-- H1 NOTE: dynamic setField uses its OWN rotated trace generator (not the `record_pin_offset` builder),
-- so its record-pin8 headroom wrap lands when that producer emits the 7 headroom pins. Limb-0-pinned for
-- now (no regression — its fields-root sub-limb `B_FIELDS_ROOT` is independently welded by the gate).
def setFieldDynForcedV3 : EffectVmDescriptor2 :=
  let g := graduateV1 (rotateV3WithFieldsRootGate EffectVmEmitSetField.SEL_SET_FIELD
    (afterFieldsRootCol setFieldDynV1Face.traceWidth) setFieldDynV1Face)
  { g with constraints := g.constraints ++ [.memOp fieldWriteOp, .memOp fieldReadbackOp] }

/-- **`receiptArchiveV3`** — the LIVE rotated receiptArchive WITH the LIFECYCLE-forcing pin (limb
`B_LIFECYCLE = 29`). The DEPLOYED `apply_receipt_archive` writes the cell LIFECYCLE (`Archived`) via
`c.archive(checkpoint)` — NOT a `fields_root` record slot — so the genuine mover is `lifecycle_felt`
(`rotation_witness.rs::lifecycle_felt`, AFTER limb 29), which folds the archival checkpoint into a
distinct `Archived` felt. Pinning that limb to PI `38` forces it; the verifier anchors PI 46 to
`lifecycle_felt_cell(post_cell)` (the Class-2 path), so a frozen-lifecycle archive forgery (claiming
an archive that did not move the lifecycle) FAILS the pin and is UNSAT
(`rotateV3WithRecordPin_rejects_wrong_post`). This MATCHES the deployed apply (which moves the
lifecycle), where the prior `B_RECORD_DIGEST` route was a MIS-ROUTE (the deployed write does not move
the authority residue). AND (STAGE C, §5.LP) the archival checkpoint folded into `lifecycle_felt` is now
LIGHT-CLIENT-FORCED via the in-circuit payload-hash weld: a receiptArchive forged to a different
`checkpoint_hash` / `archived_through` is UNSAT ledgerless
(`rotateV3WithLifecyclePayloadGate_rejects_forged`). -/
def receiptArchiveV3 : EffectVmDescriptor2 :=
  graduateV1 (rotateV3WithLifecyclePayloadGate EffectVmEmitReceiptArchive.SEL_RECEIPT_ARCHIVE_RT none discArchived
    EffectVmEmitReceiptArchive.receiptArchiveActorVmDescriptor)

/-! ### The LIVE per-mover disc forcing + teeth (the deployment realization of
`RotatedKernelRefinementLifecycleDisc`'s `discAfterForced`-class theorems against the LIVE descriptors). -/

/-- **`cellSealV3_disc_forces_sealed` — the LIVE close: a satisfying cellSeal disc witness FORCES the
AFTER disc to `Sealed(1)` with NO trusted post-cell.** The deployed face of
`RotatedKernelRefinementLifecycleDisc.cellSeal_disc_forced.2`. -/
theorem cellSealV3_disc_forces_sealed (hash : List ℤ → ℤ) (env : VmRowEnv) (isFirst isLast : Bool)
    (hlast : isLast = false)
    (hsel : env.loc EffectVmEmitCellSeal.SEL_CELLSEAL = 1)
    (h : satisfiedVm hash (rotateV3WithDiscGate EffectVmEmitCellSeal.SEL_CELLSEAL (some discLive)
      discSealed EffectVmEmitCellSeal.cellSealVmDescriptor) env isFirst isLast) :
    env.loc (afterDiscCol EffectVmEmitCellSeal.cellSealVmDescriptor.traceWidth) = discSealed :=
  rotateV3WithDiscGate_forces_after _ _ _ hash _ env isFirst isLast hlast hsel h

/-- **TOOTH — `cellSealV3_rejects_frozen` (LIVE).** A cellSeal whose AFTER disc stays `Live(0)` (the
FROZEN seal — the headline lifecycle forgery) is UNSAT for a ledgerless client. -/
theorem cellSealV3_rejects_frozen (hash : List ℤ → ℤ) (env : VmRowEnv) (isFirst isLast : Bool)
    (hlast : isLast = false)
    (hsel : env.loc EffectVmEmitCellSeal.SEL_CELLSEAL = 1)
    (hfrozen : env.loc (afterDiscCol EffectVmEmitCellSeal.cellSealVmDescriptor.traceWidth) = discLive) :
    ¬ satisfiedVm hash (rotateV3WithDiscGate EffectVmEmitCellSeal.SEL_CELLSEAL (some discLive)
      discSealed EffectVmEmitCellSeal.cellSealVmDescriptor) env isFirst isLast := by
  apply rotateV3WithDiscGate_rejects_wrong_after _ _ _ hash _ env isFirst isLast hlast hsel
  rw [hfrozen]; decide

/-- **TOOTH — `cellDestroyV3_rejects_resurrection` (LIVE).** A cellDestroy whose AFTER disc is published
as `Live(0)` (a Destroyed cell republished as alive) is UNSAT for a ledgerless client — the disc gate
forces `Destroyed(3)`, no trusted post-cell. The deployed face of
`RotatedKernelRefinementLifecycleDisc.cellDestroy_disc_rejects_resurrection`. -/
theorem cellDestroyV3_rejects_resurrection (hash : List ℤ → ℤ) (env : VmRowEnv) (isFirst isLast : Bool)
    (hlast : isLast = false)
    (hsel : env.loc EffectVmEmitCellDestroy.SEL_CELLDESTROY = 1)
    (hres : env.loc (afterDiscCol EffectVmEmitCellDestroy.cellDestroyVmDescriptor.traceWidth) = discLive) :
    ¬ satisfiedVm hash (rotateV3WithDiscGate EffectVmEmitCellDestroy.SEL_CELLDESTROY none discDestroyed
      EffectVmEmitCellDestroy.cellDestroyVmDescriptor) env isFirst isLast := by
  apply rotateV3WithDiscGate_rejects_wrong_after _ _ _ hash _ env isFirst isLast hlast hsel
  rw [hres]; decide

#assert_axioms cellSealV3_disc_forces_sealed
#assert_axioms cellSealV3_rejects_frozen
#assert_axioms cellDestroyV3_rejects_resurrection

/-! ### §5.LP.DEPLOY — the LIVE per-mover lifecycle-PAYLOAD forcing + teeth (STAGE C, the deployment
realization of `rotateV3WithLifecyclePayloadGate` against the LIVE `cellSealV3`/`cellDestroyV3`/
`receiptArchiveV3`). These consume the DEPLOYED descriptor (the payload-gated one), so editing/removing
the gate REDS them — the LIGHT-CLIENT close, NO off-cell anchor. -/

/-- **`cellSealV3_payload_forced` — the LIVE close: a satisfying cellSeal witness FORCES the committed
AFTER lifecycle limb EQUAL to the in-circuit declared payload-hash column, with NO trusted post-cell.**
The deployed face of `rotateV3WithLifecyclePayloadGate_forces` against `cellSealV3`'s base. -/
theorem cellSealV3_payload_forced (hash : List ℤ → ℤ) (env : VmRowEnv) (isFirst isLast : Bool)
    (hlast : isLast = false)
    (hsel : env.loc EffectVmEmitCellSeal.SEL_CELLSEAL = 1)
    (h : satisfiedVm hash (rotateV3WithLifecyclePayloadGate EffectVmEmitCellSeal.SEL_CELLSEAL
      (some discLive) discSealed EffectVmEmitCellSeal.cellSealVmDescriptor) env isFirst isLast) :
    env.loc (afterLifecycleCol EffectVmEmitCellSeal.cellSealVmDescriptor.traceWidth)
      = env.loc declaredLifecyclePayloadCol :=
  rotateV3WithLifecyclePayloadGate_forces _ _ _ hash _ env isFirst isLast hlast hsel h

/-- **TOOTH — `cellSealV3_payload_rejects_forged_lightclient` (LIVE, LIGHT-CLIENT).** A cellSeal forged to
differ ONLY in the sealing PAYLOAD — a different `reason_hash` / `sealed_at`, so the committed AFTER
`lifecycle_felt` (limb 29) ≠ the in-circuit `payloadHash([disc, reason_hash, block_height])` — is UNSAT
through the deployed descriptor ALONE, NO off-cell anchor. This CONVERTS the §6 named residual: the forged
payload the record pin accepted (producer-free PI) is now REJECTED in-circuit. -/
theorem cellSealV3_payload_rejects_forged_lightclient (hash : List ℤ → ℤ) (env : VmRowEnv)
    (isFirst isLast : Bool) (hlast : isLast = false)
    (hsel : env.loc EffectVmEmitCellSeal.SEL_CELLSEAL = 1)
    (hforged : env.loc (afterLifecycleCol EffectVmEmitCellSeal.cellSealVmDescriptor.traceWidth)
      ≠ env.loc declaredLifecyclePayloadCol) :
    ¬ satisfiedVm hash (rotateV3WithLifecyclePayloadGate EffectVmEmitCellSeal.SEL_CELLSEAL
      (some discLive) discSealed EffectVmEmitCellSeal.cellSealVmDescriptor) env isFirst isLast :=
  rotateV3WithLifecyclePayloadGate_rejects_forged _ _ _ hash _ env isFirst isLast hlast hsel hforged

/-- **TOOTH — `cellDestroyV3_payload_rejects_forged_lightclient` (LIVE).** A cellDestroy forged to differ in
the death-certificate payload (`death_certificate_hash` / `destroyed_at`) folded into `lifecycle_felt` is
UNSAT ledgerless — the in-circuit payload weld bites. -/
theorem cellDestroyV3_payload_rejects_forged_lightclient (hash : List ℤ → ℤ) (env : VmRowEnv)
    (isFirst isLast : Bool) (hlast : isLast = false)
    (hsel : env.loc EffectVmEmitCellDestroy.SEL_CELLDESTROY = 1)
    (hforged : env.loc (afterLifecycleCol EffectVmEmitCellDestroy.cellDestroyVmDescriptor.traceWidth)
      ≠ env.loc declaredLifecyclePayloadCol) :
    ¬ satisfiedVm hash (rotateV3WithLifecyclePayloadGate EffectVmEmitCellDestroy.SEL_CELLDESTROY
      none discDestroyed EffectVmEmitCellDestroy.cellDestroyVmDescriptor) env isFirst isLast :=
  rotateV3WithLifecyclePayloadGate_rejects_forged _ _ _ hash _ env isFirst isLast hlast hsel hforged

/-- **TOOTH — `receiptArchiveV3_payload_rejects_forged_lightclient` (LIVE).** A receiptArchive forged to
differ in the archival checkpoint (`checkpoint_hash` / `archived_through`) folded into `lifecycle_felt` is
UNSAT ledgerless. -/
theorem receiptArchiveV3_payload_rejects_forged_lightclient (hash : List ℤ → ℤ) (env : VmRowEnv)
    (isFirst isLast : Bool) (hlast : isLast = false)
    (hsel : env.loc EffectVmEmitReceiptArchive.SEL_RECEIPT_ARCHIVE_RT = 1)
    (hforged : env.loc
      (afterLifecycleCol EffectVmEmitReceiptArchive.receiptArchiveActorVmDescriptor.traceWidth)
      ≠ env.loc declaredLifecyclePayloadCol) :
    ¬ satisfiedVm hash (rotateV3WithLifecyclePayloadGate EffectVmEmitReceiptArchive.SEL_RECEIPT_ARCHIVE_RT
      none discArchived EffectVmEmitReceiptArchive.receiptArchiveActorVmDescriptor) env isFirst isLast :=
  rotateV3WithLifecyclePayloadGate_rejects_forged _ _ _ hash _ env isFirst isLast hlast hsel hforged

#assert_axioms cellSealV3_payload_forced
#assert_axioms cellSealV3_payload_rejects_forged_lightclient
#assert_axioms cellDestroyV3_payload_rejects_forged_lightclient
#assert_axioms receiptArchiveV3_payload_rejects_forged_lightclient

/-! ### The LIVE per-mover perms/VK forcing + teeth (WAVE 2 — the deployment realization of
`RotatedKernelRefinementPermsVK`'s `{setPermissions,setVK}_slot_forced` against the LIVE descriptors). -/

/-- **`setPermsV3_forces_declared` — the LIVE close: a satisfying setPermissions witness FORCES the
committed AFTER perms-digest sub-limb EQUAL to the in-circuit declared param, with NO trusted post-cell.**
The deployed face of `RotatedKernelRefinementPermsVK.setPermissions_slot_forced`. -/
theorem setPermsV3_forces_declared (hash : List ℤ → ℤ) (env : VmRowEnv) (isFirst isLast : Bool)
    (hlast : isLast = false)
    (hsel : env.loc EffectVmEmitSetPermissions.SEL_SET_PERMS = 1)
    (h : satisfiedVm hash (rotateV3WithPermsVKGate EffectVmEmitSetPermissions.SEL_SET_PERMS
      (afterPermsCol EffectVmEmitSetPermissions.setPermsVmDescriptor.traceWidth)
      EffectVmEmitSetPermissions.setPermsVmDescriptor) env isFirst isLast) :
    env.loc (afterPermsCol EffectVmEmitSetPermissions.setPermsVmDescriptor.traceWidth)
      = env.loc declaredParamCol :=
  rotateV3WithPermsVKGate_forces _ _ hash _ env isFirst isLast hlast hsel h

/-- **TOOTH — `setPermsV3_rejects_forged` (LIVE).** A setPermissions whose committed AFTER perms-digest
≠ the declared (PI-anchored) param — a forged post-permissions binding ARBITRARY permissions into
NEW_COMMIT — is UNSAT for a ledgerless client. The headline setPermissions authority forgery, closed
in-circuit with no trusted post-cell. -/
theorem setPermsV3_rejects_forged (hash : List ℤ → ℤ) (env : VmRowEnv) (isFirst isLast : Bool)
    (hlast : isLast = false)
    (hsel : env.loc EffectVmEmitSetPermissions.SEL_SET_PERMS = 1)
    (hforged : env.loc (afterPermsCol EffectVmEmitSetPermissions.setPermsVmDescriptor.traceWidth)
      ≠ env.loc declaredParamCol) :
    ¬ satisfiedVm hash (rotateV3WithPermsVKGate EffectVmEmitSetPermissions.SEL_SET_PERMS
      (afterPermsCol EffectVmEmitSetPermissions.setPermsVmDescriptor.traceWidth)
      EffectVmEmitSetPermissions.setPermsVmDescriptor) env isFirst isLast :=
  rotateV3WithPermsVKGate_rejects_forged _ _ hash _ env isFirst isLast hlast hsel hforged

/-- **TOOTH — `setVKV3_rejects_forged` (LIVE).** A setVK whose committed AFTER vk-digest ≠ the declared
(PI-anchored) param — a forged post-VK (the upgrade-safety forgery: binding an ARBITRARY verification
key into NEW_COMMIT) — is UNSAT for a ledgerless client, no trusted post-cell. -/
theorem setVKV3_rejects_forged (hash : List ℤ → ℤ) (env : VmRowEnv) (isFirst isLast : Bool)
    (hlast : isLast = false)
    (hsel : env.loc EffectVmEmitSetVK.SEL_SET_VK = 1)
    (hforged : env.loc (afterVKCol EffectVmEmitSetVK.setVKVmDescriptor.traceWidth)
      ≠ env.loc declaredParamCol) :
    ¬ satisfiedVm hash (rotateV3WithPermsVKGate EffectVmEmitSetVK.SEL_SET_VK
      (afterVKCol EffectVmEmitSetVK.setVKVmDescriptor.traceWidth)
      EffectVmEmitSetVK.setVKVmDescriptor) env isFirst isLast :=
  rotateV3WithPermsVKGate_rejects_forged _ _ hash _ env isFirst isLast hlast hsel hforged

#assert_axioms setPermsV3_forces_declared
#assert_axioms setPermsV3_rejects_forged
#assert_axioms setVKV3_rejects_forged

/-! ### The LIVE per-mover mode / fields-root forcing + teeth (WAVE 3 — the deployment realization of
the makeSovereign mode promotion + the setFieldDyn / refusal fields-root weld against the LIVE
descriptors). -/

/-- **`makeSovereignV3_forces_sovereign` — the LIVE close: a satisfying makeSovereign witness FORCES the
committed AFTER mode sub-limb to `Sovereign(1)` as a CONSTANT, with NO trusted post-cell.** -/
theorem makeSovereignV3_forces_sovereign (hash : List ℤ → ℤ) (env : VmRowEnv) (isFirst isLast : Bool)
    (hlast : isLast = false)
    (hsel : env.loc EffectVmEmitMakeSovereign.SEL_MAKE_SOVEREIGN_RT = 1)
    (h : satisfiedVm hash (rotateV3WithModeGate EffectVmEmitMakeSovereign.SEL_MAKE_SOVEREIGN_RT
      modeSovereign EffectVmEmitMakeSovereign.makeSovereignRuntimeVmDescriptor) env isFirst isLast) :
    env.loc (afterModeCol EffectVmEmitMakeSovereign.makeSovereignRuntimeVmDescriptor.traceWidth)
      = modeSovereign :=
  rotateV3WithModeGate_forces_after _ _ hash _ env isFirst isLast hlast hsel h

/-- **TOOTH — `makeSovereignV3_rejects_unpromoted` (LIVE).** A makeSovereign whose committed AFTER mode
stays `Hosted(0)` (an un-promoted sovereign — the cell claims sovereignty without flipping the committed
mode) is UNSAT for a ledgerless client, no trusted post-cell. The headline makeSovereign forgery. -/
theorem makeSovereignV3_rejects_unpromoted (hash : List ℤ → ℤ) (env : VmRowEnv) (isFirst isLast : Bool)
    (hlast : isLast = false)
    (hsel : env.loc EffectVmEmitMakeSovereign.SEL_MAKE_SOVEREIGN_RT = 1)
    (hunpromoted : env.loc
        (afterModeCol EffectVmEmitMakeSovereign.makeSovereignRuntimeVmDescriptor.traceWidth)
      = modeHosted) :
    ¬ satisfiedVm hash (rotateV3WithModeGate EffectVmEmitMakeSovereign.SEL_MAKE_SOVEREIGN_RT
      modeSovereign EffectVmEmitMakeSovereign.makeSovereignRuntimeVmDescriptor) env isFirst isLast := by
  apply rotateV3WithModeGate_rejects_unpromoted _ _ hash _ env isFirst isLast hlast hsel
  rw [hunpromoted]; decide

/-- **TOOTH — `setFieldDynV3_rejects_forged` (LIVE).** A dynamic setField whose committed AFTER
`fields_root` sub-limb ≠ the declared post-`fields_root` param — a forged post-`fields_root` (the
dynamic write committed to an arbitrary overflow map) — is UNSAT for a ledgerless client. -/
theorem setFieldDynV3_rejects_forged (hash : List ℤ → ℤ) (env : VmRowEnv) (isFirst isLast : Bool)
    (hlast : isLast = false)
    (hsel : env.loc EffectVmEmitSetField.SEL_SET_FIELD = 1)
    (hforged : env.loc (afterFieldsRootCol setFieldDynV1Face.traceWidth)
      ≠ env.loc declaredFieldsRootCol) :
    ¬ satisfiedVm hash (rotateV3WithFieldsRootGate EffectVmEmitSetField.SEL_SET_FIELD
      (afterFieldsRootCol setFieldDynV1Face.traceWidth) setFieldDynV1Face) env isFirst isLast :=
  rotateV3WithFieldsRootGate_rejects_forged _ _ hash _ env isFirst isLast hlast hsel hforged

#assert_axioms makeSovereignV3_forces_sovereign
#assert_axioms makeSovereignV3_rejects_unpromoted
#assert_axioms setFieldDynV3_rejects_forged

-- The mode / fields-root force-cols land at AFTER limb 35 / 36 (= traceWidth + 91 + 35 / +36).
#guard afterModeCol EFFECT_VM_WIDTH == EFFECT_VM_WIDTH + 91 + 35
#guard afterFieldsRootCol EFFECT_VM_WIDTH == EFFECT_VM_WIDTH + 91 + 36
#guard beforeModeCol EFFECT_VM_WIDTH == EFFECT_VM_WIDTH + 35
#guard declaredFieldsRootCol == prmCol 0
#guard decide (modeHosted ≠ modeSovereign)

-- The perms/vk force-cols land at AFTER limb 33 / 34 (= traceWidth + 91 + 33 / +34).
#guard afterPermsCol EFFECT_VM_WIDTH == EFFECT_VM_WIDTH + 91 + 33
#guard afterVKCol EFFECT_VM_WIDTH == EFFECT_VM_WIDTH + 91 + 34
#guard declaredParamCol == prmCol 0

-- The disc discriminants are pairwise distinct (the gate distinguishes lifecycle states).
#guard decide (discLive ≠ discSealed)
#guard decide (discSealed ≠ discDestroyed)
#guard decide (discDestroyed ≠ discArchived)
#guard decide (discLive ≠ discArchived)
-- The disc force-cols land at AFTER limb 32 (= traceWidth + 91 + 32) and BEFORE limb 32.
#guard afterDiscCol EFFECT_VM_WIDTH == EFFECT_VM_WIDTH + 91 + 32
#guard beforeDiscCol EFFECT_VM_WIDTH == EFFECT_VM_WIDTH + 32

#assert_axioms graduable_rotateV3WithRecordPin
#assert_axioms rotateV3WithRecordPin_pins
#assert_axioms rotateV3WithRecordPin_rejects_wrong_post
#assert_axioms rotateV3WithRecordPin_satisfiedVm_v1

-- The record pin lands at PI slot 46 (one past the four rotated commit pins 34..37); each forced
-- descriptor publishes 39 PIs, and graduation survives the appended pin.
#guard (rotateV3 EffectVmEmitCellSeal.cellSealVmDescriptor).piCount == 46
#guard cellSealV3.piCount == 47
#guard cellUnsealV3.piCount == 47
#guard cellDestroyV3.piCount == 47
#guard setPermsV3.piCount == 54
#guard setVKV3.piCount == 54
#guard refusalV3.piCount == 47
#guard receiptArchiveV3.piCount == 47
#guard graduable (rotateV3WithRecordPin B_RECORD_DIGEST EffectVmEmitRefusal.refusalVmDescriptor)
#guard graduable (rotateV3WithRecordPin B_LIFECYCLE
        EffectVmEmitReceiptArchive.receiptArchiveActorVmDescriptor)
#guard graduable (rotateV3WithRecordPin B_LIFECYCLE EffectVmEmitCellSeal.cellSealVmDescriptor)
#guard graduable (rotateV3WithRecordPin B_LIFECYCLE EffectVmEmitCellUnseal.cellUnsealVmDescriptor)
#guard graduable (rotateV3WithRecordPin B_LIFECYCLE EffectVmEmitCellDestroy.cellDestroyVmDescriptor)
#guard graduable (rotateV3WithRecordPin B_RECORD_DIGEST EffectVmEmitSetPermissions.setPermsVmDescriptor)
#guard graduable (rotateV3WithRecordPin B_RECORD_DIGEST EffectVmEmitSetVK.setVKVmDescriptor)
-- The disc-gated movers graduate (the appended disc gates are CONSTRAINTS; graduation reads
-- only sites/ranges, which are `rotateV3WithRecordPin`'s verbatim).
#guard graduable (rotateV3WithDiscGate EffectVmEmitCellSeal.SEL_CELLSEAL (some discLive) discSealed
        EffectVmEmitCellSeal.cellSealVmDescriptor)
#guard graduable (rotateV3WithDiscGate EffectVmEmitCellUnseal.SEL_CELLUNSEAL (some discSealed) discLive
        EffectVmEmitCellUnseal.cellUnsealVmDescriptor)
#guard graduable (rotateV3WithDiscGate EffectVmEmitCellDestroy.SEL_CELLDESTROY none discDestroyed
        EffectVmEmitCellDestroy.cellDestroyVmDescriptor)
#guard graduable (rotateV3WithDiscGate EffectVmEmitReceiptArchive.SEL_RECEIPT_ARCHIVE_RT none discArchived
        EffectVmEmitReceiptArchive.receiptArchiveActorVmDescriptor)
-- The perms/VK-gated movers graduate (the appended weld is a CONSTRAINT; graduation reads only
-- sites/ranges, which are `rotateV3WithRecordPin`'s verbatim).
#guard graduable (rotateV3WithPermsVKGate EffectVmEmitSetPermissions.SEL_SET_PERMS
        (afterPermsCol EffectVmEmitSetPermissions.setPermsVmDescriptor.traceWidth)
        EffectVmEmitSetPermissions.setPermsVmDescriptor)
#guard graduable (rotateV3WithPermsVKGate EffectVmEmitSetVK.SEL_SET_VK
        (afterVKCol EffectVmEmitSetVK.setVKVmDescriptor.traceWidth)
        EffectVmEmitSetVK.setVKVmDescriptor)
-- The WAVE-3 mode / fields-root-gated movers graduate (the appended gate is a CONSTRAINT; graduation
-- reads only sites/ranges, which are `rotateV3WithRecordPin`'s verbatim).
#guard graduable (rotateV3WithModeGate EffectVmEmitMakeSovereign.SEL_MAKE_SOVEREIGN_RT modeSovereign
        EffectVmEmitMakeSovereign.makeSovereignRuntimeVmDescriptor)
#guard graduable (rotateV3WithFieldsRootGate 52
        (afterFieldsRootCol EffectVmEmitRefusal.refusalVmDescriptor.traceWidth)
        EffectVmEmitRefusal.refusalVmDescriptor)
#guard graduable (rotateV3WithFieldsRootGate EffectVmEmitSetField.SEL_SET_FIELD
        (afterFieldsRootCol setFieldDynV1Face.traceWidth) setFieldDynV1Face)
-- cellSeal carries the record pin + BOTH disc gates (before + after) past its bare `rotateV3` form
-- (+3); setPerms / setVK carry the record pin + the WAVE-2 perms/vk weld (+2).
-- cellSeal: record pin (1) + before-disc + after-disc (2) + lifecycle-payload weld (1) = +4.
#guard cellSealV3.constraints.length
        == (v3Of EffectVmEmitCellSeal.cellSealVmDescriptor).constraints.length + 4
-- cellDestroy: record pin (1) + after-disc (1, no before-pin) + lifecycle-payload weld (1) = +3.
#guard cellDestroyV3.constraints.length
        == (v3Of EffectVmEmitCellDestroy.cellDestroyVmDescriptor).constraints.length + 3
-- setPerms / setVK: record pin (1) + perms/vk limb-0 weld (1) + 7 H1 headroom pins + the v10
-- 7 completion-felt welds (`withPermsVK8Weld`) = +16.
#guard setPermsV3.constraints.length
        == (v3Of EffectVmEmitSetPermissions.setPermsVmDescriptor).constraints.length + 16
#guard setVKV3.constraints.length
        == (v3Of EffectVmEmitSetVK.setVKVmDescriptor).constraints.length + 16
-- The WAVE-3 movers: makeSovereign carries the record pin + the mode gate (+2 over bare rotateV3);
-- refusal carries the record pin ALONE (+1) — its deployed `param0`/`param1` carry the refusal
-- target/reason, not a post-`fields_root` digest, so there is no in-circuit declared-param weld for
-- its `fields_root` sub-limb; the record-digest pin (verifier-anchored to
-- `compute_authority_digest_felt(post_cell)`, which folds the `fields_root` audit write) is the
-- single in-circuit close. setFieldDynForced carries the record pin + the fields-root weld + its 2
-- mem ops.
#guard makeSovereignV3.constraints.length
        == (v3Of EffectVmEmitMakeSovereign.makeSovereignRuntimeVmDescriptor).constraints.length + 9
#guard refusalV3.constraints.length
        == (v3Of EffectVmEmitRefusal.refusalVmDescriptor).constraints.length + 1
-- The forced AFTER limbs are the lifecycle limb (col tw+51+29) and the record-digest limb (col
-- tw+51+24), plus the WAVE-3 mode (tw+51+35) / fields-root (tw+51+36) limbs — the producer-witnessed
-- limbs the commitment binds but `rotateV3` did not force.
#guard B_LIFECYCLE == 29
#guard B_RECORD_DIGEST == 24
-- BOTH POLARITIES of the deployment tooth, executable on a toy LAST row (AFTER lifecycle limb at col
-- tw+47+29; with tw = 186 that is col 262; PI 46 carries the recomputed post felt). A row whose AFTER
-- limb equals PI[46] PASSES the pin; a frozen / wrong one FAILS it (the forgery is rejected).
#guard (let off := B_LIFECYCLE; let tw := (186 : Nat);
        let env : VmRowEnv := ⟨fun c => if c == tw + 91 + off then 1 else 0, fun _ => 0, fun k => if k == 46 then 1 else 0⟩;
        decide (env.loc (tw + 91 + off) = env.pub 46))   -- sealed (1) == PI[46] ⇒ pin holds
#guard (let off := B_LIFECYCLE; let tw := (186 : Nat);
        let env : VmRowEnv := ⟨fun c => if c == tw + 91 + off then 0 else 0, fun _ => 0, fun k => if k == 46 then 1 else 0⟩;
        decide (env.loc (tw + 91 + off) ≠ env.pub 46))   -- frozen-Live (0) ≠ sealed PI[46] ⇒ pin REJECTS

/-- **`v3Registry`** — the full 35-member cohort at the rotated block (the 27 v2-graduated members
+ the 8 STEP-1-widened; keys = the v2 keys suffixed `R24`; wire strings via `emitVmJson2`; driver
`EmitRotationV3.lean`). -/
def v3Registry : List (String × EffectVmDescriptor2) :=
  [ ("transferVmDescriptor2R24", v3OfFrozen EffectVmEmitTransfer.transferVmDescriptor)
  , ("burnVmDescriptor2R24", v3OfFrozen EffectVmEmitBurn.burnVmDescriptor)
  , ("mintVmDescriptor2R24", withSelectorGate EffectVmEmitMint.selM.MINT mintV3)
  , ("noteSpendVmDescriptor2R24", noteSpendV3)
  , ("noteCreateVmDescriptor2R24", noteCreateV3)
  , ("cellSealVmDescriptor2R24", cellSealV3)
  , ("cellDestroyVmDescriptor2R24", cellDestroyV3)
  , ("refusalVmDescriptor2R24", refusalFieldsWriteV3)
  , ("setPermsVmDescriptor2R24", setPermsV3)
  , ("setVKVmDescriptor2R24", setVKV3)
  , ("exerciseVmDescriptor2R24", v3Of EffectVmEmitExercise.exerciseVmDescriptor)
  , ("pipelinedSendVmDescriptor2R24", v3Of EffectVmEmitPipelinedSend.pipelinedSendVmDescriptor)
  , ("refreshVmDescriptor2R24", v3Of EffectVmEmitRefreshDelegation.refreshVmDescriptor)
  , ("incrementNonceVmDescriptor2R24",
      v3OfFrozen EffectVmEmitIncrementNonce.incrementNonceVmDescriptor)
  , ("revokeVmDescriptor2R24", v3Of EffectVmEmitRevokeDelegation.revokeVmDescriptor)
  , ("introduceVmDescriptor2R24", v3Of EffectVmEmitIntroduce.introduceVmDescriptor)
  , ("attenuateVmDescriptor2R24", withSelectorGate sel.ATTENUATE_CAPABILITY attenuateV3)
  , ("revokeCapabilityVmDescriptor2R24", withSelectorGate sel.REVOKE_CAPABILITY revokeCapabilityV3)
  , ("customVmDescriptor2R24", customV3)
  , ("setFieldDynVmDescriptor2R24", setFieldDynForcedV3)
    -- THE COHORT-WIDENING (ROTATION-CUTOVER §2c, STEP 1): the eight LIVE-path effects that
    -- the v2 graduation never covered but the v1 wire DID — their graduated RUNTIME row
    -- (frozen-frame / passthrough + nonce-tick) lifted through the SAME `rotateV3`, so the
    -- soundness keystones (`rotV3_sound_v1`, `rotV3_binds_published`) apply to them with the
    -- per-member graduability `#guard`s below and no new proof. Deleting v1 no longer bricks
    -- them. GrantCapability rides the BARE attenuate template (`dregg-effectvm-attenuateA-v1`,
    -- the UNATTENUATED cap-root grant — the v1 GRANT_CAP descriptor), distinct from the
    -- ATTENUATE_CAPABILITY phase-B `attenuateV3`.
  , ("grantCapVmDescriptor2R24",
      withSelectorGate sel.GRANT_CAP (v3Of EffectVmEmitAttenuateA.attenuateVmDescriptor))
  , ("makeSovereignVmDescriptor2R24", makeSovereignV3)
  , ("createCellVmDescriptor2R24", createCellV3)
  , ("factoryVmDescriptor2R24", factoryV3)
  , ("spawnVmDescriptor2R24", spawnV3)
  , ("receiptArchiveVmDescriptor2R24", receiptArchiveV3)
  , ("cellUnsealVmDescriptor2R24", cellUnsealV3)
  , ("emitEventVmDescriptor2R24", v3OfFrozen EffectVmEmitEmitEvent.emitEventVmDescriptor) ]
  ++ (List.finRange 8).map fun slot =>
      (s!"setFieldVmDescriptor2-{slot.val}R24",
        withSelectorGate EffectVmEmitSetField.SEL_SET_FIELD (v3OfFrozen (setFieldTickFace slot)))

#guard v3Registry.length == 36
-- Every registry entry emits a versioned v2 wire string with the rotated width, the five
-- EPOCH tables, and the four appended PI slots.
#guard v3Registry.all fun (_, d) => (emitVmJson2 d).startsWith "{\"name\":\""
-- Phase B-GATE: each graduated registry descriptor's width is the rotated base PLUS `7·n_sites`
-- lane columns (n_sites varies by v1 face), so the width is `≥ base` and the surplus is a
-- multiple of 7 (`CHIP_OUT_LANES - 1`). Concrete per-descriptor widths are pinned by the
-- emit goldens + the Rust registry fingerprints.
#guard v3Registry.all fun (_, d) =>
  EFFECT_VM_WIDTH + APPENDIX_SPAN ≤ d.traceWidth
    && (d.traceWidth - (EFFECT_VM_WIDTH + APPENDIX_SPAN)) % (CHIP_OUT_LANES - 1) == 0
#guard v3Registry.all fun (_, d) => d.tables.length == 5
#guard v3Registry.all fun (_, d) => d.hashSites.length == 0 && d.ranges.length == 0
-- The rotated transfer: the v1 graduation's constraints + 24 welds + 4 pins + 56 chip sites (v10).
#guard (v3Of EffectVmEmitTransfer.transferVmDescriptor).constraints.length
        == transferVmDescriptor2.constraints.length + 24 + 4 + 56
#guard (v3Of EffectVmEmitTransfer.transferVmDescriptor).piCount == 42 + 4
-- The graduation side conditions hold on every v1-faced member (per-instance witnesses of
-- the parametric `graduable_rotateV3`; attenuate/setFieldDyn ride `v3OfWith` over faces
-- checked here too).
#guard graduable (rotateV3 EffectVmEmitTransfer.transferVmDescriptor)
#guard graduable (rotateV3 setFieldDynV1Face)
#guard graduable (rotateV3 EffectVmEmitAttenuateA.attenuateVmDescriptor)
#guard graduable (rotateV3 EffectVmEmitRevokeCapability.revokeCapabilityVmDescriptor)
-- The COHORT-WIDENING faces (STEP 1): each graduable, so `rotV3_sound_v1` /
-- `rotV3_binds_published` apply to them with no new proof. (GrantCapability rides the
-- attenuate template already guarded above.)
#guard graduable (rotateV3 EffectVmEmitMakeSovereign.makeSovereignRuntimeVmDescriptor)
#guard graduable (rotateV3 EffectVmEmitCreateCell.createCellActorVmDescriptor)
#guard graduable (rotateV3 EffectVmEmitCreateCellFromFactory.factoryActorVmDescriptor)
#guard graduable (rotateV3 EffectVmEmitSpawn.spawnActorVmDescriptor)
#guard graduable (rotateV3 EffectVmEmitReceiptArchive.receiptArchiveActorVmDescriptor)
#guard graduable (rotateV3 EffectVmEmitCellUnseal.cellUnsealVmDescriptor)
#guard graduable (rotateV3 EffectVmEmitEmitEvent.emitEventVmDescriptor)
-- The extras ride: attenuate carries its 3 phase-B constraints (held-read + keep-write + submask),
-- revoke its 2 cap-crown constraints (held-read + remove-write, no submask), setFieldDyn its 2 mem ops.
-- Both rebased onto the ROTATED-limb cap-write base (`v3OfWithCapWrite` over the tick face — the
-- silent-forge close).
#guard attenuateV3.constraints.length
        == (v3OfCapWrite EffectVmEmitAttenuateA.attenuateVmDescriptorGenuineNoRecomputeTick).constraints.length + 3
#guard revokeCapabilityV3.constraints.length
        == (v3OfCapWrite EffectVmEmitAttenuateA.attenuateVmDescriptorGenuineNoRecomputeTick).constraints.length + 2
#guard (memOpsOf setFieldDynV3).length == 2
#guard (mapOpsOf setFieldDynV3).length == 0
#guard (mapOpsOf attenuateV3).length == 2
#guard (mapOpsOf revokeCapabilityV3).length == 2
-- The cap-family WRITE close: delegate/grantCap carry held-read + insert-write (2 map ops);
-- delegateAtten ALSO the submask lookup (+1 constraint, 2 map ops). The post-cap-root WRITE is
-- now FORCED on the live wire (guarantee A — Authority — circuit-forced for these slots), on the
-- ROTATED cap-root limb (`v3OfCapWrite` — the cap-root weld dropped, note-spend-shaped).
#guard delegateV3.constraints.length
        == (v3OfCapWrite EffectVmEmitAttenuateA.attenuateVmDescriptorGenuineNoRecomputeTick).constraints.length + 2
#guard grantCapWriteV3.constraints.length
        == (v3OfCapWrite EffectVmEmitAttenuateA.attenuateVmDescriptorGenuineNoRecomputeTick).constraints.length + 2
#guard delegateAttenV3.constraints.length
        == (v3OfCapWrite EffectVmEmitAttenuateA.attenuateVmDescriptorGenuineNoRecomputeTick).constraints.length + 3
#guard (mapOpsOf delegateV3).length == 2
#guard (mapOpsOf grantCapWriteV3).length == 2
#guard (mapOpsOf delegateAttenV3).length == 2
-- The rotated Custom carries EXACTLY its one proof-binding op + the eight `customPiExposure`
-- PI pins past the rotated passthrough base (no mem/map ops — the recursive-proof binding is
-- Custom's only NEWLY-EXPRESSIBLE leg; the eight pins publish its bound (commit, vk) columns).
#guard customV3.constraints.length == (v3Of customV1Face).constraints.length + 1 + 8
#guard (proofBindsOf customV3).length == 1
#guard (memOpsOf customV3).length == 0
#guard (mapOpsOf customV3).length == 0
#guard graduable (rotateV3 customV1Face)

/-! ### The extras' theorems, transported (the §7/§8 legs survive the rotation). -/

/-- The extras' op surface is EXACTLY the original's: the rotated graduation contributes
no mem ops (both sides are concrete lists; the kernel decides this by reduction). -/
theorem memOpsOf_setFieldDynV3 : memOpsOf setFieldDynV3 = memOpsOf setFieldDynVmDescriptor2 :=
  rfl

/-- The rotated attenuate's map ops are the ROTATED-limb read/write pair, FIRING-guarded
(`sel.ATTENUATE_CAPABILITY`) — the silent-forge close. -/
theorem mapOpsOf_attenuateV3 :
    mapOpsOf attenuateV3 = [heldReadOpRot sel.ATTENUATE_CAPABILITY, keepWriteOpRot sel.ATTENUATE_CAPABILITY] :=
  rfl

/-- The rotated dynamic setField's memory log IS the original's (op-for-op): both
descriptors declare the same two mem ops, so the gathered logs coincide definitionally —
the Blum write→read transport transports verbatim. -/
theorem setFieldDynV3_memLog (t : VmTrace) :
    memLog setFieldDynV3 t = memLog setFieldDynVmDescriptor2 t := rfl

/-- **The rotated dynamic write→read transport** — Blum applied, zero hashing, at the
rotated block: on a satisfying one-row active trace the read-back column carries EXACTLY
the written value (the §8 keystone, transported through `setFieldDynV3_memLog`). -/
theorem setFieldDynV3_readback_genuine (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hone : t.rows.length = 1)
    (hactive : (envAt t 0).loc EffectVmEmitSetField.SEL_SET_FIELD = 1)
    (hsat : Satisfied2 hash setFieldDynV3 minit mfin maddrs t) :
    (envAt t 0).loc (prmCol READBACK) = (envAt t 0).loc (prmCol NEW_VAL) := by
  have hcons := satisfied2_mem_consistent hash _ minit mfin maddrs t hsat
  rw [setFieldDynV3_memLog, setFieldDyn_memLog t hone hactive] at hcons
  obtain ⟨_, hr, _⟩ := hcons
  have := hr rfl
  simpa [MemoryChecking.step] using this

/-- **The rotated cap-crown phase-B leg, on the ROTATED-limb write path (the silent-forge close)** —
on an active attenuate row of a `Satisfied2` witness of the ROTATED attenuate (the held key
authenticated against the BEFORE rotated cap-root limb `beforeCapRootCol`, the post rotated cap-root
limb `afterCapRootCol` the genuine sorted UPDATE-AT-KEY of the narrowed rights, `keep ⊑ held` bitwise).
The map_op FIRES on the FIRING selector (`sel.ATTENUATE_CAPABILITY`), so the AFTER cap-root (var 264) is
GENUINELY bound — NOT the never-firing var2-guarded V1-state col 87 (forgeable). -/
theorem attenuateV3_non_amp (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hsub : t.tf (.custom SUBMASK_TID) = subsetTable MASK_BITS)
    (hsat : Satisfied2 hash attenuateV3 minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length)
    (hactive : (envAt t i).loc sel.ATTENUATE_CAPABILITY = 1) :
    opensTo hash ((envAt t i).loc (beforeCapRootCol EFFECT_VM_WIDTH))
        ((envAt t i).loc (prmCol CAP_KEY)) (some ((envAt t i).loc (prmCol HELD_MASK)))
    ∧ writesTo hash ((envAt t i).loc (beforeCapRootCol EFFECT_VM_WIDTH))
        ((envAt t i).loc (prmCol CAP_KEY)) ((envAt t i).loc (prmCol KEEP_MASK))
        ((envAt t i).loc (afterCapRootCol EFFECT_VM_WIDTH))
    ∧ ∃ a b : Nat, (envAt t i).loc (prmCol KEEP_MASK) = (a : ℤ)
        ∧ (envAt t i).loc (prmCol HELD_MASK) = (b : ℤ) ∧ a &&& b = a := by
  have hrowc := hsat.rowConstraints i hi
  have hmem : ∀ c ∈ ([.mapOp (heldReadOpRot sel.ATTENUATE_CAPABILITY),
      .mapOp (keepWriteOpRot sel.ATTENUATE_CAPABILITY), .lookup submaskLookup] :
      List VmConstraint2), c ∈ attenuateV3.constraints :=
    fun c hc => List.mem_append_right _ hc
  have hread := hrowc (.mapOp (heldReadOpRot sel.ATTENUATE_CAPABILITY)) (hmem _ (by simp))
  have hwrite := hrowc (.mapOp (keepWriteOpRot sel.ATTENUATE_CAPABILITY)) (hmem _ (by simp))
  have hlook := hrowc (.lookup submaskLookup) (hmem _ (by simp))
  have hr := hread hactive
  have hw := hwrite hactive
  refine ⟨hr.1, hw, ?_⟩
  have hlook' : [(envAt t i).loc (prmCol KEEP_MASK), (envAt t i).loc (prmCol HELD_MASK)]
      ∈ t.tf (.custom SUBMASK_TID) := hlook
  rw [hsub] at hlook'
  obtain ⟨a, b, _, _, hab, hx, hy⟩ := (subsetTable_mem_iff MASK_BITS _ _).mp hlook'
  exact ⟨a, b, hx, hy, hab⟩

/-! ### The cap-family WRITE keystones (`<slot>V3_non_amp` / `_forces_write`) — guarantee A closed.

Mirror of `attenuateV3_non_amp`: on an active cap-graph row of a `Satisfied2` witness of the ROTATED
cap-family descriptor, (1) the touched capability IS authenticated against the before cap-root (the
membership READ — a forged held leaf is excluded by `opensTo_functional`), and (2) the post `cap_root`
is the GENUINE sorted WRITE of the conferred value at the touched key (`writesTo`, FUNCTIONAL under CR via
`writesTo_functional` — a forged `new_cap_root` is UNSAT). THIS is the close: the cap-tree WRITE the base
descriptor previously left to an off-row prover-supplied `SpineCommits` hypothesis is now FORCED on the
deployed wire from `Satisfied2 <slot>V3`. -/

/-- **`delegateV3_forces_write` — the delegate cap-tree INSERT is FORCED in-circuit.** On an active
delegate row of a `Satisfied2 delegateV3` witness: the held authority is membership-read against the
before cap-root, and the post `cap_root` is the GENUINE sorted insert of the conferred rights
(`param[KEEP_MASK]`) at the new edge key (`param[CAP_KEY]`). Forced from the deployed `insertWriteOp` —
NOT the opaque `param.CAP_DIGEST_NEW` move, NOT an off-row decode. -/
theorem delegateV3_forces_write (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hsat : Satisfied2 hash delegateV3 minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length)
    (hactive : (envAt t i).loc sel.GRANT_CAP = 1) :
    opensTo hash ((envAt t i).loc (beforeCapRootCol EFFECT_VM_WIDTH))
        ((envAt t i).loc (prmCol ANCHOR_KEY)) (some ((envAt t i).loc (prmCol ANCHOR_MASK)))
    ∧ writesTo hash ((envAt t i).loc (beforeCapRootCol EFFECT_VM_WIDTH))
        ((envAt t i).loc (prmCol CAP_KEY)) ((envAt t i).loc (prmCol KEEP_MASK))
        ((envAt t i).loc (afterCapRootCol EFFECT_VM_WIDTH)) := by
  have hrowc := hsat.rowConstraints i hi
  have hmem : ∀ c ∈ ([.mapOp (anchorReadOpRot sel.GRANT_CAP),
      .mapOp (insertWriteOpRot sel.GRANT_CAP)] : List VmConstraint2),
      c ∈ delegateV3.constraints := fun c hc => List.mem_append_right _ hc
  have hread := hrowc (.mapOp (anchorReadOpRot sel.GRANT_CAP)) (hmem _ (by simp))
  have hwrite := hrowc (.mapOp (insertWriteOpRot sel.GRANT_CAP)) (hmem _ (by simp))
  exact ⟨(hread hactive).1, hwrite hactive⟩

/-- **`grantCapWriteV3_forces_write` — the bare grant cap-tree INSERT is FORCED in-circuit.** As
`delegateV3_forces_write`, over `grantCapWriteV3` (the deployed grantCap base + the cap-crown write
leg). -/
theorem grantCapWriteV3_forces_write (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hsat : Satisfied2 hash grantCapWriteV3 minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length)
    (hactive : (envAt t i).loc sel.GRANT_CAP = 1) :
    opensTo hash ((envAt t i).loc (beforeCapRootCol EFFECT_VM_WIDTH))
        ((envAt t i).loc (prmCol ANCHOR_KEY)) (some ((envAt t i).loc (prmCol ANCHOR_MASK)))
    ∧ writesTo hash ((envAt t i).loc (beforeCapRootCol EFFECT_VM_WIDTH))
        ((envAt t i).loc (prmCol CAP_KEY)) ((envAt t i).loc (prmCol KEEP_MASK))
        ((envAt t i).loc (afterCapRootCol EFFECT_VM_WIDTH)) := by
  have hrowc := hsat.rowConstraints i hi
  have hmem : ∀ c ∈ ([.mapOp (anchorReadOpRot sel.GRANT_CAP),
      .mapOp (insertWriteOpRot sel.GRANT_CAP)] : List VmConstraint2),
      c ∈ grantCapWriteV3.constraints := fun c hc => List.mem_append_right _ hc
  have hread := hrowc (.mapOp (anchorReadOpRot sel.GRANT_CAP)) (hmem _ (by simp))
  have hwrite := hrowc (.mapOp (insertWriteOpRot sel.GRANT_CAP)) (hmem _ (by simp))
  exact ⟨(hread hactive).1, hwrite hactive⟩

/-- **`delegateAttenV3_non_amp` — the delegateAtten cap-tree INSERT is FORCED in-circuit + non-amp.** As
`delegateV3_forces_write` PLUS the `granted ⊑ held` bitwise submask tooth (the attenuated grant cannot
amplify): the conferred rights `param[KEEP_MASK] ⊑ param[HELD_MASK]`. The post `cap_root` is the genuine
sorted insert of the attenuated grant. -/
theorem delegateAttenV3_non_amp (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hsub : t.tf (.custom SUBMASK_TID) = subsetTable MASK_BITS)
    (hsat : Satisfied2 hash delegateAttenV3 minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length)
    (hactive : (envAt t i).loc sel.GRANT_CAP = 1) :
    opensTo hash ((envAt t i).loc (beforeCapRootCol EFFECT_VM_WIDTH))
        ((envAt t i).loc (prmCol ANCHOR_KEY)) (some ((envAt t i).loc (prmCol ANCHOR_MASK)))
    ∧ writesTo hash ((envAt t i).loc (beforeCapRootCol EFFECT_VM_WIDTH))
        ((envAt t i).loc (prmCol CAP_KEY)) ((envAt t i).loc (prmCol KEEP_MASK))
        ((envAt t i).loc (afterCapRootCol EFFECT_VM_WIDTH))
    ∧ ∃ a b : Nat, (envAt t i).loc (prmCol KEEP_MASK) = (a : ℤ)
        ∧ (envAt t i).loc (prmCol HELD_MASK) = (b : ℤ) ∧ a &&& b = a := by
  have hrowc := hsat.rowConstraints i hi
  have hmem : ∀ c ∈ ([.mapOp (anchorReadOpRot sel.GRANT_CAP),
      .mapOp (insertWriteOpRot sel.GRANT_CAP), .lookup submaskLookup] :
      List VmConstraint2), c ∈ delegateAttenV3.constraints :=
    fun c hc => List.mem_append_right _ hc
  have hread := hrowc (.mapOp (anchorReadOpRot sel.GRANT_CAP)) (hmem _ (by simp))
  have hwrite := hrowc (.mapOp (insertWriteOpRot sel.GRANT_CAP)) (hmem _ (by simp))
  have hlook := hrowc (.lookup submaskLookup) (hmem _ (by simp))
  refine ⟨(hread hactive).1, hwrite hactive, ?_⟩
  have hlook' : [(envAt t i).loc (prmCol KEEP_MASK), (envAt t i).loc (prmCol HELD_MASK)]
      ∈ t.tf (.custom SUBMASK_TID) := hlook
  rw [hsub] at hlook'
  obtain ⟨a, b, _, _, hab, hx, hy⟩ := (subsetTable_mem_iff MASK_BITS _ _).mp hlook'
  exact ⟨a, b, hx, hy, hab⟩

/-- **`introduceWriteV3_forces_write` — the introduce cap-tree INSERT is FORCED in-circuit (frozen-face
close).** On an active cap-graph row of a `Satisfied2 introduceWriteV3` witness: the held authority is
membership-read against the before cap-root, and the post `cap_root` is the GENUINE sorted insert of the
conferred rights (`param[KEEP_MASK]`) at the new edge key (`param[CAP_KEY]`). Forced from the deployed
`insertWriteOp` on the MOVING `introduceVmDescriptorGenuine` face — the v1-face `gCapPass` freeze that left
this OFF-row is GONE. -/
theorem introduceWriteV3_forces_write (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hsat : Satisfied2 hash introduceWriteV3 minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length)
    (hactive : (envAt t i).loc sel.INTRODUCE = 1) :
    opensTo hash ((envAt t i).loc (beforeCapRootCol EFFECT_VM_WIDTH))
        ((envAt t i).loc (prmCol ANCHOR_KEY)) (some ((envAt t i).loc (prmCol ANCHOR_MASK)))
    ∧ writesTo hash ((envAt t i).loc (beforeCapRootCol EFFECT_VM_WIDTH))
        ((envAt t i).loc (prmCol CAP_KEY)) ((envAt t i).loc (prmCol KEEP_MASK))
        ((envAt t i).loc (afterCapRootCol EFFECT_VM_WIDTH)) := by
  have hrowc := hsat.rowConstraints i hi
  have hmem : ∀ c ∈ ([.mapOp (anchorReadOpRot sel.INTRODUCE),
      .mapOp (insertWriteOpRot sel.INTRODUCE)] : List VmConstraint2),
      c ∈ introduceWriteV3.constraints := fun c hc => List.mem_append_right _ hc
  have hread := hrowc (.mapOp (anchorReadOpRot sel.INTRODUCE)) (hmem _ (by simp))
  have hwrite := hrowc (.mapOp (insertWriteOpRot sel.INTRODUCE)) (hmem _ (by simp))
  exact ⟨(hread hactive).1, hwrite hactive⟩

/-- **`revokeDelegationWriteV3_forces_write` — the revokeDelegation cap-tree REMOVE is FORCED in-circuit
(frozen-face close).** On an active cap-graph row of a `Satisfied2 revokeDelegationWriteV3` witness: the
held authority is membership-read, and the post `cap_root` is the GENUINE sorted REMOVE (the ZERO sentinel
write) at the revoked edge key (`param[CAP_KEY]`). Forced from the deployed `removeWriteOp` on the MOVING
`revokeVmDescriptorGenuine` face — the v1-face `gCapPass` freeze is GONE. NO submask (revoke deletes a slot;
non-amplification is structural — the ZERO write is below any held mask). -/
theorem revokeDelegationWriteV3_forces_write (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hsat : Satisfied2 hash revokeDelegationWriteV3 minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length)
    (hactive : (envAt t i).loc sel.REVOKE_DELEGATION = 1) :
    opensTo hash ((envAt t i).loc (beforeCapRootCol EFFECT_VM_WIDTH))
        ((envAt t i).loc (prmCol CAP_KEY)) (some ((envAt t i).loc (prmCol HELD_MASK)))
    ∧ writesTo hash ((envAt t i).loc (beforeCapRootCol EFFECT_VM_WIDTH))
        ((envAt t i).loc (prmCol CAP_KEY)) 0
        ((envAt t i).loc (afterCapRootCol EFFECT_VM_WIDTH)) := by
  have hrowc := hsat.rowConstraints i hi
  have hmem : ∀ c ∈ ([.mapOp (heldReadOpRot sel.REVOKE_DELEGATION),
      .mapOp (removeWriteOpRot sel.REVOKE_DELEGATION),
      .base (epochBumpGate sel.REVOKE_DELEGATION
        (beforeEpochCol EFFECT_VM_WIDTH) (afterEpochCol EFFECT_VM_WIDTH))] : List VmConstraint2),
      c ∈ revokeDelegationWriteV3.constraints := fun c hc => List.mem_append_right _ hc
  have hread := hrowc (.mapOp (heldReadOpRot sel.REVOKE_DELEGATION)) (hmem _ (by simp))
  have hwrite := hrowc (.mapOp (removeWriteOpRot sel.REVOKE_DELEGATION)) (hmem _ (by simp))
  exact ⟨(hread hactive).1, hwrite hactive⟩

/-- **`revokeDelegationWriteV3_forces_epoch_bump` — the §14.EPOCH parent-epoch BUMP is FORCED in-circuit.**
On an active revoke row (`sel.REVOKE_DELEGATION = 1`, not the last row — pad rows follow) of a `Satisfied2
revokeDelegationWriteV3` witness: the committed AFTER `delegation_epoch` limb (`B_EPOCH = 30` of the AFTER
block) EQUALS the committed BEFORE epoch limb + 1. This is the deployed realization of the
`RevokeDelegationEpochResidual` `delegationEpoch += 1` clause — the freshness tick that stales every child
snapshot, no longer an off-row prover-supplied value. Forced from the deployed `epochBumpGate`. -/
theorem revokeDelegationWriteV3_forces_epoch_bump (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hsat : Satisfied2 hash revokeDelegationWriteV3 minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnl : (i + 1 == t.rows.length) = false)
    (hactive : (envAt t i).loc sel.REVOKE_DELEGATION = 1) :
    (envAt t i).loc (afterEpochCol EFFECT_VM_WIDTH)
      = (envAt t i).loc (beforeEpochCol EFFECT_VM_WIDTH) + 1 := by
  have hrowc := hsat.rowConstraints i hi
  have hmem : (VmConstraint2.base (epochBumpGate sel.REVOKE_DELEGATION
      (beforeEpochCol EFFECT_VM_WIDTH) (afterEpochCol EFFECT_VM_WIDTH)))
      ∈ revokeDelegationWriteV3.constraints :=
    List.mem_append_right _ (by simp)
  have hgate := hrowc _ hmem
  exact epochBumpGate_forces (envAt t i) (i == 0) (i + 1 == t.rows.length) hnl
    sel.REVOKE_DELEGATION (beforeEpochCol EFFECT_VM_WIDTH) (afterEpochCol EFFECT_VM_WIDTH)
    hactive hgate

/-- **TOOTH — `revokeDelegationWriteV3_rejects_wrong_epoch`.** A revoke trace whose committed AFTER epoch
is NOT the genuine BEFORE + 1 (a frozen epoch — `after = before`, the freshness-forgery that leaves stale
children looking current — or any wrong bump) does NOT satisfy `revokeDelegationWriteV3` on an active,
non-last row: UNSAT for a ledgerless client, no anchor. The deployed rejection of the
`RevokeDelegationEpochResidual` forgery. -/
theorem revokeDelegationWriteV3_rejects_wrong_epoch (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (i : Nat) (hi : i < t.rows.length) (hnl : (i + 1 == t.rows.length) = false)
    (hactive : (envAt t i).loc sel.REVOKE_DELEGATION = 1)
    (hwrong : (envAt t i).loc (afterEpochCol EFFECT_VM_WIDTH)
      ≠ (envAt t i).loc (beforeEpochCol EFFECT_VM_WIDTH) + 1) :
    ¬ Satisfied2 hash revokeDelegationWriteV3 minit mfin maddrs t :=
  fun hsat => hwrong (revokeDelegationWriteV3_forces_epoch_bump hash minit mfin maddrs t hsat i hi hnl hactive)

/-- **`refreshDelegationWriteV3_forces_write` — the refreshDelegation DELEGATIONS-tree UPDATE is FORCED
in-circuit.** On an active cap-graph row of a `Satisfied2 refreshDelegationWriteV3` witness: the child's
present snapshot is membership-read against the before DELEG-root (the rotated cap-root limb), and the
post DELEG-root is the GENUINE sorted UPDATE-AT-KEY of the recomputed snapshot (`param[KEEP_MASK]`) at the
child key (`param[CAP_KEY]`). Forced from the deployed `delegUpdateWriteOpRot` on the MOVING genuine face —
the DELEG WRITE that was the `delegRoot_runtime_column_pending` supplied digest is now in-circuit-bound. -/
theorem refreshDelegationWriteV3_forces_write (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hsat : Satisfied2 hash refreshDelegationWriteV3 minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length)
    (hactive : (envAt t i).loc sel.REFRESH_DELEGATION = 1) :
    opensTo hash ((envAt t i).loc (beforeDelegRootCol EFFECT_VM_WIDTH))
        ((envAt t i).loc (prmCol CAP_KEY)) (some ((envAt t i).loc (prmCol HELD_MASK)))
    ∧ writesTo hash ((envAt t i).loc (beforeDelegRootCol EFFECT_VM_WIDTH))
        ((envAt t i).loc (prmCol CAP_KEY)) ((envAt t i).loc (prmCol KEEP_MASK))
        ((envAt t i).loc (afterDelegRootCol EFFECT_VM_WIDTH)) := by
  have hrowc := hsat.rowConstraints i hi
  have hmem : ∀ c ∈ ([.mapOp (delegReadOpRot sel.REFRESH_DELEGATION),
      .mapOp (delegUpdateWriteOpRot sel.REFRESH_DELEGATION)] : List VmConstraint2),
      c ∈ refreshDelegationWriteV3.constraints := fun c hc => List.mem_append_right _ hc
  have hread := hrowc (.mapOp (delegReadOpRot sel.REFRESH_DELEGATION)) (hmem _ (by simp))
  have hwrite := hrowc (.mapOp (delegUpdateWriteOpRot sel.REFRESH_DELEGATION)) (hmem _ (by simp))
  exact ⟨(hread hactive).1, hwrite hactive⟩

/-- The rotated Custom declares EXACTLY the one proof-binding op (the rotated graduation
contributes none; the extras add exactly `customProofBind`). -/
theorem proofBindsOf_customV3 : proofBindsOf customV3 = [customProofBind] := by
  have hbase : proofBindsOf (v3Of customV1Face) = [] := proofBindsOf_graduateV1 (rotateV3 customV1Face)
  unfold proofBindsOf at hbase ⊢
  -- `customV3.constraints = ((v3Of …).constraints ++ [proofBind customProofBind]) ++ customPiExposure`;
  -- the eight `customPiExposure` pins are all `.base (.piBinding …)`, contributing no proof-binds.
  show (((v3Of customV1Face).constraints ++ [VmConstraint2.proofBind customProofBind])
      ++ customPiExposure).filterMap _ = _
  rw [List.filterMap_append, List.filterMap_append, hbase]
  rfl

/-- **The rotated cap-crown analog for Custom** — `customV2_binds_proof`, transported: on an active
Custom row of a `Satisfied2Custom` witness of the ROTATED Custom, the row's
`custom_proof_commitment` is the public-input commitment of a VERIFYING external sub-proof and its
`custom_program_vk_hash` is that proof's program VK. -/
theorem customV3_binds_proof (hash : List ℤ → ℤ)
    (E : Dregg2.Circuit.DescriptorIR2.ProofEngine)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hsat : Satisfied2Custom hash E customV3 minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length)
    (hactive : (envAt t i).loc SEL_CUSTOM = 1) :
    E.boundTo ((envAt t i).loc (prmCol CUSTOM_COMMIT)) ((envAt t i).loc (prmCol CUSTOM_VK)) := by
  have hm : customProofBind ∈ proofBindsOf customV3 := by
    rw [proofBindsOf_customV3]; exact List.mem_cons_self
  have := proofBind_bound hash E customV3 hsat hm i hi (by simpa [customProofBind] using hactive)
  simpa [customProofBind] using this

#assert_axioms setFieldDynV3_memLog
#assert_axioms setFieldDynV3_readback_genuine
#assert_axioms attenuateV3_non_amp
#assert_axioms delegateV3_forces_write
#assert_axioms grantCapWriteV3_forces_write
#assert_axioms delegateAttenV3_non_amp
#assert_axioms introduceWriteV3_forces_write
#assert_axioms revokeDelegationWriteV3_forces_write
#assert_axioms revokeDelegationWriteV3_forces_epoch_bump
#assert_axioms revokeDelegationWriteV3_rejects_wrong_epoch
#assert_axioms epochBumpGate_forces
#assert_axioms refreshDelegationWriteV3_forces_write
#assert_axioms proofBindsOf_customV3
#assert_axioms customV3_binds_proof
#assert_axioms noteSpendV3_grow_gate_forces_set_insert

-- NON-VACUITY of the bound block, executable (Horner toy sponge): moving the heap-root limb
-- (offset 27) or the iroot moves the chained commitment the appendix pins.
#guard wireCommitR refSponge ((List.range 31).map (fun i => (300 + i : ℤ))) 7
  != wireCommitR refSponge (((List.range 31).map (fun i => (300 + i : ℤ))).set 27 999) 7
#guard wireCommitR refSponge ((List.range 31).map (fun i => (300 + i : ℤ))) 7
  != wireCommitR refSponge ((List.range 31).map (fun i => (300 + i : ℤ))) 8

end Dregg2.Circuit.Emit.EffectVmEmitRotationV3
