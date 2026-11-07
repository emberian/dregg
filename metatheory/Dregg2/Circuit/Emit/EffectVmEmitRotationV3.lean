/-
# Dregg2.Circuit.Emit.EffectVmEmitRotationV3 — THE FULL-COHORT REGEN at the rotated block
(R = 24, CONFIRMED), staged.

`.docs-history-noclaude/ROTATION-CUTOVER.md` §5 item 1: the staged probes pin the rotated SHAPE; the 26
per-effect descriptors still emit against the 186/14 layout. THIS module re-emits EVERY
cohort member against the rotated 25+…-limb state block — as ONE parametric transformation
(`rotateV3`), so the soundness keystones lift ONCE, for all 26, not per-descriptor:

  * **§1 the appended geometry** — each rotated descriptor carries, PAST its v1 layout
    (every v1 column index, constraint, and theorem untouched): a rotated BEFORE block at
    `d.traceWidth` (187 absorption-ordered limbs · iroot · state_commit · 62 chain carriers
    = 251 columns = `B_SPAN`, the R=24 register geometry PLUS the `commitments_root` +
    `lifecycle_disc` + `perms_digest` + `vk_digest` + `mode` + `fields_root` limbs, the v11/v12
    completion octets, the v14 fields[0..7] completion NONET, and the v15 carrier-octet NONET
    lanes), a rotated AFTER block at
    `d.traceWidth + B_SPAN`, and the WIDENED-CAVEAT region at `d.traceWidth + 2·B_SPAN`
    (29-felt manifest · 9 chain carriers · caveat commit · 4 DFA rc felts + the rc fold = 45
    columns), and — 2026-07-31 — the FIELDS-CANONICITY region at `d.traceWidth + CANON9_REGION_OFF`
    (2 blocks × 8 slots × 7 aux columns = 112, the witness columns `Canonical9`'s `NoWrap` leg needs).
    Width: `+APPENDIX_SPAN = +659`.

    ⚑ **FLAG DAY 2026-07-31 (178 → 184).** `rotatedNumPreLimbs` grew by six so every `fields[j]`
    gets a NINTH lane (`Dregg2.Circuit.FieldLanes9` — eight lanes carry 247.26 bits against a
    32-byte field's 256, so no 8-lane encoding is injective, pigeonhole). NOTHING SHIFTED: the two
    free pads 176/177 plus the new columns 178..183 became the eight ninth lanes, and every column
    meaningful at 178 still means the same thing. `B_SPAN` 239 → 247, `2·B_SPAN` 478 → 494,
    `APPENDIX_SPAN` 521 → 537, the chained absorption 59 → 61 carriers (60 → 62 sites per block,
    130 → 134 appendix sites), and the setField VALUE8 pins 7 → 8 per slot (piCount 46 → 47 bare,
    50 → 51 after the rc wrap; those two were 53 → 54 / 57 → 58 before the 2026-08-07 seven-slot
    PI compaction took `V1_PI_COUNT` 42 → 35). Re-emit: every v3 descriptor, both Rust producers, the staged
    registry TSV, and every VK.

    ⚑⚑ **FLAG DAY 2026-08-01 (184 → 187) — THE KEY NONET, AND THIS ONE MOVES COLUMNS.** The same
    pigeonhole at the three CARRIER OCTETS (`child_vk` 89, `contract_hash` 97, `public_key` 105).
    The deployed `canonical_32_to_felts_8` packs 32 bytes into eight lanes at `8+8+8+6 = 30` bits
    and DROPS bits 6-7 of bytes 3, 7, …, 31 — sixteen source bits — so it is not injective
    trivially; and among valid Ed25519 keys the collision cost is ZERO, because bit 7 of byte 31 is
    the SIGN BIT and lies in the unread set (a key and its negation pack to one octet, and the
    negation is a keypair the attacker holds). `Dregg2.Circuit.KeyLanes9.keyToLanes9` is the
    base-`2^29` nonet that closes it, and `Emit.KeyCanonicity9Emit` emits its envelope.
    `rotatedNumPreLimbs` grows to **187, not 185**: `B_SPAN`'s `(n − 4)/3` is FLOOR division while
    `chunk31`'s `chunkCount` rounds up, so they agree only on `n ≡ 1 (mod 3)`; at 185 the block is
    silently one carrier column short. Columns 184/185/186 are the three ninth lanes and every
    column `0..183` keeps its meaning — but the ABSORPTION TAIL MOVES: `B_IROOT` 184 → 187,
    `B_STATE_COMMIT` 185 → 188, the chain band `186..246` → `189..250` (61 → 62 carriers, 62 → 63
    sites per block, 136 → 138 appendix sites), `B_SPAN` 247 → 251, `2·B_SPAN` 494 → 502,
    `CANON9_REGION_OFF` 539 → 547, `APPENDIX_SPAN` 651 → 659. Every `state_commit` therefore
    changes: this one is a **RE-GENESIS**, not just a VK rotation. Re-emit: every v3 descriptor,
    both Rust producers, `layout_generated.rs`, the staged registry TSVs, every VK, and bump
    `persist`'s `CANONICAL_STATE_SCHEMA_EPOCH` so a pre-flip image REFUSES TO LOAD rather than
    reinterpreting its limbs.
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
import Dregg2.Circuit.Emit.WireCommitBindsOrCollides
import Dregg2.Circuit.Emit.RotatedLayout
-- The mod-p gate-denotation toolkit (field-faithful `holdsVm ≡ 0 [ZMOD p]`): positive
-- glue `eqToModEq`/`gate_modEq_iff`, negative-tooth glue `not_modEq_zero_of_canon`. Transfer
-- imports only `EffectVmEmit`, already in this closure; no cycle.
import Dregg2.Circuit.Emit.EffectVmEmitTransfer
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
-- v10 faithful-8-felt cap-root: the native `node8` arity-16 tree (Digest8 root) the cap-write
-- column GROUP commits. ACYCLIC: DeployedCapTree's emit chain bottoms out at EffectVmEmitCapRoot →
-- EffectVmEmit, never reaching this Rotation layer.
import Dregg2.Circuit.DeployedCapTree
-- v10 faithful-8-felt HEAP-root: the native `node8` heap-tree carrier + recompose spine (the SECOND
-- faithful root, the exact twin of `DeployedCapTree`'s `Cap8Scheme`). ACYCLIC: `DeployedHeapTree`
-- imports only `DeployedCapTree` + `CapMerkleGeneric`, already in this layer's closure.
import Dregg2.Circuit.DeployedHeapTree
-- v10 faithful-8-felt FIELDS-root: the native `node8` user-field-map tree carrier + recompose spine
-- (the THIRD and LAST faithful root, the exact twin of `DeployedHeapTree`'s `Heap8Scheme`). ACYCLIC:
-- `DeployedFieldsTree` imports only `DeployedCapTree` + `CapMerkleGeneric`, already in this closure.
import Dregg2.Circuit.DeployedFieldsTree
import Dregg2.Crypto.RomMerkleOpening

namespace Dregg2.Circuit.Emit.EffectVmEmitRotationV3

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmitV2
open Dregg2.Circuit.Emit.EffectVmEmitRotationR
open Dregg2.Circuit.Emit.WireCommitBindsOrCollides (wireCommitR_binds_or_collides
  wireCommitRFind_spec wireCommitRColl_refutable_on_agreement WireColl1)
open Dregg2.Circuit.Emit.EffectVmEmitRotationCaveat
  (RotCaveatManifest caveatCommit caveatCommit_binds caveatCommitRc caveatCommitRc_binds)
open Dregg2.Circuit.Emit.EffectVmEmitTransfer
  (eqToModEq gate_modEq_iff not_modEq_zero_of_canon)
open Dregg2.Circuit.Emit.EffectVmEmitRotation (canon_eq_of_modEq)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Crypto
open Dregg2.Substrate.Heap (refSponge)
-- v10 faithful-8-felt cap-root: the native `node8` tree carrier + recompose spine.
open Dregg2.Circuit.DeployedCapTree (Digest8 Cap8Scheme CapLeaf Coll8)
open Dregg2.Circuit.DeployedCapTree.Cap8Scheme
  (recomposeUp8 capLeafDigest8 recomposeUp8Find recomposeUp8_binds_or_collides)
open Dregg2.Circuit.CapMerkleGeneric (StepG)
-- v10 faithful-8-felt HEAP-root: the native `node8` heap-tree carrier + recompose spine.
open Dregg2.Circuit.DeployedHeapTree (Heap8Scheme)
-- v10 faithful-8-felt FIELDS-root: the native `node8` user-field-map tree carrier + recompose spine.
open Dregg2.Circuit.DeployedFieldsTree (Fields8Scheme)

set_option linter.unusedVariables false
set_option autoImplicit false
-- The rotated appendix is 136 sites; the `rfl` reductions
-- over the widened `rotateV3` structure need more kernel recursion depth.
set_option maxRecDepth 16000

/-! ## §1 — the appended geometry (R = 24, offsets relative to a block base). -/

/-- Project a named faithful-8 group lane from the verified layout. `Legal.groupCoverage` and
`Legal.groupWidth` make every lane total; `getD 0` stays only at this raw-data projection boundary. -/
def layoutGroupCol (name : GroupName) (i : Fin 8) : Nat :=
  (rotated196.groupCol name i).getD 0

-- ── THE MODE / FIELDS-ROOT AUTHORITY SUB-LIMBS ───────────────────────────────────────────────────
-- The rotated block carries two dedicated authority sub-limbs beside the opaque `record_digest`
-- (r23, limb 24): the committed cell `MODE` byte at in-block offset 35 (`B_MODE`, the
-- `Hosted=0 / Sovereign=1` byte `compute_authority_digest_felt` folds —
-- `rotation_witness.rs::mode_felt`) and the committed `fields_root` digest at offset 36
-- (`B_FIELDS_ROOT`, the overflow named-field map root the same digest folds —
-- `hash_bytes(cell.state.fields_root)`). They are what makes the per-effect movers LIVE:
-- makeSovereign FORCES the AFTER mode limb to `Sovereign(1)` as a CONSTANT (the disc shape, NO
-- trusted post-cell), and setFieldDyn / refusal WELD the AFTER fields_root sub-limb to the declared
-- post-`fields_root` param column (the perms/VK weld shape, declared-param anchored).
--
-- ⚑ The WAVE-3 narrative that used to sit here ("NUM_PRE_LIMBS 35→37 … block span 49→51 … the site
-- count stays 13") is DELETED, not updated: it described a geometry three flag days dead, and every
-- number in it was false at 178 already. The live extent is `rotatedNumPreLimbs` in
-- `RotatedLayout.lean` and the live chaining is `rotV3SitesAt` below — read those, never a comment.
-- The one structural fact that survives every bump: `chunk31` (`EffectVmEmitRotationR`) is
-- length-generic, so a limb-count change moves the literal site walk and NOTHING in the
-- chained-commitment binding.

/-- The current per-block span: 187 pre-iroot limbs, iroot, state_commit, and 62 chain carriers.
Derived from `rotatedNumPreLimbs` (the ONE verified source), never a hand-carried literal.

⚠ The `(n − 4) / 3` here is `Nat` FLOOR division and `chunk31`'s `chunkCount` rounds UP, so this
formula is only the true carrier count when `n ≡ 1 (mod 3)` — `Legal.bodyAligned`. The `#guard`
below pins it against the LITERAL `rotV3SitesAt` walk so a bump to an illegal extent fails here
rather than emitting a block one carrier column short. -/
def B_SPAN : Nat := rotatedNumPreLimbs + 3 + (rotatedNumPreLimbs - 4) / 3
/-- lifecycle-disc offset inside a block (limb 32 — the WAVE-1 flag-day committed discriminant limb,
committed BESIDE the opaque `lifecycle_felt` at 29; UNCHANGED by the perms/VK + mode/fields-root flag-days). -/
def B_DISC : Nat := 32
/-- committed-permissions digest offset inside a block (limb 33 — the WAVE-2 flag-day committed
perms-digest limb; the deployed `params[0]` felt for a setPermissions row, `= permsHash[0]`). -/
def B_PERMS : Nat := layoutGroupCol .perms 0
/-- committed-verification-key digest offset inside a block (limb 34 — the WAVE-2 flag-day committed
vk-digest limb; the deployed `params[0]` felt for a setVK row, `= vkHash[0]`). -/
def B_VK : Nat := layoutGroupCol .vk 0
/-- committed cell-MODE offset inside a block (limb 35 — the WAVE-3 flag-day committed mode byte,
`Hosted=0 / Sovereign=1`; the makeSovereign CONSTANT-force limb). -/
def B_MODE : Nat := 35
/-- committed `fields_root` digest offset inside a block (limb 36 — the WAVE-3 flag-day committed
overflow named-field map root; the setFieldDyn / refusal declared-param weld limb). -/
def B_FIELDS_ROOT : Nat := layoutGroupCol .fields 0
/-- committed `revoked_root` lane-0 offset inside a block (limb 37 — the REVOKED-ROOT flag-day NEW
base limb, right after `fields_root` at 36; the credential-revocation accumulator's openable
sorted-Poseidon2 root, lane 0 of the 8-felt `revokedRootGroupCol` whose completion limbs ride 82..88). -/
def B_REVOKED_ROOT : Nat := layoutGroupCol .revoked 0
/-- iroot offset inside a block: exactly past the verified pre-limb layout, absorbed ALONE last. -/
def B_IROOT : Nat := rotatedNumPreLimbs
/-- State-commit offset inside a block, immediately after iroot. -/
def B_STATE_COMMIT : Nat := B_IROOT + 1
/-- committed-height offset inside a block (limb 31, after the `commitments_root` shift — UNCHANGED
by the disc / perms-VK flag-days, which append PAST it). -/
def B_COMMITTED_HEIGHT : Nat := 31
/-- cap-root offset inside a block (unshifted — `commitments_root` rides AFTER nullifier_root). -/
def B_CAP_ROOT : Nat := layoutGroupCol .cap 0
/-- nullifier-root offset inside a block (unshifted, limb 26). -/
def B_NULLIFIER_ROOT_OFF : Nat := layoutGroupCol .nullifier 0
/-- commitments-root offset inside a block (limb 27 — the flag-day new committed shielded-set root). -/
def B_COMMITMENTS_ROOT : Nat := layoutGroupCol .commitments 0
/-- delegation-epoch offset inside a block (limb 30 — the committed per-cell `delegation_epoch`,
`commitment.rs::compute_rotated_pre_limbs` `pre[30]`; absorption order cells_root · r0..r23 · cap_root ·
nullifier_root · commitments_root · heap_root · lifecycle · **epoch** · committed_height). The forced
limb for `revokeDelegation`'s parent-epoch BUMP (the §14.EPOCH write-gate). -/
def B_EPOCH : Nat := 30
/-- The caveat region span: 29 manifest felts + 9 manifest-chain carriers + 1 manifest commit +
the 4-felt DFA route-commitment carrier (the dsl rc-EMIT — `C_RC_OFF`) + the 2 carriers that
absorb it + the FINAL caveat commit. ⚑ 43 → 45 at the rc-FOLD flag day. -/
def C_SPAN : Nat := 45
/-- The 29-limb MANIFEST fold's carrier, inside the caveat region — the `caveatCommit` digest.
⚑ This is an INTERMEDIATE now: it is the accumulator the rc extension chains off, not the
published caveat commitment. What is pinned to PI is `C_COMMIT` (45-span flag day). -/
def C_MANIFEST_COMMIT : Nat := 38
/-- In-region base of the 4-felt DFA ROUTE-COMMITMENT carrier (offsets 39..42, past the MANIFEST
fold's carrier at 38). Carries `custom_proof_pi_commitment(DfaProofWire.public_inputs)` — the
4-felt fold-bound anchor of a `Witnessed{Dfa}` caveat's DSL-circuit STARK (the SAME derivation as
the custom carrier's `custom_proof_commitment`, term-for-term) — on a Dfa-gated turn, ZERO on every
other turn (the absent sentinel; the region is producer-filled uniformly on every row). Rust twin
`trace_rotated::C_DFA_RC_OFF`. Published as 4 TAIL PIs by `withDfaRcPins`.

⚑ **The rc-FOLD flag day.** These four columns used to be read by NOTHING: the `caveatCommit` fold
stopped at the manifest and the `withDfaRcPins` pins were `local[c] == pi[k]` with the prover
choosing both sides, so `UnforcedPiPins.dropUnforcedPins` deleted them (correctly — they were 144
of the 159) and the `CarrierWitness::Dsl` fold, which locates its slot BY that pin, refused every
deployed leg. They are now ABSORBED (`caveatV3SitesAt`'s two new sites → `caveatCommitRc`), so a
non-pin constraint with a row denotation reads them, they are in `UnforcedPiPins.forcedCols`, and
the pins survive the subtraction ON THEIR OWN MERITS. -/
def C_RC_OFF : Nat := 39
/-- The rc extension's FIRST carrier: `hash [manifest commit, rc0, rc1, rc2]` (arity 4). -/
def C_RC_CARRIER : Nat := 43
/-- **The published caveat commitment** — `hash [rc carrier, rc3]` (arity 2), i.e.
`caveatCommitRc` of the row's manifest AND its route-commitment carrier. THIS is the column
`rotPins` pins to PI `piBase + 3`. ⚑ 38 → 44 at the rc-FOLD flag day. -/
def C_COMMIT : Nat := 44
/-- **The FIELDS-CANONICITY region's in-appendix base** — past both rotated blocks and the caveat
region. It carries the seven aux columns per `(block, slot)` that make `Canonical9`'s third leg
(`NoWrap`) expressible: `r, q0, q1, v0, v0b, v1, v1b`. See `Emit.FieldsCanonicity9Emit`. -/
def CANON9_REGION_OFF : Nat := 2 * B_SPAN + C_SPAN

/-- **The fields-canonicity region's span**: 2 blocks × 8 slots × 7 aux columns.

⚑ **FLAG DAY 2026-07-31 (APPENDIX_SPAN 539 → 651).** `FieldLanes9.canonical9_iff_in_image` proves
`Canonical9` is EXACTLY the nine-lane encoder's image, and its third leg `NoWrap` is **not a range
check on any lane** — it is a joint condition on lane 0, lane 1 and lane 8's top nibble. Expressing
it needs witness columns, and they ride here.

The region sits PAST both blocks and the caveat region, so **that** flag day left the pre-limb
geometry and the absorption chain untouched — a descriptor re-emit and a VK rotation, not a
re-genesis. ⚑ The 2026-08-01 KEY-nonet flag day is the opposite case and must not be read through
this paragraph: it grows `rotatedNumPreLimbs` itself (184 → 187), so `B_SPAN` 247 → 251, this
region's base 539 → 547, every chain carrier moves, and every `state_commit` changes. That one IS a
re-genesis (bump `CANONICAL_STATE_SCHEMA_EPOCH`; the constant is in `persist/src/lib.rs` and this
docstring deliberately does not restate its value).

112 is a multiple of `CHIP_OUT_LANES - 1 = 7`, so the registry's `(traceWidth - base) % 7 == 0`
width discipline survives verbatim. -/
def CANON9_SPAN : Nat := 2 * 8 * 7

/-- The whole appendix width: two rotated blocks, the caveat region, and the fields-canonicity
region. -/
def APPENDIX_SPAN : Nat := CANON9_REGION_OFF + CANON9_SPAN

/-- The rotated CAVEAT-region base offset (past the v1 layout + the two rotated blocks). Defined
HERE, beside the other span constants, so every consumer in this file names it instead of carrying
`478`/`494` — the bare-literal drift class the 178 → 184 flag day paid for. -/
def CAVEAT_REGION_OFF : Nat := 2 * B_SPAN

-- The map-root offsets ride past the R=24 probe's named columns (cap_root at probe `capRootCol 24`);
-- the `commitments_root` limb is the +1 over the bare R=24 register shape.
#guard B_CAP_ROOT == capRootCol 24
#guard B_COMMITMENTS_ROOT == B_NULLIFIER_ROOT_OFF + 1
#guard B_DISC == 32                  -- the WAVE-1 disc limb (after committed_height at 31)
#guard B_PERMS == 33                 -- WAVE-2 committed perms-digest limb
#guard B_VK == 34                    -- WAVE-2 committed vk-digest limb
#guard B_MODE == 35                  -- WAVE-3 committed mode byte limb
#guard B_FIELDS_ROOT == 36           -- WAVE-3 committed fields_root digest limb
#guard B_IROOT == 196                -- verified pre-iroot layout, then iroot (FLAG DAY: was 184)
#guard B_IROOT == rotated196.numPreLimbs
#guard B_STATE_COMMIT == B_IROOT + 1
#guard B_COMMITTED_HEIGHT == 31      -- last SCALAR pre-iroot limb (disc/perms/vk/mode/fields-root ride past it)
#guard B_SPAN == B_IROOT + 67        -- 196 pre-iroot + iroot + state_commit + 65 chain carriers = 263
#guard B_SPAN == 263
-- ⚑ THE COUNTING GATE THE KEY-NONET FLAG DAY EXISTS BECAUSE OF. `B_SPAN`'s `(n − 4)/3` is FLOOR
-- division; the real carrier chain is `chunk31`'s `chunkCount`, which rounds UP. They agree exactly
-- on `n ≡ 1 (mod 3)`. At n = 185 the formula says 60 carriers where the chain needs 61 and the block
-- is silently one column short — every other guard in this file would still have passed.
#guard rotatedNumPreLimbs % 3 == 1
#guard APPENDIX_SPAN == 2 * B_SPAN + C_SPAN + CANON9_SPAN
#guard CANON9_REGION_OFF == 571      -- 2·251 + 45: the canonicity aux ride PAST the caveat region
#guard CANON9_SPAN == 112            -- 2 blocks × 8 slots × 7 aux columns
#guard CANON9_SPAN % (CHIP_OUT_LANES - 1) == 0   -- the registry width discipline survives
#guard APPENDIX_SPAN == 683          -- 547 + 112 (was 651 at the 184-limb geometry)
#guard CAVEAT_REGION_OFF == 2 * B_SPAN
#guard CAVEAT_REGION_OFF == 526      -- was 494
#guard C_RC_OFF == C_MANIFEST_COMMIT + 1  -- the rc carrier rides PAST the manifest fold's digest
#guard C_RC_CARRIER == C_RC_OFF + 4       -- ...and the two absorbing carriers ride past IT
#guard C_COMMIT == C_RC_CARRIER + 1       -- the FINAL digest is the published caveat commitment
#guard C_SPAN == C_COMMIT + 1             -- which closes the region

/-- The pre-iroot limb list of a block at `base` — all `rotatedNumPreLimbs = 187` of them, in the
verified `rotated196` tiling order: cells_root · r0..r23 · cap_root · nullifier_root ·
commitments_root · heap_root · lifecycle · epoch · committed height · lifecycle_disc · perms_digest ·
vk_digest · **mode** · **fields_root** · revoked_root · the faithful-8-felt completion limbs · the
three carrier octets · the fields NONET lanes (`113..168` plus `176..183`) · and — 2026-08-01 — the
three CARRIER-OCTET ninth lanes `184` (child_vk), `185` (contract_hash) and `186` (**public_key**).
Literal, so every positional fact is `rfl`. ⚑ 184 → 187: the tail three entries are NEW columns;
every earlier entry names the column it always named.

⚑ **THIS LIST IS THE ANCHOR'S DOMAIN.** `wireCommitR` folds exactly these, so a lane that is not
here is a free felt `state_commit` never sees. That is why the owner key's ninth lane is limb 186
and not an appendix column — see `Emit.KeyCanonicity9Emit.lane8_is_absorbed_iff`. -/
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
  , a (base + 66), a (base + 67), a (base + 68), a (base + 69), a (base + 70), a (base + 71)
  , a (base + 72), a (base + 73), a (base + 74), a (base + 75), a (base + 76), a (base + 77)
  , a (base + 78), a (base + 79), a (base + 80), a (base + 81), a (base + 82), a (base + 83)
  , a (base + 84), a (base + 85), a (base + 86), a (base + 87), a (base + 88), a (base + 89)
  , a (base + 90), a (base + 91), a (base + 92), a (base + 93), a (base + 94), a (base + 95)
  , a (base + 96), a (base + 97), a (base + 98), a (base + 99), a (base + 100), a (base + 101)
  , a (base + 102), a (base + 103), a (base + 104), a (base + 105), a (base + 106), a (base + 107)
  , a (base + 108), a (base + 109), a (base + 110), a (base + 111), a (base + 112), a (base + 113)
  , a (base + 114), a (base + 115), a (base + 116), a (base + 117), a (base + 118), a (base + 119)
  , a (base + 120), a (base + 121), a (base + 122), a (base + 123), a (base + 124), a (base + 125)
  , a (base + 126), a (base + 127), a (base + 128), a (base + 129), a (base + 130), a (base + 131)
  , a (base + 132), a (base + 133), a (base + 134), a (base + 135), a (base + 136), a (base + 137)
  , a (base + 138), a (base + 139), a (base + 140), a (base + 141), a (base + 142), a (base + 143)
  , a (base + 144), a (base + 145), a (base + 146), a (base + 147), a (base + 148), a (base + 149)
  , a (base + 150), a (base + 151), a (base + 152), a (base + 153), a (base + 154), a (base + 155)
  , a (base + 156), a (base + 157), a (base + 158), a (base + 159), a (base + 160), a (base + 161)
  , a (base + 162), a (base + 163), a (base + 164), a (base + 165), a (base + 166), a (base + 167)
  , a (base + 168), a (base + 169), a (base + 170), a (base + 171), a (base + 172), a (base + 173)
  , a (base + 174), a (base + 175), a (base + 176), a (base + 177), a (base + 178), a (base + 179)
  , a (base + 180), a (base + 181), a (base + 182), a (base + 183), a (base + 184), a (base + 185)
  , a (base + 186), a (base + 187), a (base + 188), a (base + 189), a (base + 190), a (base + 191)
  , a (base + 192), a (base + 193), a (base + 194), a (base + 195) ]

theorem preLimbsAt_length (base : Nat) (a : Assignment) :
    (preLimbsAt base a).length = 196 := rfl

/-- The literal limb list really is the verified layout's extent — the `#guard` that makes a future
`rotatedNumPreLimbs` bump fail HERE rather than silently emit a short block. -/
theorem preLimbsAt_length_eq_layout (base : Nat) (a : Assignment) :
    (preLimbsAt base a).length = rotatedNumPreLimbs := rfl

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

/-- Read the 4-felt DFA ROUTE-COMMITMENT carrier off a row at region base `base` (positional).
The list `caveatCommitRc` absorbs — so the columns the `withDfaRcPins` pins publish are exactly
the ones the published caveat commitment folds. -/
def rcAt (base : Nat) (a : Assignment) : List ℤ :=
  [a (base + C_RC_OFF), a (base + C_RC_OFF + 1), a (base + C_RC_OFF + 2), a (base + C_RC_OFF + 3)]

theorem rcAt_length (base : Nat) (a : Assignment) : (rcAt base a).length = 4 := rfl

/-! ## §2 — the col-chained sites (position-independent; graduate to the probe's bytes). -/

/-- The 63 chained absorption sites of a rotated block at `base` (v15): the 4-wide head over limbs
0..3, SIXTY-ONE 3-wide body groups (limbs 4..186 — the 183-limb body `[4..186]` is exactly sixty-one
3-wide groups, NO arity-2 leftover, which is why `Legal.bodyAligned` forces `(187-4) % 3 = 0`), then the
iroot ALONE last onto the state-commit carrier. Chaining is by CARRIER COLUMNS (`.col`), which
graduates to the SAME wire bytes as `.digest` chaining while keeping the group position-independent.
Chain carriers ride `base + 189 .. base + 250` (62 carriers); the state-commit carrier is
`base + 188` (`B_STATE_COMMIT`) and the iroot is `base + 187` (`B_IROOT`).

⚑ 184 → 187 moved ALL of that: the band was `186..246`, state_commit was 185 and iroot 184. The
178 → 184 flag day left ONE hand-written Rust mirror of `B_CHAIN_BASE` behind at 180 and the
producer then wrote chain digests over four pre-limbs, the iroot and state_commit — every rotated
member UNSAT. `EmitLayoutManifest` now reads `bChainBase` off this list's FIRST site rather than
restating it; the same is required of every consumer. -/
def rotV3SitesAt (base : Nat) : List VmHashSite :=
  [ ⟨base + 198, [.col (base + 0), .col (base + 1), .col (base + 2), .col (base + 3)], 4⟩
  , ⟨base + 199, [.col (base + 198), .col (base + 4), .col (base + 5), .col (base + 6)], 4⟩
  , ⟨base + 200, [.col (base + 199), .col (base + 7), .col (base + 8), .col (base + 9)], 4⟩
  , ⟨base + 201, [.col (base + 200), .col (base + 10), .col (base + 11), .col (base + 12)], 4⟩
  , ⟨base + 202, [.col (base + 201), .col (base + 13), .col (base + 14), .col (base + 15)], 4⟩
  , ⟨base + 203, [.col (base + 202), .col (base + 16), .col (base + 17), .col (base + 18)], 4⟩
  , ⟨base + 204, [.col (base + 203), .col (base + 19), .col (base + 20), .col (base + 21)], 4⟩
  , ⟨base + 205, [.col (base + 204), .col (base + 22), .col (base + 23), .col (base + 24)], 4⟩
  , ⟨base + 206, [.col (base + 205), .col (base + 25), .col (base + 26), .col (base + 27)], 4⟩
  , ⟨base + 207, [.col (base + 206), .col (base + 28), .col (base + 29), .col (base + 30)], 4⟩
  , ⟨base + 208, [.col (base + 207), .col (base + 31), .col (base + 32), .col (base + 33)], 4⟩
  , ⟨base + 209, [.col (base + 208), .col (base + 34), .col (base + 35), .col (base + 36)], 4⟩
  , ⟨base + 210, [.col (base + 209), .col (base + 37), .col (base + 38), .col (base + 39)], 4⟩
  , ⟨base + 211, [.col (base + 210), .col (base + 40), .col (base + 41), .col (base + 42)], 4⟩
  , ⟨base + 212, [.col (base + 211), .col (base + 43), .col (base + 44), .col (base + 45)], 4⟩
  , ⟨base + 213, [.col (base + 212), .col (base + 46), .col (base + 47), .col (base + 48)], 4⟩
  , ⟨base + 214, [.col (base + 213), .col (base + 49), .col (base + 50), .col (base + 51)], 4⟩
  , ⟨base + 215, [.col (base + 214), .col (base + 52), .col (base + 53), .col (base + 54)], 4⟩
  , ⟨base + 216, [.col (base + 215), .col (base + 55), .col (base + 56), .col (base + 57)], 4⟩
  , ⟨base + 217, [.col (base + 216), .col (base + 58), .col (base + 59), .col (base + 60)], 4⟩
  , ⟨base + 218, [.col (base + 217), .col (base + 61), .col (base + 62), .col (base + 63)], 4⟩
  , ⟨base + 219, [.col (base + 218), .col (base + 64), .col (base + 65), .col (base + 66)], 4⟩
  , ⟨base + 220, [.col (base + 219), .col (base + 67), .col (base + 68), .col (base + 69)], 4⟩
  , ⟨base + 221, [.col (base + 220), .col (base + 70), .col (base + 71), .col (base + 72)], 4⟩
  , ⟨base + 222, [.col (base + 221), .col (base + 73), .col (base + 74), .col (base + 75)], 4⟩
  , ⟨base + 223, [.col (base + 222), .col (base + 76), .col (base + 77), .col (base + 78)], 4⟩
  , ⟨base + 224, [.col (base + 223), .col (base + 79), .col (base + 80), .col (base + 81)], 4⟩
  , ⟨base + 225, [.col (base + 224), .col (base + 82), .col (base + 83), .col (base + 84)], 4⟩
  , ⟨base + 226, [.col (base + 225), .col (base + 85), .col (base + 86), .col (base + 87)], 4⟩
  , ⟨base + 227, [.col (base + 226), .col (base + 88), .col (base + 89), .col (base + 90)], 4⟩
  , ⟨base + 228, [.col (base + 227), .col (base + 91), .col (base + 92), .col (base + 93)], 4⟩
  , ⟨base + 229, [.col (base + 228), .col (base + 94), .col (base + 95), .col (base + 96)], 4⟩
  , ⟨base + 230, [.col (base + 229), .col (base + 97), .col (base + 98), .col (base + 99)], 4⟩
  , ⟨base + 231, [.col (base + 230), .col (base + 100), .col (base + 101), .col (base + 102)], 4⟩
  , ⟨base + 232, [.col (base + 231), .col (base + 103), .col (base + 104), .col (base + 105)], 4⟩
  , ⟨base + 233, [.col (base + 232), .col (base + 106), .col (base + 107), .col (base + 108)], 4⟩
  , ⟨base + 234, [.col (base + 233), .col (base + 109), .col (base + 110), .col (base + 111)], 4⟩
  , ⟨base + 235, [.col (base + 234), .col (base + 112), .col (base + 113), .col (base + 114)], 4⟩
  , ⟨base + 236, [.col (base + 235), .col (base + 115), .col (base + 116), .col (base + 117)], 4⟩
  , ⟨base + 237, [.col (base + 236), .col (base + 118), .col (base + 119), .col (base + 120)], 4⟩
  , ⟨base + 238, [.col (base + 237), .col (base + 121), .col (base + 122), .col (base + 123)], 4⟩
  , ⟨base + 239, [.col (base + 238), .col (base + 124), .col (base + 125), .col (base + 126)], 4⟩
  , ⟨base + 240, [.col (base + 239), .col (base + 127), .col (base + 128), .col (base + 129)], 4⟩
  , ⟨base + 241, [.col (base + 240), .col (base + 130), .col (base + 131), .col (base + 132)], 4⟩
  , ⟨base + 242, [.col (base + 241), .col (base + 133), .col (base + 134), .col (base + 135)], 4⟩
  , ⟨base + 243, [.col (base + 242), .col (base + 136), .col (base + 137), .col (base + 138)], 4⟩
  , ⟨base + 244, [.col (base + 243), .col (base + 139), .col (base + 140), .col (base + 141)], 4⟩
  , ⟨base + 245, [.col (base + 244), .col (base + 142), .col (base + 143), .col (base + 144)], 4⟩
  , ⟨base + 246, [.col (base + 245), .col (base + 145), .col (base + 146), .col (base + 147)], 4⟩
  , ⟨base + 247, [.col (base + 246), .col (base + 148), .col (base + 149), .col (base + 150)], 4⟩
  , ⟨base + 248, [.col (base + 247), .col (base + 151), .col (base + 152), .col (base + 153)], 4⟩
  , ⟨base + 249, [.col (base + 248), .col (base + 154), .col (base + 155), .col (base + 156)], 4⟩
  , ⟨base + 250, [.col (base + 249), .col (base + 157), .col (base + 158), .col (base + 159)], 4⟩
  , ⟨base + 251, [.col (base + 250), .col (base + 160), .col (base + 161), .col (base + 162)], 4⟩
  , ⟨base + 252, [.col (base + 251), .col (base + 163), .col (base + 164), .col (base + 165)], 4⟩
  , ⟨base + 253, [.col (base + 252), .col (base + 166), .col (base + 167), .col (base + 168)], 4⟩
  , ⟨base + 254, [.col (base + 253), .col (base + 169), .col (base + 170), .col (base + 171)], 4⟩
  , ⟨base + 255, [.col (base + 254), .col (base + 172), .col (base + 173), .col (base + 174)], 4⟩
  , ⟨base + 256, [.col (base + 255), .col (base + 175), .col (base + 176), .col (base + 177)], 4⟩
  , ⟨base + 257, [.col (base + 256), .col (base + 178), .col (base + 179), .col (base + 180)], 4⟩
  , ⟨base + 258, [.col (base + 257), .col (base + 181), .col (base + 182), .col (base + 183)], 4⟩
  , ⟨base + 259, [.col (base + 258), .col (base + 184), .col (base + 185), .col (base + 186)], 4⟩
  , ⟨base + 260, [.col (base + 259), .col (base + 187), .col (base + 188), .col (base + 189)], 4⟩
  , ⟨base + 261, [.col (base + 260), .col (base + 190), .col (base + 191), .col (base + 192)], 4⟩
  , ⟨base + 262, [.col (base + 261), .col (base + 193), .col (base + 194), .col (base + 195)], 4⟩
  , ⟨base + 197, [.col (base + 262), .col (base + 196)], 2⟩ ]

/-- **Every rotated absorption site asks the chip for an ADMITTED arity, at EVERY base.** The list
above is a literal spine of 4-input sites with a terminal 2-input site, so the arity is independent
of `base` — which is what makes this a fact about the FAMILY rather than about one instantiation.
`graduateV1` now takes the admission as a construction obligation, and this is the discharge every
rotated graduation and the S2 compaction rides. -/
theorem rotV3SitesAt_admitted (base : Nat) :
    ∀ s ∈ rotV3SitesAt base, ChipArityAdmitted s.inputs.length :=
  of_decide_eq_true (Eq.refl true)

#assert_axioms rotV3SitesAt_admitted

/-- The 12 chained caveat sites at region base `base` (the `caveatSites` shape, positional):
4-wide head over `[count, e0.tag, e0.dom, e0.key]`, eight (carrier+3) body groups, the
(carrier+1) tail onto the MANIFEST-commit carrier — then the rc EXTENSION, two further sites
absorbing the 4-felt DFA route-commitment carrier onto the PUBLISHED caveat commit
(`chunk31 [rc0,rc1,rc2,rc3] = [[rc0,rc1,rc2],[rc3]]`, so arity 4 then arity 2 — never the
chip-refused 3). ⚑ THE rc-FOLD FLAG DAY: the last two sites are new, and they are what makes the
rc columns FORCED rather than merely published. -/
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
  , ⟨base + 38, [.col (base + 37), .col (base + 28)], 2⟩
  -- THE rc EXTENSION (the two sites that force the DFA route-commitment carrier):
  , ⟨base + 43, [.col (base + 38), .col (base + 39), .col (base + 40), .col (base + 41)], 4⟩
  , ⟨base + 44, [.col (base + 43), .col (base + 42)], 2⟩ ]

/-- The whole appendix site group for a descriptor of width `w`. The AFTER block rides at
`w + B_SPAN`; the caveat region at `w + CAVEAT_REGION_OFF` (`= 2·B_SPAN`). ⚑ Both offsets are the
NAMED constants — the two bare `239`/`478` literals that used to sit here are exactly the drift the
178 → 184 flag day paid for, and 184 → 187 would have paid it again. -/
def rotV3Appendix (w : Nat) : List VmHashSite :=
  rotV3SitesAt w ++ rotV3SitesAt (w + B_SPAN) ++ caveatV3SitesAt (w + CAVEAT_REGION_OFF)

-- Arity discipline: every appendix site is arity 4 or 2 (the chip refuses 3) — checked at
-- a concrete base; the literal arities are base-independent.
#guard (rotV3Appendix 186).all fun s => s.arity == 4 || s.arity == 2
#guard (rotV3Appendix 186).length == 144  -- 63 (before) + 63 (after) + 12 (caveat: 10 + the rc pair)
-- ⚑ **THE COUNTING GATE**, stated where both sources exist: pin `B_SPAN`'s FLOOR-division formula
-- against the LITERAL site walk. A block is its limbs, its iroot, and one column per emitted site
-- (62 chain carriers + the state-commit carrier). `(n − 4)/3` rounds DOWN while `chunk31`'s
-- `chunkCount` rounds UP, so they agree only on `n ≡ 1 (mod 3)` — at n = 185 the formula would have
-- said 60 carriers where the chain needs 61 and the block would have been silently one column
-- short, with every other `#guard` in this file still passing. THIS is the one that would go red.
#guard B_SPAN == rotatedNumPreLimbs + 1 + (rotV3SitesAt 0).length
#guard (rotV3SitesAt 0).length == 66
#guard (rotV3SitesAt 0).map (·.digestCol) == (List.range 65).map (· + 198) ++ [197]
-- Every caveat-region site's carrier column lands INSIDE the region (`< C_SPAN`), and the two new
-- ones land exactly on `C_RC_CARRIER` / `C_COMMIT` — the emit cannot drift off the named offsets.
#guard (caveatV3SitesAt 0).map (·.digestCol) == [29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 43, 44]
#guard (caveatV3SitesAt 0).all fun s => s.digestCol < C_SPAN

/-- The columns the caveat-region sites READ (their `.col` inputs) — the emit-level surface
`UnforcedPiPins.forcedCols` sums for this region. -/
def caveatV3SiteReads (base : Nat) : List Nat :=
  (caveatV3SitesAt base).flatMap fun s =>
    s.inputs.filterMap fun i => match i with | .col c => some c | _ => none

-- ⚑ **THE ANTI-VACUITY GUARD.** All FOUR DFA route-commitment columns are READ by a caveat-region
-- chip site. This is the whole repair in one executable line: before the rc FOLD this list
-- contained the 29 manifest limbs and the nine carriers and NOTHING at 39..42, which is why
-- `dropUnforcedPins` was right to delete the pins on them. A member's `forcedCols` contains this
-- surface, so the pins now survive the subtraction on their own merits.
#guard (List.range 4).all fun k => (caveatV3SiteReads 0).contains (C_RC_OFF + k)
#guard (caveatV3SiteReads 0).contains C_MANIFEST_COMMIT   -- ...and the manifest fold feeds it
#guard (caveatV3SiteReads 0).contains C_RC_CARRIER        -- ...and the first rc carrier feeds the commit
-- The commitment itself is a DIGEST, never an input (a chain ends there).
#guard !(caveatV3SiteReads 0).contains C_COMMIT
-- Every manifest limb is still read (the rc extension ADDED, it displaced nothing).
#guard (List.range 29).all fun k => (caveatV3SiteReads 0).contains k

-- **THE BYTE-IDENTITY TRIPWIRE** (v15, 187-limb shape): the col-chained 63-site block at base 0
-- graduates to the EXACT wire JSON of its DIGEST-chained twin (the running accumulator referenced
-- as `.digest (k-1)` instead of `.col carrier`). `HashInput.toExpr` resolves `.digest k` to site
-- `k`'s `digestCol`, which IS the chain-carrier column the col-chained form names, so the two emit
-- byte-for-byte. This is the standalone analog of the old R=24-probe cross-check, at the deployed
-- 187-limb geometry (the R-register probe no longer matches the faithful-8-felt completion limbs).
private def rotV3SitesDigestAt0 : List VmHashSite :=
  [ ⟨198, [.col 0, .col 1, .col 2, .col 3], 4⟩
  , ⟨199, [.digest 0, .col 4, .col 5, .col 6], 4⟩
  , ⟨200, [.digest 1, .col 7, .col 8, .col 9], 4⟩
  , ⟨201, [.digest 2, .col 10, .col 11, .col 12], 4⟩
  , ⟨202, [.digest 3, .col 13, .col 14, .col 15], 4⟩
  , ⟨203, [.digest 4, .col 16, .col 17, .col 18], 4⟩
  , ⟨204, [.digest 5, .col 19, .col 20, .col 21], 4⟩
  , ⟨205, [.digest 6, .col 22, .col 23, .col 24], 4⟩
  , ⟨206, [.digest 7, .col 25, .col 26, .col 27], 4⟩
  , ⟨207, [.digest 8, .col 28, .col 29, .col 30], 4⟩
  , ⟨208, [.digest 9, .col 31, .col 32, .col 33], 4⟩
  , ⟨209, [.digest 10, .col 34, .col 35, .col 36], 4⟩
  , ⟨210, [.digest 11, .col 37, .col 38, .col 39], 4⟩
  , ⟨211, [.digest 12, .col 40, .col 41, .col 42], 4⟩
  , ⟨212, [.digest 13, .col 43, .col 44, .col 45], 4⟩
  , ⟨213, [.digest 14, .col 46, .col 47, .col 48], 4⟩
  , ⟨214, [.digest 15, .col 49, .col 50, .col 51], 4⟩
  , ⟨215, [.digest 16, .col 52, .col 53, .col 54], 4⟩
  , ⟨216, [.digest 17, .col 55, .col 56, .col 57], 4⟩
  , ⟨217, [.digest 18, .col 58, .col 59, .col 60], 4⟩
  , ⟨218, [.digest 19, .col 61, .col 62, .col 63], 4⟩
  , ⟨219, [.digest 20, .col 64, .col 65, .col 66], 4⟩
  , ⟨220, [.digest 21, .col 67, .col 68, .col 69], 4⟩
  , ⟨221, [.digest 22, .col 70, .col 71, .col 72], 4⟩
  , ⟨222, [.digest 23, .col 73, .col 74, .col 75], 4⟩
  , ⟨223, [.digest 24, .col 76, .col 77, .col 78], 4⟩
  , ⟨224, [.digest 25, .col 79, .col 80, .col 81], 4⟩
  , ⟨225, [.digest 26, .col 82, .col 83, .col 84], 4⟩
  , ⟨226, [.digest 27, .col 85, .col 86, .col 87], 4⟩
  , ⟨227, [.digest 28, .col 88, .col 89, .col 90], 4⟩
  , ⟨228, [.digest 29, .col 91, .col 92, .col 93], 4⟩
  , ⟨229, [.digest 30, .col 94, .col 95, .col 96], 4⟩
  , ⟨230, [.digest 31, .col 97, .col 98, .col 99], 4⟩
  , ⟨231, [.digest 32, .col 100, .col 101, .col 102], 4⟩
  , ⟨232, [.digest 33, .col 103, .col 104, .col 105], 4⟩
  , ⟨233, [.digest 34, .col 106, .col 107, .col 108], 4⟩
  , ⟨234, [.digest 35, .col 109, .col 110, .col 111], 4⟩
  , ⟨235, [.digest 36, .col 112, .col 113, .col 114], 4⟩
  , ⟨236, [.digest 37, .col 115, .col 116, .col 117], 4⟩
  , ⟨237, [.digest 38, .col 118, .col 119, .col 120], 4⟩
  , ⟨238, [.digest 39, .col 121, .col 122, .col 123], 4⟩
  , ⟨239, [.digest 40, .col 124, .col 125, .col 126], 4⟩
  , ⟨240, [.digest 41, .col 127, .col 128, .col 129], 4⟩
  , ⟨241, [.digest 42, .col 130, .col 131, .col 132], 4⟩
  , ⟨242, [.digest 43, .col 133, .col 134, .col 135], 4⟩
  , ⟨243, [.digest 44, .col 136, .col 137, .col 138], 4⟩
  , ⟨244, [.digest 45, .col 139, .col 140, .col 141], 4⟩
  , ⟨245, [.digest 46, .col 142, .col 143, .col 144], 4⟩
  , ⟨246, [.digest 47, .col 145, .col 146, .col 147], 4⟩
  , ⟨247, [.digest 48, .col 148, .col 149, .col 150], 4⟩
  , ⟨248, [.digest 49, .col 151, .col 152, .col 153], 4⟩
  , ⟨249, [.digest 50, .col 154, .col 155, .col 156], 4⟩
  , ⟨250, [.digest 51, .col 157, .col 158, .col 159], 4⟩
  , ⟨251, [.digest 52, .col 160, .col 161, .col 162], 4⟩
  , ⟨252, [.digest 53, .col 163, .col 164, .col 165], 4⟩
  , ⟨253, [.digest 54, .col 166, .col 167, .col 168], 4⟩
  , ⟨254, [.digest 55, .col 169, .col 170, .col 171], 4⟩
  , ⟨255, [.digest 56, .col 172, .col 173, .col 174], 4⟩
  , ⟨256, [.digest 57, .col 175, .col 176, .col 177], 4⟩
  , ⟨257, [.digest 58, .col 178, .col 179, .col 180], 4⟩
  , ⟨258, [.digest 59, .col 181, .col 182, .col 183], 4⟩
  , ⟨259, [.digest 60, .col 184, .col 185, .col 186], 4⟩
  , ⟨260, [.digest 61, .col 187, .col 188, .col 189], 4⟩
  , ⟨261, [.digest 62, .col 190, .col 191, .col 192], 4⟩
  , ⟨262, [.digest 63, .col 193, .col 194, .col 195], 4⟩
  , ⟨197, [.digest 64, .col 196], 2⟩ ]

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
    (colEq a b).holdsVm env isFirst isLast ↔ env.loc a ≡ env.loc b [ZMOD 2013265921] := by
  subst hlast
  simp only [colEq, VmConstraint.holdsVm, EmittedExpr.eval]
  exact gate_modEq_iff (by ring)

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
  , .piBinding .last (w + B_SPAN + B_STATE_COMMIT) (piBase + 1)
  , .piBinding .last (w + B_SPAN + B_COMMITTED_HEIGHT) (piBase + 2)
  , .piBinding .last (w + CAVEAT_REGION_OFF + C_COMMIT) (piBase + 3) ]

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
          ++ weldsAt (d.traceWidth + B_SPAN) STATE_AFTER_BASE
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
          ++ weldsAtNoCapRoot (d.traceWidth + B_SPAN) STATE_AFTER_BASE
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

/-- Every rotated-block site is col-only (62 literal cases). -/
theorem rotV3SitesAt_colOnly (base : Nat) : ∀ s ∈ rotV3SitesAt base, colOnly s = true := by
  intro s hs
  fin_cases hs <;> rfl

/-- Every caveat site is col-only (10 literal cases). -/
theorem caveatV3SitesAt_colOnly (base : Nat) :
    ∀ s ∈ caveatV3SitesAt base, colOnly s = true := by
  intro s hs
  simp only [caveatV3SitesAt, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

set_option maxHeartbeats 6400000 in
/-- **The block pin, parametric in `base`** (v14): the sixty-two col-chained site equations compose
into the chained rotated commitment — the row's state-commit carrier at `base + B_STATE_COMMIT` IS
`wireCommitR` of the row's OWN 187 limbs and iroot (the fields-NONET completion shape PLUS the
three carrier-octet ninth lanes 184/185/186, so the OWNER KEY's ninth lane is folded into
`state_commit` here and nowhere else). Stated against the NAMED offsets; the `show` below is the one
place the concrete 188/187 appear. -/
theorem rotV3SitesAt_pin (hash : List ℤ → ℤ) (env : VmRowEnv) (base : Nat)
    (h : ∀ s ∈ rotV3SitesAt base, env.loc s.digestCol = hash (s.resolvedInputs env [])) :
    env.loc (base + B_STATE_COMMIT)
      = wireCommitR hash (preLimbsAt base env.loc) (env.loc (base + B_IROOT)) := by
  show env.loc (base + 197) = wireCommitR hash (preLimbsAt base env.loc) (env.loc (base + 196))
  have h0 : env.loc (base + 198) = hash [env.loc (base + 0), env.loc (base + 1), env.loc (base + 2), env.loc (base + 3)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 198, [.col (base + 0), .col (base + 1), .col (base + 2), .col (base + 3)], 4⟩
        (by simp [rotV3SitesAt])
  have h1 : env.loc (base + 199) = hash [env.loc (base + 198), env.loc (base + 4), env.loc (base + 5), env.loc (base + 6)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 199, [.col (base + 198), .col (base + 4), .col (base + 5), .col (base + 6)], 4⟩
        (by simp [rotV3SitesAt])
  have h2 : env.loc (base + 200) = hash [env.loc (base + 199), env.loc (base + 7), env.loc (base + 8), env.loc (base + 9)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 200, [.col (base + 199), .col (base + 7), .col (base + 8), .col (base + 9)], 4⟩
        (by simp [rotV3SitesAt])
  have h3 : env.loc (base + 201) = hash [env.loc (base + 200), env.loc (base + 10), env.loc (base + 11), env.loc (base + 12)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 201, [.col (base + 200), .col (base + 10), .col (base + 11), .col (base + 12)], 4⟩
        (by simp [rotV3SitesAt])
  have h4 : env.loc (base + 202) = hash [env.loc (base + 201), env.loc (base + 13), env.loc (base + 14), env.loc (base + 15)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 202, [.col (base + 201), .col (base + 13), .col (base + 14), .col (base + 15)], 4⟩
        (by simp [rotV3SitesAt])
  have h5 : env.loc (base + 203) = hash [env.loc (base + 202), env.loc (base + 16), env.loc (base + 17), env.loc (base + 18)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 203, [.col (base + 202), .col (base + 16), .col (base + 17), .col (base + 18)], 4⟩
        (by simp [rotV3SitesAt])
  have h6 : env.loc (base + 204) = hash [env.loc (base + 203), env.loc (base + 19), env.loc (base + 20), env.loc (base + 21)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 204, [.col (base + 203), .col (base + 19), .col (base + 20), .col (base + 21)], 4⟩
        (by simp [rotV3SitesAt])
  have h7 : env.loc (base + 205) = hash [env.loc (base + 204), env.loc (base + 22), env.loc (base + 23), env.loc (base + 24)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 205, [.col (base + 204), .col (base + 22), .col (base + 23), .col (base + 24)], 4⟩
        (by simp [rotV3SitesAt])
  have h8 : env.loc (base + 206) = hash [env.loc (base + 205), env.loc (base + 25), env.loc (base + 26), env.loc (base + 27)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 206, [.col (base + 205), .col (base + 25), .col (base + 26), .col (base + 27)], 4⟩
        (by simp [rotV3SitesAt])
  have h9 : env.loc (base + 207) = hash [env.loc (base + 206), env.loc (base + 28), env.loc (base + 29), env.loc (base + 30)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 207, [.col (base + 206), .col (base + 28), .col (base + 29), .col (base + 30)], 4⟩
        (by simp [rotV3SitesAt])
  have h10 : env.loc (base + 208) = hash [env.loc (base + 207), env.loc (base + 31), env.loc (base + 32), env.loc (base + 33)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 208, [.col (base + 207), .col (base + 31), .col (base + 32), .col (base + 33)], 4⟩
        (by simp [rotV3SitesAt])
  have h11 : env.loc (base + 209) = hash [env.loc (base + 208), env.loc (base + 34), env.loc (base + 35), env.loc (base + 36)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 209, [.col (base + 208), .col (base + 34), .col (base + 35), .col (base + 36)], 4⟩
        (by simp [rotV3SitesAt])
  have h12 : env.loc (base + 210) = hash [env.loc (base + 209), env.loc (base + 37), env.loc (base + 38), env.loc (base + 39)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 210, [.col (base + 209), .col (base + 37), .col (base + 38), .col (base + 39)], 4⟩
        (by simp [rotV3SitesAt])
  have h13 : env.loc (base + 211) = hash [env.loc (base + 210), env.loc (base + 40), env.loc (base + 41), env.loc (base + 42)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 211, [.col (base + 210), .col (base + 40), .col (base + 41), .col (base + 42)], 4⟩
        (by simp [rotV3SitesAt])
  have h14 : env.loc (base + 212) = hash [env.loc (base + 211), env.loc (base + 43), env.loc (base + 44), env.loc (base + 45)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 212, [.col (base + 211), .col (base + 43), .col (base + 44), .col (base + 45)], 4⟩
        (by simp [rotV3SitesAt])
  have h15 : env.loc (base + 213) = hash [env.loc (base + 212), env.loc (base + 46), env.loc (base + 47), env.loc (base + 48)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 213, [.col (base + 212), .col (base + 46), .col (base + 47), .col (base + 48)], 4⟩
        (by simp [rotV3SitesAt])
  have h16 : env.loc (base + 214) = hash [env.loc (base + 213), env.loc (base + 49), env.loc (base + 50), env.loc (base + 51)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 214, [.col (base + 213), .col (base + 49), .col (base + 50), .col (base + 51)], 4⟩
        (by simp [rotV3SitesAt])
  have h17 : env.loc (base + 215) = hash [env.loc (base + 214), env.loc (base + 52), env.loc (base + 53), env.loc (base + 54)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 215, [.col (base + 214), .col (base + 52), .col (base + 53), .col (base + 54)], 4⟩
        (by simp [rotV3SitesAt])
  have h18 : env.loc (base + 216) = hash [env.loc (base + 215), env.loc (base + 55), env.loc (base + 56), env.loc (base + 57)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 216, [.col (base + 215), .col (base + 55), .col (base + 56), .col (base + 57)], 4⟩
        (by simp [rotV3SitesAt])
  have h19 : env.loc (base + 217) = hash [env.loc (base + 216), env.loc (base + 58), env.loc (base + 59), env.loc (base + 60)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 217, [.col (base + 216), .col (base + 58), .col (base + 59), .col (base + 60)], 4⟩
        (by simp [rotV3SitesAt])
  have h20 : env.loc (base + 218) = hash [env.loc (base + 217), env.loc (base + 61), env.loc (base + 62), env.loc (base + 63)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 218, [.col (base + 217), .col (base + 61), .col (base + 62), .col (base + 63)], 4⟩
        (by simp [rotV3SitesAt])
  have h21 : env.loc (base + 219) = hash [env.loc (base + 218), env.loc (base + 64), env.loc (base + 65), env.loc (base + 66)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 219, [.col (base + 218), .col (base + 64), .col (base + 65), .col (base + 66)], 4⟩
        (by simp [rotV3SitesAt])
  have h22 : env.loc (base + 220) = hash [env.loc (base + 219), env.loc (base + 67), env.loc (base + 68), env.loc (base + 69)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 220, [.col (base + 219), .col (base + 67), .col (base + 68), .col (base + 69)], 4⟩
        (by simp [rotV3SitesAt])
  have h23 : env.loc (base + 221) = hash [env.loc (base + 220), env.loc (base + 70), env.loc (base + 71), env.loc (base + 72)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 221, [.col (base + 220), .col (base + 70), .col (base + 71), .col (base + 72)], 4⟩
        (by simp [rotV3SitesAt])
  have h24 : env.loc (base + 222) = hash [env.loc (base + 221), env.loc (base + 73), env.loc (base + 74), env.loc (base + 75)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 222, [.col (base + 221), .col (base + 73), .col (base + 74), .col (base + 75)], 4⟩
        (by simp [rotV3SitesAt])
  have h25 : env.loc (base + 223) = hash [env.loc (base + 222), env.loc (base + 76), env.loc (base + 77), env.loc (base + 78)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 223, [.col (base + 222), .col (base + 76), .col (base + 77), .col (base + 78)], 4⟩
        (by simp [rotV3SitesAt])
  have h26 : env.loc (base + 224) = hash [env.loc (base + 223), env.loc (base + 79), env.loc (base + 80), env.loc (base + 81)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 224, [.col (base + 223), .col (base + 79), .col (base + 80), .col (base + 81)], 4⟩
        (by simp [rotV3SitesAt])
  have h27 : env.loc (base + 225) = hash [env.loc (base + 224), env.loc (base + 82), env.loc (base + 83), env.loc (base + 84)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 225, [.col (base + 224), .col (base + 82), .col (base + 83), .col (base + 84)], 4⟩
        (by simp [rotV3SitesAt])
  have h28 : env.loc (base + 226) = hash [env.loc (base + 225), env.loc (base + 85), env.loc (base + 86), env.loc (base + 87)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 226, [.col (base + 225), .col (base + 85), .col (base + 86), .col (base + 87)], 4⟩
        (by simp [rotV3SitesAt])
  have h29 : env.loc (base + 227) = hash [env.loc (base + 226), env.loc (base + 88), env.loc (base + 89), env.loc (base + 90)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 227, [.col (base + 226), .col (base + 88), .col (base + 89), .col (base + 90)], 4⟩
        (by simp [rotV3SitesAt])
  have h30 : env.loc (base + 228) = hash [env.loc (base + 227), env.loc (base + 91), env.loc (base + 92), env.loc (base + 93)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 228, [.col (base + 227), .col (base + 91), .col (base + 92), .col (base + 93)], 4⟩
        (by simp [rotV3SitesAt])
  have h31 : env.loc (base + 229) = hash [env.loc (base + 228), env.loc (base + 94), env.loc (base + 95), env.loc (base + 96)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 229, [.col (base + 228), .col (base + 94), .col (base + 95), .col (base + 96)], 4⟩
        (by simp [rotV3SitesAt])
  have h32 : env.loc (base + 230) = hash [env.loc (base + 229), env.loc (base + 97), env.loc (base + 98), env.loc (base + 99)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 230, [.col (base + 229), .col (base + 97), .col (base + 98), .col (base + 99)], 4⟩
        (by simp [rotV3SitesAt])
  have h33 : env.loc (base + 231) = hash [env.loc (base + 230), env.loc (base + 100), env.loc (base + 101), env.loc (base + 102)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 231, [.col (base + 230), .col (base + 100), .col (base + 101), .col (base + 102)], 4⟩
        (by simp [rotV3SitesAt])
  have h34 : env.loc (base + 232) = hash [env.loc (base + 231), env.loc (base + 103), env.loc (base + 104), env.loc (base + 105)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 232, [.col (base + 231), .col (base + 103), .col (base + 104), .col (base + 105)], 4⟩
        (by simp [rotV3SitesAt])
  have h35 : env.loc (base + 233) = hash [env.loc (base + 232), env.loc (base + 106), env.loc (base + 107), env.loc (base + 108)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 233, [.col (base + 232), .col (base + 106), .col (base + 107), .col (base + 108)], 4⟩
        (by simp [rotV3SitesAt])
  have h36 : env.loc (base + 234) = hash [env.loc (base + 233), env.loc (base + 109), env.loc (base + 110), env.loc (base + 111)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 234, [.col (base + 233), .col (base + 109), .col (base + 110), .col (base + 111)], 4⟩
        (by simp [rotV3SitesAt])
  have h37 : env.loc (base + 235) = hash [env.loc (base + 234), env.loc (base + 112), env.loc (base + 113), env.loc (base + 114)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 235, [.col (base + 234), .col (base + 112), .col (base + 113), .col (base + 114)], 4⟩
        (by simp [rotV3SitesAt])
  have h38 : env.loc (base + 236) = hash [env.loc (base + 235), env.loc (base + 115), env.loc (base + 116), env.loc (base + 117)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 236, [.col (base + 235), .col (base + 115), .col (base + 116), .col (base + 117)], 4⟩
        (by simp [rotV3SitesAt])
  have h39 : env.loc (base + 237) = hash [env.loc (base + 236), env.loc (base + 118), env.loc (base + 119), env.loc (base + 120)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 237, [.col (base + 236), .col (base + 118), .col (base + 119), .col (base + 120)], 4⟩
        (by simp [rotV3SitesAt])
  have h40 : env.loc (base + 238) = hash [env.loc (base + 237), env.loc (base + 121), env.loc (base + 122), env.loc (base + 123)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 238, [.col (base + 237), .col (base + 121), .col (base + 122), .col (base + 123)], 4⟩
        (by simp [rotV3SitesAt])
  have h41 : env.loc (base + 239) = hash [env.loc (base + 238), env.loc (base + 124), env.loc (base + 125), env.loc (base + 126)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 239, [.col (base + 238), .col (base + 124), .col (base + 125), .col (base + 126)], 4⟩
        (by simp [rotV3SitesAt])
  have h42 : env.loc (base + 240) = hash [env.loc (base + 239), env.loc (base + 127), env.loc (base + 128), env.loc (base + 129)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 240, [.col (base + 239), .col (base + 127), .col (base + 128), .col (base + 129)], 4⟩
        (by simp [rotV3SitesAt])
  have h43 : env.loc (base + 241) = hash [env.loc (base + 240), env.loc (base + 130), env.loc (base + 131), env.loc (base + 132)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 241, [.col (base + 240), .col (base + 130), .col (base + 131), .col (base + 132)], 4⟩
        (by simp [rotV3SitesAt])
  have h44 : env.loc (base + 242) = hash [env.loc (base + 241), env.loc (base + 133), env.loc (base + 134), env.loc (base + 135)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 242, [.col (base + 241), .col (base + 133), .col (base + 134), .col (base + 135)], 4⟩
        (by simp [rotV3SitesAt])
  have h45 : env.loc (base + 243) = hash [env.loc (base + 242), env.loc (base + 136), env.loc (base + 137), env.loc (base + 138)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 243, [.col (base + 242), .col (base + 136), .col (base + 137), .col (base + 138)], 4⟩
        (by simp [rotV3SitesAt])
  have h46 : env.loc (base + 244) = hash [env.loc (base + 243), env.loc (base + 139), env.loc (base + 140), env.loc (base + 141)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 244, [.col (base + 243), .col (base + 139), .col (base + 140), .col (base + 141)], 4⟩
        (by simp [rotV3SitesAt])
  have h47 : env.loc (base + 245) = hash [env.loc (base + 244), env.loc (base + 142), env.loc (base + 143), env.loc (base + 144)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 245, [.col (base + 244), .col (base + 142), .col (base + 143), .col (base + 144)], 4⟩
        (by simp [rotV3SitesAt])
  have h48 : env.loc (base + 246) = hash [env.loc (base + 245), env.loc (base + 145), env.loc (base + 146), env.loc (base + 147)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 246, [.col (base + 245), .col (base + 145), .col (base + 146), .col (base + 147)], 4⟩
        (by simp [rotV3SitesAt])
  have h49 : env.loc (base + 247) = hash [env.loc (base + 246), env.loc (base + 148), env.loc (base + 149), env.loc (base + 150)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 247, [.col (base + 246), .col (base + 148), .col (base + 149), .col (base + 150)], 4⟩
        (by simp [rotV3SitesAt])
  have h50 : env.loc (base + 248) = hash [env.loc (base + 247), env.loc (base + 151), env.loc (base + 152), env.loc (base + 153)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 248, [.col (base + 247), .col (base + 151), .col (base + 152), .col (base + 153)], 4⟩
        (by simp [rotV3SitesAt])
  have h51 : env.loc (base + 249) = hash [env.loc (base + 248), env.loc (base + 154), env.loc (base + 155), env.loc (base + 156)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 249, [.col (base + 248), .col (base + 154), .col (base + 155), .col (base + 156)], 4⟩
        (by simp [rotV3SitesAt])
  have h52 : env.loc (base + 250) = hash [env.loc (base + 249), env.loc (base + 157), env.loc (base + 158), env.loc (base + 159)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 250, [.col (base + 249), .col (base + 157), .col (base + 158), .col (base + 159)], 4⟩
        (by simp [rotV3SitesAt])
  have h53 : env.loc (base + 251) = hash [env.loc (base + 250), env.loc (base + 160), env.loc (base + 161), env.loc (base + 162)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 251, [.col (base + 250), .col (base + 160), .col (base + 161), .col (base + 162)], 4⟩
        (by simp [rotV3SitesAt])
  have h54 : env.loc (base + 252) = hash [env.loc (base + 251), env.loc (base + 163), env.loc (base + 164), env.loc (base + 165)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 252, [.col (base + 251), .col (base + 163), .col (base + 164), .col (base + 165)], 4⟩
        (by simp [rotV3SitesAt])
  have h55 : env.loc (base + 253) = hash [env.loc (base + 252), env.loc (base + 166), env.loc (base + 167), env.loc (base + 168)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 253, [.col (base + 252), .col (base + 166), .col (base + 167), .col (base + 168)], 4⟩
        (by simp [rotV3SitesAt])
  have h56 : env.loc (base + 254) = hash [env.loc (base + 253), env.loc (base + 169), env.loc (base + 170), env.loc (base + 171)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 254, [.col (base + 253), .col (base + 169), .col (base + 170), .col (base + 171)], 4⟩
        (by simp [rotV3SitesAt])
  have h57 : env.loc (base + 255) = hash [env.loc (base + 254), env.loc (base + 172), env.loc (base + 173), env.loc (base + 174)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 255, [.col (base + 254), .col (base + 172), .col (base + 173), .col (base + 174)], 4⟩
        (by simp [rotV3SitesAt])
  have h58 : env.loc (base + 256) = hash [env.loc (base + 255), env.loc (base + 175), env.loc (base + 176), env.loc (base + 177)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 256, [.col (base + 255), .col (base + 175), .col (base + 176), .col (base + 177)], 4⟩
        (by simp [rotV3SitesAt])
  have h59 : env.loc (base + 257) = hash [env.loc (base + 256), env.loc (base + 178), env.loc (base + 179), env.loc (base + 180)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 257, [.col (base + 256), .col (base + 178), .col (base + 179), .col (base + 180)], 4⟩
        (by simp [rotV3SitesAt])
  have h60 : env.loc (base + 258) = hash [env.loc (base + 257), env.loc (base + 181), env.loc (base + 182), env.loc (base + 183)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 258, [.col (base + 257), .col (base + 181), .col (base + 182), .col (base + 183)], 4⟩
        (by simp [rotV3SitesAt])
  have h61 : env.loc (base + 259) = hash [env.loc (base + 258), env.loc (base + 184), env.loc (base + 185), env.loc (base + 186)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 259, [.col (base + 258), .col (base + 184), .col (base + 185), .col (base + 186)], 4⟩
        (by simp [rotV3SitesAt])
  have h62 : env.loc (base + 260) = hash [env.loc (base + 259), env.loc (base + 187), env.loc (base + 188), env.loc (base + 189)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 260, [.col (base + 259), .col (base + 187), .col (base + 188), .col (base + 189)], 4⟩
        (by simp [rotV3SitesAt])
  have h63 : env.loc (base + 261) = hash [env.loc (base + 260), env.loc (base + 190), env.loc (base + 191), env.loc (base + 192)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 261, [.col (base + 260), .col (base + 190), .col (base + 191), .col (base + 192)], 4⟩
        (by simp [rotV3SitesAt])
  have h64 : env.loc (base + 262) = hash [env.loc (base + 261), env.loc (base + 193), env.loc (base + 194), env.loc (base + 195)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 262, [.col (base + 261), .col (base + 193), .col (base + 194), .col (base + 195)], 4⟩
        (by simp [rotV3SitesAt])
  have h65 : env.loc (base + 197) = hash [env.loc (base + 262), env.loc (base + 196)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 197, [.col (base + 262), .col (base + 196)], 2⟩
        (by simp [rotV3SitesAt])
  rw [h65, h64, h63, h62, h61, h60, h59, h58, h57, h56, h55, h54, h53, h52, h51, h50, h49, h48, h47, h46, h45, h44, h43, h42, h41, h40, h39, h38, h37, h36, h35, h34, h33, h32, h31, h30, h29, h28, h27, h26, h25, h24, h23, h22, h21, h20, h19, h18, h17, h16, h15, h14, h13, h12, h11, h10, h9, h8, h7, h6, h5, h4, h3, h2, h1, h0]
  rfl

set_option maxHeartbeats 6400000 in
/-- **The caveat MANIFEST pin, parametric in `base`**: the ten col-chained manifest site equations
compose into the chained caveat commitment of the row's OWN manifest block. (The published
commitment is the rc EXTENSION of this — `caveatV3SitesAt_pin_rc` below.) -/
theorem caveatV3SitesAt_pin (hash : List ℤ → ℤ) (env : VmRowEnv) (base : Nat)
    (h : ∀ s ∈ caveatV3SitesAt base, env.loc s.digestCol = hash (s.resolvedInputs env [])) :
    env.loc (base + C_MANIFEST_COMMIT) = caveatCommit hash (manifestAt base env.loc) := by
  show env.loc (base + 38) = caveatCommit hash (manifestAt base env.loc)
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

set_option maxHeartbeats 6400000 in
/-- **THE PUBLISHED CAVEAT PIN, parametric in `base`** — the column `rotPins` pins to PI
`piBase + 3` carries `caveatCommitRc` of the row's OWN manifest block AND its OWN DFA
route-commitment carrier. Two further site equations past the manifest fold, in the same
`chunk31` arity-{2,4} discipline.

⚑ This is the theorem that makes the rc carrier a BOUND datum rather than a published one. The
`withDfaRcPins` pins publish columns `base + C_RC_OFF + k`; those same four columns are read HERE
by two chip sites onto the pinned commitment, so an adversary who rewrites the carrier AND the
four PIs it publishes still moves `env.loc (base + C_COMMIT)` — and that column is pinned to a PI
a verifier reconstructs from the turn's own witnessed predicates. -/
theorem caveatV3SitesAt_pin_rc (hash : List ℤ → ℤ) (env : VmRowEnv) (base : Nat)
    (h : ∀ s ∈ caveatV3SitesAt base, env.loc s.digestCol = hash (s.resolvedInputs env [])) :
    env.loc (base + C_COMMIT)
      = caveatCommitRc hash (manifestAt base env.loc) (rcAt base env.loc) := by
  have hman := caveatV3SitesAt_pin hash env base h
  show env.loc (base + 44) = caveatCommitRc hash (manifestAt base env.loc) (rcAt base env.loc)
  have h10 : env.loc (base + 43) = hash [env.loc (base + 38), env.loc (base + 39),
      env.loc (base + 40), env.loc (base + 41)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 43, [.col (base + 38), .col (base + 39), .col (base + 40),
        .col (base + 41)], 4⟩ (by simp [caveatV3SitesAt])
  have h11 : env.loc (base + 44) = hash [env.loc (base + 43), env.loc (base + 42)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 44, [.col (base + 43), .col (base + 42)], 2⟩ (by simp [caveatV3SitesAt])
  show env.loc (base + 44)
    = chainFrom hash (caveatCommit hash (manifestAt base env.loc)) (chunk31 (rcAt base env.loc))
  rw [h11, h10, ← hman]
  show _ = chainFrom hash (env.loc (base + C_MANIFEST_COMMIT))
    (chunk31 [env.loc (base + C_RC_OFF), env.loc (base + C_RC_OFF + 1),
      env.loc (base + C_RC_OFF + 2), env.loc (base + C_RC_OFF + 3)])
  rfl

#assert_axioms go_colOnly_mem
#assert_axioms rotV3SitesAt_pin
#assert_axioms caveatV3SitesAt_pin
#assert_axioms caveatV3SitesAt_pin_rc

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
    env.loc (d.traceWidth + B_STATE_COMMIT)
      = wireCommitR hash (preLimbsAt d.traceWidth env.loc) (env.loc (d.traceWidth + B_IROOT))
    ∧ env.loc (d.traceWidth + B_SPAN + B_STATE_COMMIT)
      = wireCommitR hash (preLimbsAt (d.traceWidth + B_SPAN) env.loc)
          (env.loc (d.traceWidth + B_SPAN + B_IROOT))
    ∧ env.loc (d.traceWidth + CAVEAT_REGION_OFF + C_COMMIT)
      = caveatCommitRc hash (manifestAt (d.traceWidth + CAVEAT_REGION_OFF) env.loc)
          (rcAt (d.traceWidth + CAVEAT_REGION_OFF) env.loc) := by
  have hsites := h.2.1
  have heq := go_colOnly_mem hash env [] _ hsites
  have hmem : ∀ s ∈ rotV3Appendix d.traceWidth, s ∈ (rotateV3 d).hashSites :=
    fun s hs => List.mem_append_right _ hs
  refine ⟨?_, ?_, ?_⟩
  · exact rotV3SitesAt_pin hash env d.traceWidth fun s hs =>
      heq s (hmem s (List.mem_append_left _ (List.mem_append_left _ hs)))
        (rotV3SitesAt_colOnly _ s hs)
  · exact rotV3SitesAt_pin hash env (d.traceWidth + B_SPAN) fun s hs =>
      heq s (hmem s (List.mem_append_left _ (List.mem_append_right _ hs)))
        (rotV3SitesAt_colOnly _ s hs)
  · exact caveatV3SitesAt_pin_rc hash env (d.traceWidth + CAVEAT_REGION_OFF) fun s hs =>
      heq s (hmem s (List.mem_append_right _ hs)) (caveatV3SitesAt_colOnly _ s hs)

/-- A weld of the rotated descriptor holds on every satisfying TRANSITION row (`isLast = false`).
The weld is a `.gate`, which under the deployed `when_transition()` binds only off the last row, so
the welded-column equality is read at the active row. -/
theorem rotateV3_weld (hash : List ℤ → ℤ) (d : EffectVmDescriptor)
    (env : VmRowEnv) (isFirst isLast : Bool) (hlast : isLast = false)
    (h : satisfiedVm hash (rotateV3 d) env isFirst isLast)
    {a b : Nat}
    (hw : colEq a b ∈ weldsAt d.traceWidth STATE_BEFORE_BASE
        ∨ colEq a b ∈ weldsAt (d.traceWidth + B_SPAN) STATE_AFTER_BASE) :
    env.loc a ≡ env.loc b [ZMOD 2013265921] := by
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
    env.loc (d.traceWidth + 1) ≡ env.loc (sbCol state.BALANCE_LO) [ZMOD 2013265921]
    ∧ env.loc (d.traceWidth + 2) ≡ env.loc (sbCol state.NONCE) [ZMOD 2013265921]
    ∧ env.loc (d.traceWidth + B_CAP_ROOT) ≡ env.loc (sbCol state.CAP_ROOT) [ZMOD 2013265921]
    ∧ env.loc (d.traceWidth + B_SPAN + 1) ≡ env.loc (saCol state.BALANCE_LO) [ZMOD 2013265921]
    ∧ env.loc (d.traceWidth + B_SPAN + 2) ≡ env.loc (saCol state.NONCE) [ZMOD 2013265921]
    ∧ env.loc (d.traceWidth + B_SPAN + B_CAP_ROOT) ≡ env.loc (saCol state.CAP_ROOT) [ZMOD 2013265921] := by
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
    · rcases List.mem_append.mp hs' with hs'' | hs'' <;> fin_cases hs'' <;> rfl
    · fin_cases hs' <;> rfl

#assert_axioms rotateV3_satisfiedVm_v1
#assert_axioms rotateV3_pins_commits
#assert_axioms rotateV3_welds_named
#assert_axioms graduable_rotateV3

/-! ### The Satisfied2-level keystones (one composition each, parametric in `d`). -/

/-- The graduated rotated descriptor of a cohort member. -/
def v3Of (d : EffectVmDescriptor)
    (hAdm : ∀ s ∈ (rotateV3 d).hashSites,
        ChipArityAdmitted s.inputs.length := by graduate_arity) :
    EffectVmDescriptor2 :=
  graduateV1 (rotateV3 d) hAdm

/-- **THE GRADUATION MODEL, AS ONE NAMED SOURCE.**  The width a v1 face `d` reaches once it is
rotated and graduated: its own face, plus the rotated appendix, plus `CHIP_OUT_LANES - 1` lane
columns per chip site (its own sites plus the appendix's).

⚑ This exists so that no consumer ever pins a rotated member's width to a LITERAL again.  A literal
is a constant checked against its own definition — it cannot go red for any reason except that the
geometry moved, its only repair is retyping, and on 2026-08-01 (`rotatedNumPreLimbs` 184 → 187) a
dozen of them went red at once across the tree and took the whole emitter cone, and with it
`check-descriptor-drift.sh`, offline while detecting nothing.  `X.traceWidth == gradRotWidthOf f`
is a different thing: the MODEL against what `graduateV1 ∘ rotateV3*` actually emitted.  It rides
every rotation flag day unchanged and still reds if graduation's per-site lane count, the appendix's
site walk, or the face's own chip sites move. -/
def gradRotWidthOf (d : EffectVmDescriptor) : Nat :=
  (d.traceWidth + APPENDIX_SPAN)
    + (CHIP_OUT_LANES - 1) * (d.hashSites.length + (rotV3Appendix d.traceWidth).length)

-- The model IS the emission, for the plain rotation.
#guard (v3Of EffectVmEmitTransfer.transferVmDescriptor).traceWidth
  == gradRotWidthOf EffectVmEmitTransfer.transferVmDescriptor

/-- A `Satisfied2` witness of the rotated graduation yields the FULL v1 denotation of the
ORIGINAL descriptor on every row — the per-effect soundness chains lift to v3 by THIS one
composition. -/
theorem rotV3_sound_v1 (permOut : List ℤ → List ℤ) (hash : List ℤ → ℤ) (d : EffectVmDescriptor)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hgrad : graduable d = true)
    (hf : Satisfied2Faithful permOut hash (v3Of d (sitesFit_admitted (graduable_spec (graduable_rotateV3 hgrad)).2.1)) minit mfin maddrs t) :
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
    (hf : Satisfied2Faithful permOut hash (v3Of d (sitesFit_admitted (graduable_spec (graduable_rotateV3 hgrad)).2.1)) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) :
    (envAt t i).loc (d.traceWidth + B_STATE_COMMIT)
      = wireCommitR hash (preLimbsAt d.traceWidth (envAt t i).loc)
          ((envAt t i).loc (d.traceWidth + B_IROOT))
    ∧ (envAt t i).loc (d.traceWidth + B_SPAN + B_STATE_COMMIT)
      = wireCommitR hash (preLimbsAt (d.traceWidth + B_SPAN) (envAt t i).loc)
          ((envAt t i).loc (d.traceWidth + B_SPAN + B_IROOT))
    ∧ (envAt t i).loc (d.traceWidth + CAVEAT_REGION_OFF + C_COMMIT)
      = caveatCommitRc hash (manifestAt (d.traceWidth + CAVEAT_REGION_OFF) (envAt t i).loc)
          (rcAt (d.traceWidth + CAVEAT_REGION_OFF) (envAt t i).loc) :=
  rotateV3_pins_commits hash d _ _ _
    (satisfied2Faithful_satisfiedVm permOut hash (rotateV3 d) minit mfin maddrs t
      (graduable_rotateV3 hgrad) hf i hi)

/-- The rotated descriptor PUBLISHES: first row → rotated OLD commit on PI `d.piCount`;
last row → rotated NEW commit, rotated height, caveat commit on `d.piCount + 1..3`. -/
theorem rotV3_publishes (permOut : List ℤ → List ℤ) (hash : List ℤ → ℤ) (d : EffectVmDescriptor)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hgrad : graduable d = true)
    (hf : Satisfied2Faithful permOut hash (v3Of d (sitesFit_admitted (graduable_spec (graduable_rotateV3 hgrad)).2.1)) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) :
    ((i == 0) = true →
      (envAt t i).loc (d.traceWidth + B_STATE_COMMIT) ≡ (envAt t i).pub d.piCount [ZMOD 2013265921])
    ∧ ((i + 1 == t.rows.length) = true →
      (envAt t i).loc (d.traceWidth + B_SPAN + B_STATE_COMMIT)
          ≡ (envAt t i).pub (d.piCount + 1) [ZMOD 2013265921]
      ∧ (envAt t i).loc (d.traceWidth + B_SPAN + B_COMMITTED_HEIGHT)
          ≡ (envAt t i).pub (d.piCount + 2) [ZMOD 2013265921]
      ∧ (envAt t i).loc (d.traceWidth + CAVEAT_REGION_OFF + C_COMMIT)
          ≡ (envAt t i).pub (d.piCount + 3) [ZMOD 2013265921]) := by
  have h := satisfied2Faithful_satisfiedVm permOut hash (rotateV3 d) minit mfin maddrs t
    (graduable_rotateV3 hgrad) hf i hi
  have hmem : ∀ c ∈ rotPins d.traceWidth d.piCount, c ∈ (rotateV3 d).constraints :=
    fun c hc => List.mem_append_right _ (List.mem_append_right _ hc)
  have h0 := h.1 _ (hmem (.piBinding .first (d.traceWidth + B_STATE_COMMIT) d.piCount)
    (by simp [rotPins]))
  have h1 := h.1 _ (hmem (.piBinding .last (d.traceWidth + B_SPAN + B_STATE_COMMIT)
    (d.piCount + 1)) (by simp [rotPins]))
  have h2 := h.1 _ (hmem (.piBinding .last (d.traceWidth + B_SPAN + B_COMMITTED_HEIGHT)
    (d.piCount + 2)) (by simp [rotPins]))
  have h3 := h.1 _ (hmem (.piBinding .last (d.traceWidth + CAVEAT_REGION_OFF + C_COMMIT) (d.piCount + 3))
    (by simp [rotPins]))
  simp only [VmConstraint.holdsVm] at h0 h1 h2 h3
  exact ⟨h0, fun hl => ⟨h1 hl, h2 hl, h3 hl⟩⟩

/-- **THE rc TOOTH — the caveat leg, stated alone.** Two last-row `Satisfied2` witnesses of the
same cohort member that publish the SAME caveat commit (PI `piCount + 3`) agree on the WHOLE
caveat manifest AND on the 4-felt DFA route-commitment carrier.

This is the statement the pin-only emit could not make. `withDfaRcPins` alone gave
`loc(rc col) ≡ pub(rc slot)`, which an adversary satisfies by moving BOTH sides; nothing tied
either side to a value a verifier holds. With the carrier folded into the pinned commitment, the
rc is forced by the SAME published felt the manifest is. -/
theorem rotV3_caveat_binds_manifest_and_rc (permOut : List ℤ → List ℤ) (hash : List ℤ → ℤ)
    (hCR : Poseidon2SpongeCR hash)
    (d : EffectVmDescriptor)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (minit' : ℤ → ℤ) (mfin' : ℤ → ℤ × Nat) (maddrs' : List ℤ) (t' : VmTrace)
    (hgrad : graduable d = true)
    (hf : Satisfied2Faithful permOut hash (v3Of d (sitesFit_admitted (graduable_spec (graduable_rotateV3 hgrad)).2.1)) minit mfin maddrs t)
    (hf' : Satisfied2Faithful permOut hash (v3Of d (sitesFit_admitted (graduable_spec (graduable_rotateV3 hgrad)).2.1)) minit' mfin' maddrs' t')
    (k l : Nat) (hk : k < t.rows.length) (hl : l < t'.rows.length)
    (hlast : (k + 1 == t.rows.length) = true) (hlast' : (l + 1 == t'.rows.length) = true)
    (hpubCav : (envAt t k).pub (d.piCount + 3) = (envAt t' l).pub (d.piCount + 3))
    (hcCanonCav : 0 ≤ (envAt t k).loc (d.traceWidth + CAVEAT_REGION_OFF + C_COMMIT)
        ∧ (envAt t k).loc (d.traceWidth + CAVEAT_REGION_OFF + C_COMMIT) < 2013265921)
    (hcCanonCav' : 0 ≤ (envAt t' l).loc (d.traceWidth + CAVEAT_REGION_OFF + C_COMMIT)
        ∧ (envAt t' l).loc (d.traceWidth + CAVEAT_REGION_OFF + C_COMMIT) < 2013265921) :
    manifestAt (d.traceWidth + CAVEAT_REGION_OFF) (envAt t k).loc
        = manifestAt (d.traceWidth + CAVEAT_REGION_OFF) (envAt t' l).loc
    ∧ rcAt (d.traceWidth + CAVEAT_REGION_OFF) (envAt t k).loc
        = rcAt (d.traceWidth + CAVEAT_REGION_OFF) (envAt t' l).loc := by
  have hp := rotV3_pins permOut hash d minit mfin maddrs t hgrad hf
  have hp' := rotV3_pins permOut hash d minit' mfin' maddrs' t' hgrad hf'
  obtain ⟨-, -, hk1⟩ := (rotV3_publishes permOut hash d minit mfin maddrs t hgrad hf k hk).2 hlast
  obtain ⟨-, -, hk2⟩ :=
    (rotV3_publishes permOut hash d minit' mfin' maddrs' t' hgrad hf' l hl).2 hlast'
  have hccEq : (envAt t k).loc (d.traceWidth + CAVEAT_REGION_OFF + C_COMMIT)
      = (envAt t' l).loc (d.traceWidth + CAVEAT_REGION_OFF + C_COMMIT) :=
    canon_eq_of_modEq hcCanonCav hcCanonCav'
      (calc (envAt t k).loc (d.traceWidth + CAVEAT_REGION_OFF + C_COMMIT)
            ≡ (envAt t k).pub (d.piCount + 3) [ZMOD 2013265921] := hk1
        _ = (envAt t' l).pub (d.piCount + 3) := hpubCav
        _ ≡ (envAt t' l).loc (d.traceWidth + CAVEAT_REGION_OFF + C_COMMIT) [ZMOD 2013265921] :=
            hk2.symm)
  have hcc : caveatCommitRc hash (manifestAt (d.traceWidth + CAVEAT_REGION_OFF) (envAt t k).loc)
        (rcAt (d.traceWidth + CAVEAT_REGION_OFF) (envAt t k).loc)
      = caveatCommitRc hash (manifestAt (d.traceWidth + CAVEAT_REGION_OFF) (envAt t' l).loc)
        (rcAt (d.traceWidth + CAVEAT_REGION_OFF) (envAt t' l).loc) := by
    rw [← (hp k hk).2.2, ← (hp' l hl).2.2]
    show (envAt t k).loc (d.traceWidth + CAVEAT_REGION_OFF + C_COMMIT)
      = (envAt t' l).loc (d.traceWidth + CAVEAT_REGION_OFF + C_COMMIT)
    exact hccEq
  exact caveatCommitRc_binds hash hCR (by rw [rcAt_length, rcAt_length]) hcc

/-- **THE MOVE-BOTH REFUSAL, contrapositive.** A leg whose route-commitment carrier DIFFERS from
the honest one publishes a DIFFERENT caveat commit — no matter what it does to the four PI slots
`withDfaRcPins` publishes, because those pins are not what binds the carrier any more. Against a
caveat commit the verifier reconstructs from the turn's OWN witnessed predicates
(`proof_verify.rs`: PI `piCount + 3` is witness-INDEPENDENT and re-derived, and `caveat.dfa_rc` is
recomputed from the turn's Dfa blobs), such a leg is UNSAT. -/
theorem rotV3_moved_rc_moves_the_published_caveat_commit (permOut : List ℤ → List ℤ)
    (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (d : EffectVmDescriptor)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (minit' : ℤ → ℤ) (mfin' : ℤ → ℤ × Nat) (maddrs' : List ℤ) (t' : VmTrace)
    (hgrad : graduable d = true)
    (hf : Satisfied2Faithful permOut hash (v3Of d (sitesFit_admitted (graduable_spec (graduable_rotateV3 hgrad)).2.1)) minit mfin maddrs t)
    (hf' : Satisfied2Faithful permOut hash (v3Of d (sitesFit_admitted (graduable_spec (graduable_rotateV3 hgrad)).2.1)) minit' mfin' maddrs' t')
    (k l : Nat) (hk : k < t.rows.length) (hl : l < t'.rows.length)
    (hlast : (k + 1 == t.rows.length) = true) (hlast' : (l + 1 == t'.rows.length) = true)
    (hcCanonCav : 0 ≤ (envAt t k).loc (d.traceWidth + CAVEAT_REGION_OFF + C_COMMIT)
        ∧ (envAt t k).loc (d.traceWidth + CAVEAT_REGION_OFF + C_COMMIT) < 2013265921)
    (hcCanonCav' : 0 ≤ (envAt t' l).loc (d.traceWidth + CAVEAT_REGION_OFF + C_COMMIT)
        ∧ (envAt t' l).loc (d.traceWidth + CAVEAT_REGION_OFF + C_COMMIT) < 2013265921)
    (hrc : rcAt (d.traceWidth + CAVEAT_REGION_OFF) (envAt t k).loc
        ≠ rcAt (d.traceWidth + CAVEAT_REGION_OFF) (envAt t' l).loc) :
    (envAt t k).pub (d.piCount + 3) ≠ (envAt t' l).pub (d.piCount + 3) := fun hpubCav =>
  hrc (rotV3_caveat_binds_manifest_and_rc permOut hash hCR d minit mfin maddrs t
    minit' mfin' maddrs' t' hgrad hf hf' k l hk hl hlast hlast' hpubCav
    hcCanonCav hcCanonCav').2

set_option maxHeartbeats 1600000 in
/-- **THE END-TO-END KEYSTONE — once, for all 26.** Two `Satisfied2` witnesses of ANY cohort
member's rotated graduation publishing the SAME rotated OLD commit, the SAME rotated NEW
commit, and the SAME caveat commit agree on the WHOLE rotated before block, the WHOLE after
block (all 24 registers — balance/nonce included by the welds — every map root, lifecycle,
epoch, height), BOTH iroots, the published height, the WHOLE caveat manifest (every
entry's type tag, DOMAIN TAG, KEY, params) **AND the 4-felt DFA ROUTE-COMMITMENT CARRIER** —
under the ONE CR floor, via the PARAMETRIC `wireCommitR_binds` / `caveatCommitRc_binds`.

⚑ The rc conjunct is the rc-FOLD flag day's payload. Before it, the route commitment was outside
every binding: two witnesses could publish the same caveat commit and carry DIFFERENT rc, so the
`withDfaRcPins` PI exposure attested nothing a light client could use. -/
theorem rotV3_binds_published (permOut : List ℤ → List ℤ) (hash : List ℤ → ℤ)
    (hCR : Poseidon2SpongeCR hash)
    (d : EffectVmDescriptor)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (minit' : ℤ → ℤ) (mfin' : ℤ → ℤ × Nat) (maddrs' : List ℤ) (t' : VmTrace)
    (hgrad : graduable d = true)
    (hf : Satisfied2Faithful permOut hash (v3Of d (sitesFit_admitted (graduable_spec (graduable_rotateV3 hgrad)).2.1)) minit mfin maddrs t)
    (hf' : Satisfied2Faithful permOut hash (v3Of d (sitesFit_admitted (graduable_spec (graduable_rotateV3 hgrad)).2.1)) minit' mfin' maddrs' t')
    (i j : Nat) (hi : i < t.rows.length) (hj : j < t'.rows.length)
    (hfirst : (i == 0) = true) (hfirst' : (j == 0) = true)
    (k l : Nat) (hk : k < t.rows.length) (hl : l < t'.rows.length)
    (hlast : (k + 1 == t.rows.length) = true) (hlast' : (l + 1 == t'.rows.length) = true)
    (hpubOld : (envAt t i).pub d.piCount = (envAt t' j).pub d.piCount)
    (hpubNew : (envAt t k).pub (d.piCount + 1) = (envAt t' l).pub (d.piCount + 1))
    (hpubCav : (envAt t k).pub (d.piCount + 3) = (envAt t' l).pub (d.piCount + 3))
    -- The digest/PI carriers are field-canonical (`0 ≤ · < p`, the deployed range-check invariant):
    -- lifts each mod-`p` commit/height pin to the genuine ℤ hash-output equality the CR floor needs.
    (hcCanonOld : 0 ≤ (envAt t i).loc (d.traceWidth + B_STATE_COMMIT)
        ∧ (envAt t i).loc (d.traceWidth + B_STATE_COMMIT) < 2013265921)
    (hcCanonOld' : 0 ≤ (envAt t' j).loc (d.traceWidth + B_STATE_COMMIT)
        ∧ (envAt t' j).loc (d.traceWidth + B_STATE_COMMIT) < 2013265921)
    (hcCanonNew : 0 ≤ (envAt t k).loc (d.traceWidth + B_SPAN + B_STATE_COMMIT)
        ∧ (envAt t k).loc (d.traceWidth + B_SPAN + B_STATE_COMMIT) < 2013265921)
    (hcCanonNew' : 0 ≤ (envAt t' l).loc (d.traceWidth + B_SPAN + B_STATE_COMMIT)
        ∧ (envAt t' l).loc (d.traceWidth + B_SPAN + B_STATE_COMMIT) < 2013265921)
    (hhCanon : 0 ≤ (envAt t k).pub (d.piCount + 2)
        ∧ (envAt t k).pub (d.piCount + 2) < 2013265921)
    (hhCanon' : 0 ≤ (envAt t' l).pub (d.piCount + 2)
        ∧ (envAt t' l).pub (d.piCount + 2) < 2013265921)
    (hcCanonCav : 0 ≤ (envAt t k).loc (d.traceWidth + CAVEAT_REGION_OFF + C_COMMIT)
        ∧ (envAt t k).loc (d.traceWidth + CAVEAT_REGION_OFF + C_COMMIT) < 2013265921)
    (hcCanonCav' : 0 ≤ (envAt t' l).loc (d.traceWidth + CAVEAT_REGION_OFF + C_COMMIT)
        ∧ (envAt t' l).loc (d.traceWidth + CAVEAT_REGION_OFF + C_COMMIT) < 2013265921) :
    (preLimbsAt d.traceWidth (envAt t i).loc = preLimbsAt d.traceWidth (envAt t' j).loc
      ∧ (envAt t i).loc (d.traceWidth + B_IROOT) = (envAt t' j).loc (d.traceWidth + B_IROOT))
    ∧ (preLimbsAt (d.traceWidth + B_SPAN) (envAt t k).loc
        = preLimbsAt (d.traceWidth + B_SPAN) (envAt t' l).loc
      ∧ (envAt t k).loc (d.traceWidth + B_SPAN + B_IROOT) = (envAt t' l).loc (d.traceWidth + B_SPAN + B_IROOT)
      ∧ (envAt t k).pub (d.piCount + 2) = (envAt t' l).pub (d.piCount + 2))
    ∧ (manifestAt (d.traceWidth + CAVEAT_REGION_OFF) (envAt t k).loc
        = manifestAt (d.traceWidth + CAVEAT_REGION_OFF) (envAt t' l).loc
      ∧ rcAt (d.traceWidth + CAVEAT_REGION_OFF) (envAt t k).loc
        = rcAt (d.traceWidth + CAVEAT_REGION_OFF) (envAt t' l).loc) := by
  have hp := rotV3_pins permOut hash d minit mfin maddrs t hgrad hf
  have hp' := rotV3_pins permOut hash d minit' mfin' maddrs' t' hgrad hf'
  have hq := rotV3_publishes permOut hash d minit mfin maddrs t hgrad hf
  have hq' := rotV3_publishes permOut hash d minit' mfin' maddrs' t' hgrad hf'
  refine ⟨?_, ?_, ?_⟩
  · -- the before block, via the first-row pins
    have hc := (hq i hi).1 hfirst
    have hc' := (hq' j hj).1 hfirst'
    -- Lift the two OLD-commit pins to a genuine ℤ equality of the digest carriers via canonicality:
    --   loc(SC)(i) ≡ pub(pc)(i) = pub(pc)(j) ≡ loc(SC)(j).
    have hcEq : (envAt t i).loc (d.traceWidth + B_STATE_COMMIT)
        = (envAt t' j).loc (d.traceWidth + B_STATE_COMMIT) :=
      canon_eq_of_modEq hcCanonOld hcCanonOld'
        (calc (envAt t i).loc (d.traceWidth + B_STATE_COMMIT)
              ≡ (envAt t i).pub d.piCount [ZMOD 2013265921] := hc
          _ = (envAt t' j).pub d.piCount := hpubOld
          _ ≡ (envAt t' j).loc (d.traceWidth + B_STATE_COMMIT) [ZMOD 2013265921] := hc'.symm)
    have hwire : wireCommitR hash (preLimbsAt d.traceWidth (envAt t i).loc)
        ((envAt t i).loc (d.traceWidth + B_IROOT))
        = wireCommitR hash (preLimbsAt d.traceWidth (envAt t' j).loc)
            ((envAt t' j).loc (d.traceWidth + B_IROOT)) := by
      rw [← (hp i hi).1, ← (hp' j hj).1]
      show (envAt t i).loc (d.traceWidth + B_STATE_COMMIT)
        = (envAt t' j).loc (d.traceWidth + B_STATE_COMMIT)
      exact hcEq
    exact wireCommitR_binds hash hCR
      (by rw [preLimbsAt_length, preLimbsAt_length]) hwire
  · -- the after block, via the last-row pins
    obtain ⟨hc, hh, -⟩ := (hq k hk).2 hlast
    obtain ⟨hc', hh', -⟩ := (hq' l hl).2 hlast'
    have hcEq : (envAt t k).loc (d.traceWidth + B_SPAN + B_STATE_COMMIT)
        = (envAt t' l).loc (d.traceWidth + B_SPAN + B_STATE_COMMIT) :=
      canon_eq_of_modEq hcCanonNew hcCanonNew'
        (calc (envAt t k).loc (d.traceWidth + B_SPAN + B_STATE_COMMIT)
              ≡ (envAt t k).pub (d.piCount + 1) [ZMOD 2013265921] := hc
          _ = (envAt t' l).pub (d.piCount + 1) := hpubNew
          _ ≡ (envAt t' l).loc (d.traceWidth + B_SPAN + B_STATE_COMMIT) [ZMOD 2013265921] := hc'.symm)
    have hwire : wireCommitR hash (preLimbsAt (d.traceWidth + B_SPAN) (envAt t k).loc)
        ((envAt t k).loc (d.traceWidth + B_SPAN + B_IROOT))
        = wireCommitR hash (preLimbsAt (d.traceWidth + B_SPAN) (envAt t' l).loc)
            ((envAt t' l).loc (d.traceWidth + B_SPAN + B_IROOT)) := by
      rw [← (hp k hk).2.1, ← (hp' l hl).2.1]
      show (envAt t k).loc (d.traceWidth + B_SPAN + B_STATE_COMMIT)
        = (envAt t' l).loc (d.traceWidth + B_SPAN + B_STATE_COMMIT)
      exact hcEq
    obtain ⟨hpre, hir⟩ := wireCommitR_binds hash hCR
      (by rw [preLimbsAt_length, preLimbsAt_length]) hwire
    refine ⟨hpre, hir, ?_⟩
    -- the published heights agree: pub(pc+2)(k) ≡ loc(CH)(k) = loc(CH)(l) ≡ pub(pc+2)(l), lifted
    -- to ℤ by the PI-slot canonicality; the loc(CH) equality is the height limb of the bound block.
    have hHtEq : (envAt t k).loc (d.traceWidth + B_SPAN + B_COMMITTED_HEIGHT)
        = (envAt t' l).loc (d.traceWidth + B_SPAN + B_COMMITTED_HEIGHT) :=
      congrArg (fun L => L.getD 31 0) hpre
    exact canon_eq_of_modEq hhCanon hhCanon'
      (calc (envAt t k).pub (d.piCount + 2)
            ≡ (envAt t k).loc (d.traceWidth + B_SPAN + B_COMMITTED_HEIGHT) [ZMOD 2013265921] := hh.symm
        _ = (envAt t' l).loc (d.traceWidth + B_SPAN + B_COMMITTED_HEIGHT) := hHtEq
        _ ≡ (envAt t' l).pub (d.piCount + 2) [ZMOD 2013265921] := hh')
  · -- the caveat manifest AND the route-commitment carrier, via the last-row pin
    exact rotV3_caveat_binds_manifest_and_rc permOut hash hCR d minit mfin maddrs t
      minit' mfin' maddrs' t' hgrad hf hf' k l hk hl hlast hlast' hpubCav
      hcCanonCav hcCanonCav'

#assert_axioms rotV3_sound_v1
#assert_axioms rotV3_pins
#assert_axioms rotV3_publishes
#assert_axioms rotV3_caveat_binds_manifest_and_rc
#assert_axioms rotV3_moved_rc_moves_the_published_caveat_commit
#assert_axioms rotV3_binds_published

/-! ## §4½ — ⚑ THE FLOOR-FREE PUBLISHED-COMMITMENT BINDING (Site 2 of the weld de-vacuuming).

`rotV3_binds_published` binds the published PIs to the decoded kernel limbs under `hCR :
Poseidon2SpongeCR hash`, which `Circuit.HashFloorHonesty.poseidon2SpongeCR_false_babyBear` PROVES
FALSE at deployed BabyBear width — so at the deployed hash it is a true-but-empty implication, and so
is every rung above it (`descriptorRefines`, the per-effect refinement, the apex): "a Mina settlement
today certifies the AIR's arithmetic, not that a dregg turn happened."

`rotV3_before_binds_or_collides` is the OLD-state-commitment half restated WITHOUT the floor, by the
same `_binds_or_collides` idiom the map leaf received and the faithful 8-felt commitment already
carries: two `Satisfied2Faithful` witnesses of ANY rotated cohort member (transfer INCLUDED — the
"once, for all 26" keystone above is stated at the same `d`) publishing the SAME rotated OLD commit
EITHER agree on the whole rotated before block AND its iroot, OR EXHIBIT a genuine collision of the
deployed sponge at the two distinct limb lists `wireCommitRFind` returns. NO hypothesis on `hash`.
This is what makes "Mina verified the proof" mean "a dregg turn happened, OR the prover found a
Poseidon2 collision" — a satisfiable antecedent at the deployed hash, with the crypto residual named
in the conclusion rather than assumed away in a refuted premise.

BOTH POLARITIES, FLOOR-FREE (no `Function.Injective hash`, which is the refuted CR floor inj-spelled):
`rotV3_before_forgery_exhibits_collision` is the forged pole — a forged OLD commitment that publishes
the same digest on a DIFFERENT before-block is refused UNLESS the prover HANDS BACK a genuine sponge
collision; and `WireCommitBindsOrCollides.wireCommitRColl_refutable_on_agreement` is the refutability
canary — on agreeing claims the residual is FALSE, so the disjunction is not a free `True`. The honest
pole is that `rotV3_before_binds_or_collides` is UNCONDITIONAL: an honest trace whose limbs match lands
in the left disjunct with no hypothesis at all. -/
theorem rotV3_before_binds_or_collides (permOut : List ℤ → List ℤ) (hash : List ℤ → ℤ)
    (d : EffectVmDescriptor)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (minit' : ℤ → ℤ) (mfin' : ℤ → ℤ × Nat) (maddrs' : List ℤ) (t' : VmTrace)
    (hgrad : graduable d = true)
    (hf : Satisfied2Faithful permOut hash (v3Of d (sitesFit_admitted (graduable_spec (graduable_rotateV3 hgrad)).2.1)) minit mfin maddrs t)
    (hf' : Satisfied2Faithful permOut hash (v3Of d (sitesFit_admitted (graduable_spec (graduable_rotateV3 hgrad)).2.1)) minit' mfin' maddrs' t')
    (i j : Nat) (hi : i < t.rows.length) (hj : j < t'.rows.length)
    (hfirst : (i == 0) = true) (hfirst' : (j == 0) = true)
    (hpubOld : (envAt t i).pub d.piCount = (envAt t' j).pub d.piCount)
    (hcCanonOld : 0 ≤ (envAt t i).loc (d.traceWidth + B_STATE_COMMIT)
        ∧ (envAt t i).loc (d.traceWidth + B_STATE_COMMIT) < 2013265921)
    (hcCanonOld' : 0 ≤ (envAt t' j).loc (d.traceWidth + B_STATE_COMMIT)
        ∧ (envAt t' j).loc (d.traceWidth + B_STATE_COMMIT) < 2013265921) :
    (preLimbsAt d.traceWidth (envAt t i).loc = preLimbsAt d.traceWidth (envAt t' j).loc
      ∧ (envAt t i).loc (d.traceWidth + B_IROOT) = (envAt t' j).loc (d.traceWidth + B_IROOT))
    ∨ WireColl1 hash (preLimbsAt d.traceWidth (envAt t i).loc)
        ((envAt t i).loc (d.traceWidth + B_IROOT))
        (preLimbsAt d.traceWidth (envAt t' j).loc)
        ((envAt t' j).loc (d.traceWidth + B_IROOT)) := by
  have hp := rotV3_pins permOut hash d minit mfin maddrs t hgrad hf
  have hp' := rotV3_pins permOut hash d minit' mfin' maddrs' t' hgrad hf'
  have hq := rotV3_publishes permOut hash d minit mfin maddrs t hgrad hf
  have hq' := rotV3_publishes permOut hash d minit' mfin' maddrs' t' hgrad hf'
  have hc := (hq i hi).1 hfirst
  have hc' := (hq' j hj).1 hfirst'
  have hcEq : (envAt t i).loc (d.traceWidth + B_STATE_COMMIT)
      = (envAt t' j).loc (d.traceWidth + B_STATE_COMMIT) :=
    canon_eq_of_modEq hcCanonOld hcCanonOld'
      (calc (envAt t i).loc (d.traceWidth + B_STATE_COMMIT)
            ≡ (envAt t i).pub d.piCount [ZMOD 2013265921] := hc
        _ = (envAt t' j).pub d.piCount := hpubOld
        _ ≡ (envAt t' j).loc (d.traceWidth + B_STATE_COMMIT) [ZMOD 2013265921] := hc'.symm)
  have hwire : wireCommitR hash (preLimbsAt d.traceWidth (envAt t i).loc)
      ((envAt t i).loc (d.traceWidth + B_IROOT))
      = wireCommitR hash (preLimbsAt d.traceWidth (envAt t' j).loc)
          ((envAt t' j).loc (d.traceWidth + B_IROOT)) := by
    rw [← (hp i hi).1, ← (hp' j hj).1]
    show (envAt t i).loc (d.traceWidth + B_STATE_COMMIT)
      = (envAt t' j).loc (d.traceWidth + B_STATE_COMMIT)
    exact hcEq
  exact wireCommitR_binds_or_collides hash
    (by rw [preLimbsAt_length, preLimbsAt_length]) hwire

/-- **FORGED POLE, FLOOR-FREE.** Two `Satisfied2Faithful` witnesses of the same cohort member that
publish the SAME rotated OLD commit but whose decoded before-blocks DIFFER (`hne`) HAND BACK a genuine
collision of the deployed sponge — a forged OLD commitment on different limbs is refused unless the
prover exhibits a real `SpongeColl`. No hypothesis on `hash`: the left disjunct of
`rotV3_before_binds_or_collides` is excluded by `hne`, leaving the residual. -/
theorem rotV3_before_forgery_exhibits_collision (permOut : List ℤ → List ℤ) (hash : List ℤ → ℤ)
    (d : EffectVmDescriptor)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (minit' : ℤ → ℤ) (mfin' : ℤ → ℤ × Nat) (maddrs' : List ℤ) (t' : VmTrace)
    (hgrad : graduable d = true)
    (hf : Satisfied2Faithful permOut hash (v3Of d (sitesFit_admitted (graduable_spec (graduable_rotateV3 hgrad)).2.1)) minit mfin maddrs t)
    (hf' : Satisfied2Faithful permOut hash (v3Of d (sitesFit_admitted (graduable_spec (graduable_rotateV3 hgrad)).2.1)) minit' mfin' maddrs' t')
    (i j : Nat) (hi : i < t.rows.length) (hj : j < t'.rows.length)
    (hfirst : (i == 0) = true) (hfirst' : (j == 0) = true)
    (hpubOld : (envAt t i).pub d.piCount = (envAt t' j).pub d.piCount)
    (hcCanonOld : 0 ≤ (envAt t i).loc (d.traceWidth + B_STATE_COMMIT)
        ∧ (envAt t i).loc (d.traceWidth + B_STATE_COMMIT) < 2013265921)
    (hcCanonOld' : 0 ≤ (envAt t' j).loc (d.traceWidth + B_STATE_COMMIT)
        ∧ (envAt t' j).loc (d.traceWidth + B_STATE_COMMIT) < 2013265921)
    (hne : ¬ (preLimbsAt d.traceWidth (envAt t i).loc = preLimbsAt d.traceWidth (envAt t' j).loc
      ∧ (envAt t i).loc (d.traceWidth + B_IROOT) = (envAt t' j).loc (d.traceWidth + B_IROOT))) :
    WireColl1 hash (preLimbsAt d.traceWidth (envAt t i).loc)
        ((envAt t i).loc (d.traceWidth + B_IROOT))
        (preLimbsAt d.traceWidth (envAt t' j).loc)
        ((envAt t' j).loc (d.traceWidth + B_IROOT)) := by
  rcases rotV3_before_binds_or_collides permOut hash d minit mfin maddrs t minit' mfin' maddrs' t'
    hgrad hf hf' i j hi hj hfirst hfirst' hpubOld hcCanonOld hcCanonOld' with hbind | hcoll
  · exact absurd hbind hne
  · exact hcoll

#assert_axioms rotV3_before_binds_or_collides
#assert_axioms rotV3_before_forgery_exhibits_collision

/-! ## §5 — the v3 registry: all 27 v2-cohort members (+ the 8 widened), rotated. -/

/-- Append v2-native extras (map ops / mem ops / lookups) to a rotated graduation —
the attenuate phase-B leg and the dynamic setField ride through unchanged. -/
def v3OfWith (d : EffectVmDescriptor) (extras : List VmConstraint2)
    (hAdm : ∀ s ∈ (rotateV3 d).hashSites,
        ChipArityAdmitted s.inputs.length := by graduate_arity) : EffectVmDescriptor2 :=
  { v3Of d hAdm with constraints := (v3Of d hAdm).constraints ++ extras }

/-- The graduated cap-WRITE rotated descriptor (cap-root weld DROPPED — the rotated cap-root limb is
witness-carried, note-spend-shaped). -/
def v3OfCapWrite (d : EffectVmDescriptor)
    (hAdm : ∀ s ∈ (rotateV3CapWrite d).hashSites,
        ChipArityAdmitted s.inputs.length := by graduate_arity) :
    EffectVmDescriptor2 :=
  graduateV1 (rotateV3CapWrite d) hAdm

/-- Append v2-native extras (the cap-crown ROTATED-limb write leg) to a cap-WRITE rotated graduation. As
`v3OfWith` but over `rotateV3CapWrite` — the cap-root advance lives on the rotated limb (`insertWriteOpRot`/
`removeWriteOpRot`), escaping the v1-state continuity collision. -/
def v3OfWithCapWrite (d : EffectVmDescriptor) (extras : List VmConstraint2)
    (hAdm : ∀ s ∈ (rotateV3CapWrite d).hashSites,
        ChipArityAdmitted s.inputs.length := by graduate_arity) : EffectVmDescriptor2 :=
  { v3OfCapWrite d hAdm with constraints := (v3OfCapWrite d hAdm).constraints ++ extras }

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
  , piCount     := pi.V1_PI_COUNT
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
  , root    := fun _ => .var (sbCol state.CAP_ROOT)
  , key     := .var (prmCol CAP_KEY)
  , value   := .var (prmCol KEEP_MASK)
  , newRoot := fun _ => .var (saCol state.CAP_ROOT)
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

/-- The rotated AFTER-block `cap_root` limb column (limb 25 of the after block at `base = w + B_SPAN`). The
deployed cap accumulator's POST root — the write-gate's `newRoot`, witness-carried (no v1-state continuity). -/
def afterCapRootCol (w : Nat) : Nat := w + B_SPAN + B_CAP_ROOT

/-! ### v10 — the FAITHFUL 8-felt cap-root column GROUP + the native-`node8` write relation `writesTo8`.

The scalar `writesTo` on the lane-0 cap-root limb (`beforeCapRootCol`/`afterCapRootCol`, limb 25) is only
the ~31-bit lane-0 PROJECTION of the deployed 8-felt cap root. v10 commits the FULL 8-felt root: limb 25
(lane 0) ‖ the seven completion limbs 52..58 (lanes 1..7) — both blocks — absorbed into the wide state
commit. The GROUP readers below pin those eight columns to a `Digest8`; `writesTo8` is the native
arity-16 `node8` UPDATE-AT-KEY over the FULL 8-felt root (`recomposeUp8`, ~124-bit), NEVER a lane-0
squeeze (the soundness downgrade the GENTIAN tooth closes). The anti-forge tooth is the recompose
binding (`recomposeUp8_binds_or_collides`): a forged high-felt post-root forces a different post-leaf,
unless the deployed chip collides at the two `node8` blocks the walk hands back. -/

/-- The cap-root 8-felt column at lane `i` in the block based at `blockBase` (limb `B_CAP_ROOT` = 25 for
lane 0; the seven completion limbs 52..58 for lanes 1..7). `blockBase = w` (BEFORE) / `w + B_SPAN` (AFTER). -/
def capRootGroupCol (blockBase : Nat) (i : Fin 8) : Nat :=
  blockBase + layoutGroupCol .cap i

/-- The BEFORE-block 8-felt cap-root digest read off the row env (lane 0 = `beforeCapRootCol`). -/
def beforeCapRootCols (env : VmRowEnv) : Digest8 :=
  fun i => env.loc (capRootGroupCol EFFECT_VM_WIDTH i)

/-- The AFTER-block 8-felt cap-root digest read off the row env (lane 0 = `afterCapRootCol`). -/
def afterCapRootCols (env : VmRowEnv) : Digest8 :=
  fun i => env.loc (capRootGroupCol (EFFECT_VM_WIDTH + B_SPAN) i)

/-- Lane 0 of the BEFORE group IS the existing scalar cap-root limb (the projection the scalar `writesTo`
forces) — so the 8-felt relation REFINES the lane-0 write rather than replacing it. -/
theorem beforeCapRootCols_lane0 (env : VmRowEnv) :
    beforeCapRootCols env 0 = env.loc (beforeCapRootCol EFFECT_VM_WIDTH) := by
  rfl

/-- Lane 0 of the AFTER group IS the existing scalar post cap-root limb. -/
theorem afterCapRootCols_lane0 (env : VmRowEnv) :
    afterCapRootCols env 0 = env.loc (afterCapRootCol EFFECT_VM_WIDTH) := by
  rfl

/-- **`writesTo8 S8 oldRoot k v newRoot`** — the native-`node8` cap-tree UPDATE-AT-KEY over the FULL
8-felt root: some sibling/direction `path` recomposes `oldRoot` from a leaf keyed `k`, and recomposes
`newRoot` from the in-place-narrowed leaf (same key `k`, rights felt `v`) along the SAME path. The
faithful 8-felt twin of the scalar `writesTo` (which is the lane-0 projection); the `(k,v) ↔ CapLeaf`
other-field encoding is the named faithful-encoding residual the cap-family consumers carry. -/
def writesTo8 (S8 : Cap8Scheme) (oldRoot : Digest8) (k v : ℤ) (newRoot : Digest8) : Prop :=
  ∃ (oldLeaf newLeaf : CapLeaf) (path : List (StepG Digest8)),
    oldLeaf.slot_hash = k ∧ newLeaf.slot_hash = k ∧ newLeaf.mask_lo = v ∧
    recomposeUp8 S8 (capLeafDigest8 S8 oldLeaf) path = oldRoot ∧
    recomposeUp8 S8 (capLeafDigest8 S8 newLeaf) path = newRoot

/-! ⚑ The bare `writesTo8_forces_postleaf_or_collides` disjunction that stood here is DELETED: at
deployed BabyBear parameters a chip collision EXISTS by pigeonhole, so `binds ∨ collides` is
satisfiable through its RIGHT branch without the tooth ever biting — it quantified over SOLUTIONS,
where hardness quantifies over EFFICIENT ADVERSARIES. Its extraction spine
(`DeployedCapTree.Cap8Scheme.recomposeUp8_binds_or_collides` + `recomposeUp8Find`) REMAINS as the
reduction-internal witness. The EXPORTED successor is `writesTo8_forces_postleaf_rom` (§WALK-ROM
below): the same-path walk equivocation as a keyed-ROM game, closed from the PROVED birthday floor
via the walking extractor of `Crypto.RomMerkleOpening`. -/

/-! ### v10 — the FAITHFUL 8-felt HEAP-root column GROUP + the native-`node8` heap-write relation
`heapWritesTo8` (the SECOND faithful root, the exact twin of the cap-root group above).

The scalar heap `writesTo` on the lane-0 heap-root limb (limb `B_HEAP_ROOT = 28`) is only the ~31-bit
lane-0 PROJECTION of the deployed 8-felt heap root. v10 commits the FULL 8-felt root: limb 28 (lane 0) ‖
the seven completion limbs 59..65 (lanes 1..7) — both blocks — absorbed into the wide state commit. The
GROUP readers below pin those eight columns to a `Digest8`; `heapWritesTo8` is the native arity-16 `node8`
UPDATE-AT-KEY over the FULL 8-felt heap root (`Heap8Scheme.recomposeUp8`, ~124-bit), NEVER a lane-0 squeeze
(the soundness downgrade the heap GENTIAN tooth closes). The anti-forge tooth is the recompose injectivity
(`recomposeUp8_inj_of_path`): a forged high-felt post-root forces a different post-leaf. -/

/-- The heap-root limb in the rotated block (the fourth faithful-root limb, after `cap_root`=25,
`nullifier_root`=26, `commitments_root`=27). Lane 0 of the 8-felt heap-root group. -/
def B_HEAP_ROOT : Nat := layoutGroupCol .heap 0

/-- The BEFORE-block scalar heap-root column (lane 0 = limb `B_HEAP_ROOT` = 28). -/
def beforeHeapRootCol (w : Nat) : Nat := w + B_HEAP_ROOT

/-- The AFTER-block scalar heap-root column. -/
def afterHeapRootCol (w : Nat) : Nat := w + B_SPAN + B_HEAP_ROOT

/-- The heap-root 8-felt column at lane `i` in the block based at `blockBase` (limb `B_HEAP_ROOT` = 28 for
lane 0; the seven completion limbs 59..65 for lanes 1..7 — the cap completions 52..58 shifted by 7). The
cap/heap/fields groups SHARE the ONE `node8` lane by design; heap's completions sit ABOVE cap's. -/
def heapRootGroupCol (blockBase : Nat) (i : Fin 8) : Nat :=
  blockBase + layoutGroupCol .heap i

/-- The BEFORE-block 8-felt heap-root digest read off the row env (lane 0 = `beforeHeapRootCol`). -/
def beforeHeapRootCols (env : VmRowEnv) : Digest8 :=
  fun i => env.loc (heapRootGroupCol EFFECT_VM_WIDTH i)

/-- The AFTER-block 8-felt heap-root digest read off the row env (lane 0 = `afterHeapRootCol`). -/
def afterHeapRootCols (env : VmRowEnv) : Digest8 :=
  fun i => env.loc (heapRootGroupCol (EFFECT_VM_WIDTH + B_SPAN) i)

/-! ### `MapOp.root`/`newRoot` 8-felt groups (Phase H-HEAP-8 / the cap-analog emit widening).

`MapOp.root`/`newRoot` are now `Fin 8 → EmittedExpr` (matching the deployed Rust `MapOpSpec` `[8]`).
For the 8-felt-WELDED families (cap · heap) the group IS the real `…RootGroupCol` lanes (lane 0 the
scalar limb, lanes 1..7 the completion limbs) — the deployed `map_ops` chip recomposes the faithful
~124-bit root and the after-spine keystone (`CapOpenEmit` / `HeapOpenEmit`) trace-forces it. For a
family NOT yet 8-felt-welded (`nullifier` · `commitments` · `cells` · `fields`, until its own
campaign) the group is the scalar limb CARRIED across all 8 lanes (`scalarRootGroup`) — the root is
still a single ~31-bit felt, denotation is lane 0, and no keystone forces the extra lanes. -/

/-- The BEFORE-block cap-root 8-felt column group (lane 0 = `beforeCapRootCol`, lanes 1..7 the cap
completion limbs 52..58). -/
def beforeCapRootGroup : Fin 8 → EmittedExpr := fun i => .var (capRootGroupCol EFFECT_VM_WIDTH i)

/-- The AFTER-block cap-root 8-felt column group (lane 0 = `afterCapRootCol`). -/
def afterCapRootGroup : Fin 8 → EmittedExpr := fun i => .var (capRootGroupCol (EFFECT_VM_WIDTH + B_SPAN) i)

/-- The BEFORE-block heap-root 8-felt column group (lane 0 = `beforeHeapRootCol`, lanes 1..7 the heap
completion limbs 59..65). -/
def beforeHeapRootGroup : Fin 8 → EmittedExpr := fun i => .var (heapRootGroupCol EFFECT_VM_WIDTH i)

/-- The AFTER-block heap-root 8-felt column group (lane 0 = `afterHeapRootCol`). -/
def afterHeapRootGroup : Fin 8 → EmittedExpr := fun i => .var (heapRootGroupCol (EFFECT_VM_WIDTH + B_SPAN) i)

/-- A not-yet-8-felt-welded root as a `MapOp` group: the scalar limb `col` carried across all 8
lanes (denotation is lane 0; no after-spine keystone forces lanes 1..7 — the root stays ~31-bit
until that family's own weld). -/
def scalarRootGroup (col : Nat) : Fin 8 → EmittedExpr := fun _ => .var col

/-- Lane 0 of the BEFORE heap group IS the existing scalar heap-root limb (the projection the scalar
`writesTo` forces) — the 8-felt relation REFINES the lane-0 write rather than replacing it. -/
theorem beforeHeapRootCols_lane0 (env : VmRowEnv) :
    beforeHeapRootCols env 0 = env.loc (beforeHeapRootCol EFFECT_VM_WIDTH) := by
  rfl

/-- Lane 0 of the AFTER heap group IS the existing scalar post heap-root limb. -/
theorem afterHeapRootCols_lane0 (env : VmRowEnv) :
    afterHeapRootCols env 0 = env.loc (afterHeapRootCol EFFECT_VM_WIDTH) := by
  rfl

/-- **`heapWritesTo8 S8 oldRoot k v newRoot`** — the native-`node8` heap-tree UPDATE-AT-KEY over the FULL
8-felt root: some sibling/direction `path` recomposes `oldRoot` from the LINKED heap leaf
`(k, oldVal, next)`, and recomposes `newRoot` from the in-place-updated leaf `(k, v, next)` along the
SAME path with the SAME pointer (a value update HOLDS the IMT `nextAddr` fixed — it never re-links the
sorted chain; `heap_root.rs::apply_value_update`). The faithful 8-felt twin of the scalar heap
`writesTo`. Heap leaves are the gap-#5 IMT `(addr, value, nextAddr)`, so the key IS the address and
the written value is the leaf's second field — no `CapLeaf` re-encoding residual. -/
def heapWritesTo8 (S8 : Heap8Scheme) (oldRoot : Digest8) (k v : ℤ) (newRoot : Digest8) : Prop :=
  ∃ (oldVal next : ℤ) (path : List (StepG Digest8)),
    Heap8Scheme.recomposeUp8 S8 (Heap8Scheme.heapLeafDigest8 S8 (k, oldVal, next)) path = oldRoot ∧
    Heap8Scheme.recomposeUp8 S8 (Heap8Scheme.heapLeafDigest8 S8 (k, v, next)) path = newRoot

/-- **(REDUCTION-INTERNAL extraction step — NOT an exported headline.)** Along a FIXED sibling path
the post-root EITHER pins the post-leaf digest at full ~124-bit width, OR the deployed arity-16 chip
genuinely collides at the two `node8` blocks the walk hands back. ⚑ A bare `binds ∨ collides` is a
SHIRK as a headline (a chip collision EXISTS by pigeonhole at deployed parameters) — this lemma is
KEPT (public) only because the `RotatedKernelRefinementCapFamily` refinement decodes consume it as an
extraction step inside their own carriers; the EXPORTED security headline is
`heapWritesTo8_forces_postleaf_rom` (§WALK-ROM below), closed from the PROVED birthday floor. -/
theorem heapWritesTo8_forces_postleaf_or_collides (S8 : Heap8Scheme) (path : List (StepG Digest8))
    {a b : Digest8} (h : Heap8Scheme.recomposeUp8 S8 a path = Heap8Scheme.recomposeUp8 S8 b path) :
    a = b ∨ Coll8 S8.chipAbsorb8 (Heap8Scheme.recomposeUp8Find S8 a b path) :=
  Heap8Scheme.recomposeUp8_binds_or_collides S8 path h

/-! ### v10 — the FAITHFUL 8-felt FIELDS-root column GROUP + the native-`node8` fields-write relation
`fieldsWritesTo8` (the THIRD and LAST faithful root, the exact twin of the cap/heap-root groups above).

The scalar fields `writesTo` on the lane-0 fields-root limb (limb `B_FIELDS_ROOT = 36`) is only the
~31-bit lane-0 PROJECTION of the deployed 8-felt user-field-map root. v10 commits the FULL 8-felt root:
limb 36 (lane 0) ‖ the seven completion limbs 66,67,19,20,21,22,23 (lanes 1..7 — NON-contiguous: 66,67
are past the heap completions, 19..23 are the repurposed register-headroom limbs) — both blocks —
absorbed into the wide state commit. The GROUP readers below pin those eight columns to a `Digest8`;
`fieldsWritesTo8` is the native arity-16 `node8` UPDATE-AT-KEY over the FULL 8-felt fields root
(`Fields8Scheme.recomposeUp8`, ~124-bit), NEVER a lane-0 squeeze (the soundness downgrade the fields
GENTIAN tooth `circuit/tests/fields_root_gentian_weld.rs` closes). The anti-forge tooth is the recompose
injectivity (`recomposeUp8_inj_of_path`): a forged high-felt post-root forces a different post-leaf. -/

/-- The fields-root 8-felt column at lane `i` in the block based at `blockBase`: lane 0 = limb
`B_FIELDS_ROOT` = 36; the seven completion limbs are NON-contiguous — 66,67 (past heap's 59..65) for
lanes 1,2 and the repurposed register-headroom limbs 19,20,21,22,23 for lanes 3..7. The cap/heap/fields
groups SHARE the ONE `node8` lane by design. -/
def fieldsRootGroupCol (blockBase : Nat) (i : Fin 8) : Nat :=
  blockBase + layoutGroupCol .fields i

/-- The BEFORE-block 8-felt fields-root digest read off the row env (lane 0 = limb `B_FIELDS_ROOT`=36). -/
def beforeFieldsRootCols (env : VmRowEnv) : Digest8 :=
  fun i => env.loc (fieldsRootGroupCol EFFECT_VM_WIDTH i)

/-- The AFTER-block 8-felt fields-root digest read off the row env (lane 0 at the AFTER block base). -/
def afterFieldsRootCols (env : VmRowEnv) : Digest8 :=
  fun i => env.loc (fieldsRootGroupCol (EFFECT_VM_WIDTH + B_SPAN) i)

/-- The BEFORE-block fields-root 8-felt column group (lane 0 = limb 36, lanes 1..7 the fields completion
limbs 66,67,19..23). -/
def beforeFieldsRootGroup : Fin 8 → EmittedExpr := fun i => .var (fieldsRootGroupCol EFFECT_VM_WIDTH i)

/-- The AFTER-block fields-root 8-felt column group (lane 0 at the AFTER block base). -/
def afterFieldsRootGroup : Fin 8 → EmittedExpr := fun i => .var (fieldsRootGroupCol (EFFECT_VM_WIDTH + B_SPAN) i)

/-- Lane 0 of the BEFORE fields group IS the existing scalar fields-root limb (limb `B_FIELDS_ROOT`=36),
the projection the scalar `writesTo` forces — the 8-felt relation REFINES the lane-0 write. -/
theorem beforeFieldsRootCols_lane0 (env : VmRowEnv) :
    beforeFieldsRootCols env 0 = env.loc (EFFECT_VM_WIDTH + B_FIELDS_ROOT) := by
  rfl

/-- Lane 0 of the AFTER fields group IS the existing scalar post fields-root limb. -/
theorem afterFieldsRootCols_lane0 (env : VmRowEnv) :
    afterFieldsRootCols env 0 = env.loc (EFFECT_VM_WIDTH + B_SPAN + B_FIELDS_ROOT) := by
  rfl

/-! ### v11 — the FAITHFUL 8-felt ACCUMULATOR root column GROUPS (nullifier@26 · commitments@27 ·
cells@0), the exact twins of the cap/heap/fields groups above, over the 21 NEW DEDICATED completion
limbs 68..88 (never shared with another family — a shared block would break OLD/NEW commit continuity
cross-turn). Each accumulator's genuine node8 `root8` rides lane 0 (its historical scalar limb) ‖ 7
dedicated completion limbs. The deployed Rust producer fills all 8 lanes via `CanonicalHeapTree8`, and
the map-op node8 AIR binds them lane-for-lane (deployed-faithful, ~124-bit — NEVER the lane-0 squeeze). -/

/-- The nullifier-root 8-felt column at lane `i` (lane 0 = limb `B_NULLIFIER_ROOT_OFF` = 26; the seven
DEDICATED completion limbs 68..74 for lanes 1..7). -/
def nullifierRootGroupCol (blockBase : Nat) (i : Fin 8) : Nat :=
  blockBase + layoutGroupCol .nullifier i

/-- The commitments-root 8-felt column at lane `i` (lane 0 = limb `B_COMMITMENTS_ROOT` = 27; the seven
DEDICATED completion limbs 75..81 for lanes 1..7, REVOKED-ROOT +1 shift from 74..80). -/
def commitmentsRootGroupCol (blockBase : Nat) (i : Fin 8) : Nat :=
  blockBase + layoutGroupCol .commitments i

/-- The cells-root 8-felt column at lane `i` (lane 0 = limb 0 = accounts root; the seven completion
limbs 169..175 for lanes 1..7 — RELOCATED off revoked's 82..88 by the revoked-root flag-day so the
two groups are now DISJOINT, not shared).

⚑ WOUND #23 (`docs/WOUND-felt-width-boundaries-2026-07-19.md`): this docstring used to say "the
producer leaves 169..175 zero (circuit-only completion)", and that was TRUE of both Rust producers —
which made the committed `cells_root` ONE ~31-bit felt sitting inside the faithful 8-felt consensus
anchor the executor signs and the receipt QC aggregates over. Both producers
(`rotation_witness::produce`, `commitment::compute_rotated_pre_limbs`) now write all eight lanes on
EVERY turn from the native `CanonicalHeapTree8` existence-tree root; the createCell/factory/spawn
trace generator still OVERWRITES the whole group with its own in-circuit accounts tree, which is the
object the two map-ops below actually gate. Only those three members constrain this group; on every
other member the lanes are absorbed by `wireCommitR` and gated by nothing. -/
def cellsRootGroupCol (blockBase : Nat) (i : Fin 8) : Nat :=
  blockBase + layoutGroupCol .cells i

/-- The revoked-root 8-felt column at lane `i` (lane 0 = limb `B_REVOKED_ROOT` = 37; the seven
completion limbs 82..88 for lanes 1..7 — the shifted-free slots the base widen opened). The exact
twin of `nullifierRootGroupCol` / `commitmentsRootGroupCol`; the credential-revocation accumulator's
committed faithful 8-felt root (hole #139), sourced from `V9RotationContext.revoked_root`. -/
def revokedRootGroupCol (blockBase : Nat) (i : Fin 8) : Nat :=
  blockBase + layoutGroupCol .revoked i

/-- The BEFORE/AFTER-block nullifier-root 8-felt column groups (lane 0 = the scalar limb 26). -/
def beforeNullifierRootGroup : Fin 8 → EmittedExpr :=
  fun i => .var (nullifierRootGroupCol EFFECT_VM_WIDTH i)
def afterNullifierRootGroup : Fin 8 → EmittedExpr :=
  fun i => .var (nullifierRootGroupCol (EFFECT_VM_WIDTH + B_SPAN) i)

/-- The BEFORE/AFTER-block commitments-root 8-felt column groups (lane 0 = the scalar limb 27). -/
def beforeCommitmentsRootGroup : Fin 8 → EmittedExpr :=
  fun i => .var (commitmentsRootGroupCol EFFECT_VM_WIDTH i)
def afterCommitmentsRootGroup : Fin 8 → EmittedExpr :=
  fun i => .var (commitmentsRootGroupCol (EFFECT_VM_WIDTH + B_SPAN) i)

/-- The BEFORE/AFTER-block cells-root 8-felt column groups (lane 0 = the scalar limb 0). -/
def beforeCellsRootGroup : Fin 8 → EmittedExpr :=
  fun i => .var (cellsRootGroupCol EFFECT_VM_WIDTH i)
def afterCellsRootGroup : Fin 8 → EmittedExpr :=
  fun i => .var (cellsRootGroupCol (EFFECT_VM_WIDTH + B_SPAN) i)

/-- The BEFORE/AFTER-block revoked-root 8-felt column groups (lane 0 = the scalar limb 37). -/
def beforeRevokedRootGroup : Fin 8 → EmittedExpr :=
  fun i => .var (revokedRootGroupCol EFFECT_VM_WIDTH i)
def afterRevokedRootGroup : Fin 8 → EmittedExpr :=
  fun i => .var (revokedRootGroupCol (EFFECT_VM_WIDTH + B_SPAN) i)

/-- Lane 0 of each accumulator group IS the existing scalar limb (the projection the scalar `writesTo`
forces) — the 8-felt group REFINES the lane-0 write. -/
theorem nullifierRootGroupCol_lane0 (bb : Nat) :
    nullifierRootGroupCol bb 0 = bb + B_NULLIFIER_ROOT_OFF := by rfl
theorem commitmentsRootGroupCol_lane0 (bb : Nat) :
    commitmentsRootGroupCol bb 0 = bb + B_COMMITMENTS_ROOT := by rfl
theorem cellsRootGroupCol_lane0 (bb : Nat) :
    cellsRootGroupCol bb 0 = bb + 0 := by rfl
theorem revokedRootGroupCol_lane0 (bb : Nat) :
    revokedRootGroupCol bb 0 = bb + B_REVOKED_ROOT := by rfl

/-- The BEFORE/AFTER-block 8-felt accumulator-root digests read off the row env (lane 0 = the scalar limb;
lanes 1..7 the dedicated completion limbs 68..88). The `Digest8` twins of `beforeFieldsRootCols`, one per
accumulator family — the `AccumulatorOpenEmit` after-spine keystone forces `heapWritesTo8` over exactly
these committed groups (the assurance-case reads the consumer trio quantifies over). -/
def beforeNullifierRootCols (env : VmRowEnv) : Digest8 :=
  fun i => env.loc (nullifierRootGroupCol EFFECT_VM_WIDTH i)
def afterNullifierRootCols (env : VmRowEnv) : Digest8 :=
  fun i => env.loc (nullifierRootGroupCol (EFFECT_VM_WIDTH + B_SPAN) i)
def beforeCommitmentsRootCols (env : VmRowEnv) : Digest8 :=
  fun i => env.loc (commitmentsRootGroupCol EFFECT_VM_WIDTH i)
def afterCommitmentsRootCols (env : VmRowEnv) : Digest8 :=
  fun i => env.loc (commitmentsRootGroupCol (EFFECT_VM_WIDTH + B_SPAN) i)
def beforeCellsRootCols (env : VmRowEnv) : Digest8 :=
  fun i => env.loc (cellsRootGroupCol EFFECT_VM_WIDTH i)
def afterCellsRootCols (env : VmRowEnv) : Digest8 :=
  fun i => env.loc (cellsRootGroupCol (EFFECT_VM_WIDTH + B_SPAN) i)
def beforeRevokedRootCols (env : VmRowEnv) : Digest8 :=
  fun i => env.loc (revokedRootGroupCol EFFECT_VM_WIDTH i)
def afterRevokedRootCols (env : VmRowEnv) : Digest8 :=
  fun i => env.loc (revokedRootGroupCol (EFFECT_VM_WIDTH + B_SPAN) i)

/-- **`fieldsWritesTo8 S8 oldRoot k v newRoot`** — the native-`node8` fields-tree UPDATE-AT-KEY over the
FULL 8-felt root: some sibling/direction `path` recomposes `oldRoot` from the fields leaf `(k, oldVal)`,
and recomposes `newRoot` from the in-place-updated leaf `(k, v)` along the SAME path. The faithful 8-felt
twin of the scalar fields `writesTo` (which is the lane-0 projection). Fields leaves are `(addr, value)`
(addr = `field_key_hash key`), so the key IS the address and the written value is the leaf's second
field — no re-encoding residual. -/
def fieldsWritesTo8 (S8 : Fields8Scheme) (oldRoot : Digest8) (k v : ℤ) (newRoot : Digest8) : Prop :=
  ∃ (oldVal next : ℤ) (path : List (StepG Digest8)),
    Fields8Scheme.recomposeUp8 S8 (Fields8Scheme.fieldsLeafDigest8 S8 (k, oldVal, next)) path = oldRoot ∧
    Fields8Scheme.recomposeUp8 S8 (Fields8Scheme.fieldsLeafDigest8 S8 (k, v, next)) path = newRoot

/-- **(REDUCTION-INTERNAL extraction step — NOT an exported headline.)** Along a FIXED sibling path
the post-root EITHER pins the post-leaf digest at full ~124-bit width, OR the deployed arity-16 chip
genuinely collides at the two `node8` blocks the walk hands back. ⚑ A bare `binds ∨ collides` is a
SHIRK as a headline — KEPT (public) only because `RotatedKernelRefinementCapFamily` consumes it as an
extraction step; the EXPORTED security headline is `fieldsWritesTo8_forces_postleaf_rom` (§WALK-ROM
below), closed from the PROVED birthday floor. -/
theorem fieldsWritesTo8_forces_postleaf_or_collides (S8 : Fields8Scheme) (path : List (StepG Digest8))
    {a b : Digest8}
    (h : Fields8Scheme.recomposeUp8 S8 a path = Fields8Scheme.recomposeUp8 S8 b path) :
    a = b ∨ Coll8 S8.chipAbsorb8 (Fields8Scheme.recomposeUp8Find S8 a b path) :=
  Fields8Scheme.recomposeUp8_binds_or_collides S8 path h

/-! ### §WALK-ROM — THE EXPORTED SUCCESSORS of the three `writesTo8` walk disjunctions, ON THE
PROVED KEYED-ROM FLOOR.

⚑ THE MODELLING STEP, STATED (never smuggled): the deployed arity-16 `node8` chip
(`chipAbsorb8 : List ℤ → Digest8` — ONE fixed public function shared by the cap/heap/fields trees)
is idealised as a sampled oracle `H : Unit × (Fin (2^l) × Fin (2^l)) → Fin (2^l)`; the ~124-bit
8-felt `Digest8` accumulator becomes ONE λ-bit word (there is NO `l` at which `Fin (2^l)` is the
deployed digest — the felt-width discipline, said out loud), and the ordered two-child node message
`nodeMsg` is the ROM restatement of the `node8` block pair a `StepG` walk absorbs (direction = the
index bit). The key is `Unit` because the deployed chip runs UNTAGGED — no domain-separation claim
is made or smuggled (the `vmSpongeFamily` convention). What this buys over the deleted disjunctions:
the floor under the tooth is `keyedRom_hard` (the birthday bound — a THEOREM), the forger is an
ORACLE PROGRAM, and the walking extractor PAYS its own `2·depth` queries
(`Crypto.RomMerkleOpening`'s same-context chain walk — exactly this shape: two leaf accumulators,
one SHARED sibling path, LEFT-injectivity of the step encoding). What it does not buy: any statement
about the fixed deployed chip itself (CR of a fixed public function is a conjecture, not a Lean
theorem). -/

section WalkRomSuccessor

open Dregg2.Crypto.RomMerkleOpening
open Dregg2.Crypto.RomCarrierSites (RomForgeryEff)
open Dregg2.Crypto.ConcreteSecurity (Negl PolyBounded)
open Dregg2.Crypto.FloorGames (Game Adversary gameAdv)

/-- The `node8` walk equivocation game at pinned depth `d`: the adversary outputs a shared
`(bit, sibling)` path and TWO leaf digests; it wins iff the leaves are DISTINCT yet recompose to the
SAME root along the shared path, against the sampled oracle — `recomposeUp8`'s equivocation event,
at the sampled chip. -/
abbrev node8WalkRomGame (d : ℕ → ℕ) : Game :=
  merkleOpenRomGame Unit inferInstance inferInstance ⟨()⟩ d

/-- **⚑⚑ THE GENERIC WALK BINDING, DISCHARGED** — every query-bounded forger of the `node8` recompose
walk has NEGLIGIBLE advantage (`merkleOpenRom_binds`: the walking extractor re-descends both chains,
`2·d` queries PAID, and `keyedRom_hard` closes it). NO floor hypothesis, no `Compress8CR`, no
`IsPolyTime`. -/
theorem node8Walk_binds_rom (d Q Q' : ℕ → ℕ)
    (hle : ∀ l, Q l + 2 * d l ≤ Q' l)
    (hQ' : PolyBounded (fun l => ((Q' l : ℝ) * (Q' l : ℝ) + 1)))
    (A : Adversary (node8WalkRomGame d))
    (hA : RomForgeryEff (merkleRomFamily Unit inferInstance inferInstance ⟨()⟩)
      (merkleOpenForgery Unit inferInstance inferInstance ⟨()⟩ d) Q A) :
    Negl (gameAdv (node8WalkRomGame d) A) :=
  merkleOpenRom_binds Unit inferInstance inferInstance ⟨()⟩ d Q Q' hle hQ' A hA

/-- **⚑⚑ THE CAP-TREE WALK TOOTH, DISCHARGED** — the exported successor of the deleted
`writesTo8_forces_postleaf_or_collides`: a query-bounded forger that reaches one cap post-root from
two DISTINCT post-leaf digests along one sibling path (the forged-`newRoot` shape `writesTo8`
excludes) has NEGLIGIBLE advantage in the keyed-ROM model of the §WALK-ROM header. -/
theorem writesTo8_forces_postleaf_rom (d Q Q' : ℕ → ℕ)
    (hle : ∀ l, Q l + 2 * d l ≤ Q' l)
    (hQ' : PolyBounded (fun l => ((Q' l : ℝ) * (Q' l : ℝ) + 1)))
    (A : Adversary (node8WalkRomGame d))
    (hA : RomForgeryEff (merkleRomFamily Unit inferInstance inferInstance ⟨()⟩)
      (merkleOpenForgery Unit inferInstance inferInstance ⟨()⟩ d) Q A) :
    Negl (gameAdv (node8WalkRomGame d) A) :=
  node8Walk_binds_rom d Q Q' hle hQ' A hA

/-- **⚑⚑ THE HEAP-TREE WALK TOOTH, DISCHARGED** — the exported successor of the (kept-internal)
`heapWritesTo8_forces_postleaf_or_collides` extraction step, at the SAME sampled chip (the deployed
trees share ONE `node8` lane). -/
theorem heapWritesTo8_forces_postleaf_rom (d Q Q' : ℕ → ℕ)
    (hle : ∀ l, Q l + 2 * d l ≤ Q' l)
    (hQ' : PolyBounded (fun l => ((Q' l : ℝ) * (Q' l : ℝ) + 1)))
    (A : Adversary (node8WalkRomGame d))
    (hA : RomForgeryEff (merkleRomFamily Unit inferInstance inferInstance ⟨()⟩)
      (merkleOpenForgery Unit inferInstance inferInstance ⟨()⟩ d) Q A) :
    Negl (gameAdv (node8WalkRomGame d) A) :=
  node8Walk_binds_rom d Q Q' hle hQ' A hA

/-- **⚑⚑ THE FIELDS-TREE WALK TOOTH, DISCHARGED** — the exported successor of the (kept-internal)
`fieldsWritesTo8_forces_postleaf_or_collides` extraction step, at the SAME sampled chip. -/
theorem fieldsWritesTo8_forces_postleaf_rom (d Q Q' : ℕ → ℕ)
    (hle : ∀ l, Q l + 2 * d l ≤ Q' l)
    (hQ' : PolyBounded (fun l => ((Q' l : ℝ) * (Q' l : ℝ) + 1)))
    (A : Adversary (node8WalkRomGame d))
    (hA : RomForgeryEff (merkleRomFamily Unit inferInstance inferInstance ⟨()⟩)
      (merkleOpenForgery Unit inferInstance inferInstance ⟨()⟩ d) Q A) :
    Negl (gameAdv (node8WalkRomGame d) A) :=
  node8Walk_binds_rom d Q Q' hle hQ' A hA

#assert_axioms node8Walk_binds_rom
#assert_axioms writesTo8_forces_postleaf_rom
#assert_axioms heapWritesTo8_forces_postleaf_rom
#assert_axioms fieldsWritesTo8_forces_postleaf_rom

end WalkRomSuccessor

/-- The held-capability MEMBERSHIP read on the ROTATED before-block cap-root limb (limb 25). The before
`cap_root` (rotated limb) opens at `param[CAP_KEY]` to `param[HELD_MASK]` (root unchanged — a read). The
membership-read authenticates against the SAME root the write-gate opens against. **Guarded by the per-effect
runtime selector column `s`** — the column the trace generator sets to `1` on THIS effect's active row (e.g.
`sel.REVOKE_DELEGATION = 30` for revokeDelegation). The forge close (`bd7ba0bf9`): the guard MUST be the
selector that fires on the cap-write row, else the map_op never fires and the AFTER cap-root rides unbound. -/
def heldReadOpRot (s : Nat) : MapOp :=
  { guard   := .var s
  , root    := beforeCapRootGroup
  , key     := .var (prmCol CAP_KEY)
  , value   := .var (prmCol HELD_MASK)
  , newRoot := beforeCapRootGroup
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
  , root    := beforeCapRootGroup
  , key     := .var (prmCol ANCHOR_KEY)
  , value   := .var (prmCol ANCHOR_MASK)
  , newRoot := beforeCapRootGroup
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
  , root    := beforeCapRootGroup
  , key     := .var (prmCol CAP_KEY)
  , value   := .var (prmCol KEEP_MASK)
  , newRoot := afterCapRootGroup
  , op      := .insert }

/-- The revokeDelegation REMOVE on the ROTATED limbs: the AFTER rotated cap-root is the genuine sorted
ZERO-value write (the slot REMOVE) at `param[CAP_KEY]` into the BEFORE rotated cap-root. Note-spend-shaped:
witness-carried, folds into the committed rotated state-commit, no v1-state continuity collision.
**Guarded by the per-effect runtime selector column `s`** (`sel.REVOKE_DELEGATION = 30` on the
revokeDelegation row); the forge close re-points it off the never-firing `selA.ATTENUATE = 2` so the
AFTER cap-root is GENUINELY bound to the sorted REMOVE. -/
def removeWriteOpRot (s : Nat) : MapOp :=
  { guard   := .var s
  , root    := beforeCapRootGroup
  , key     := .var (prmCol CAP_KEY)
  , value   := .const 0
  , newRoot := afterCapRootGroup
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
  , root    := beforeCapRootGroup
  , key     := .var (prmCol CAP_KEY)
  , value   := .var (prmCol KEEP_MASK)
  , newRoot := afterCapRootGroup
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
    [.lookup submaskLookup]

/-- The rotated REVOKE-CAPABILITY (sel 24): the arity-2 map-ops DROPPED (the REMOVE-shaped after-spine
deploy — mirroring `revokeDelegationWriteV3`'s remove drop). The cap-tree REMOVE is FORCED by the deployed
`effCapRemoveV3` wrap (`CapRemoveEmit.effCapRemoveV3_forces_write8`: the removed-leaf membership in BEFORE
is TRACE-FORCED over the FULL committed 8-felt cap-root groups; the AFTER root is the deployed tombstone
zero-fold `cap_root.rs::CanonicalCapTree::remove_witness` — exactly the executor's `capabilities.revoke`
tombstone semantics), not the scalar `heldReadOpRot`/`removeWriteOpRot` pair (whose arity-2 heap fold is
UNSAT against the deployed arity-7 `CanonicalCapTree` and whose scalar root left the seven high felts
unbound). NO submask — revoke deletes a slot, it does not narrow rights; NO epoch gate — revokeCapability
does not bump the delegation epoch (unlike revokeDelegation). -/
def revokeCapabilityV3 : EffectVmDescriptor2 :=
  v3OfWithCapWrite EffectVmEmitAttenuateA.attenuateVmDescriptorGenuineNoRecomputeTick []

/-- The rotated DELEGATE (the unattenuated cross-vat grant), on the ROTATED-limb write path with the
arity-2 map-ops DROPPED (the INSERT-shaped after-spine deploy): the faithful 8-felt cap-tree INSERT is
FORCED by the deployed insert-shaped cap-open wrap (`CapInsertEmit.effCapInsertV3_forces_write8` — the
spliced-leaf membership in the REBUILT AFTER tree over the FULL committed 8-felt cap-root groups), NOT
the arity-2 scalar `insertWriteOpRot` (which is UNSAT against the deployed arity-7
`CanonicalCapTree::insert_witness` — the update-at-key `writesTo` shape does not fit a fresh-key splice,
and its scalar root left the seven high felts unbound). The delegate base IS the attenuate-A moving face
(`delegateVmDescriptor := attenuateVmDescriptor`). NO submask lookup — an unattenuated delegate confers
the held edge as-is. -/
def delegateV3 : EffectVmDescriptor2 :=
  v3OfWithCapWrite EffectVmEmitAttenuateA.attenuateVmDescriptorGenuineNoRecomputeTick []

/-- The rotated DELEGATE-ATTEN (the attenuated grant): the arity-2 map-ops DROPPED (the INSERT-shaped
after-spine deploy — see `delegateV3`); ONLY the `granted ⊑ held` submask lookup (the non-amplification
tooth, REUSED from attenuate) survives. The cap-tree INSERT is FORCED by the deployed
`effCapInsertV3` wrap. Shares the moving attenuate-A face. -/
def delegateAttenV3 : EffectVmDescriptor2 :=
  v3OfWithCapWrite EffectVmEmitAttenuateA.attenuateVmDescriptorGenuineNoRecomputeTick
    [.lookup submaskLookup]

/-- The rotated GRANT-CAP (the bare cap grant): the arity-2 map-ops DROPPED (the INSERT-shaped
after-spine deploy — the cap-tree INSERT rides the deployed `effCapInsertV3` wrap, see `delegateV3`).
Shares the moving attenuate-A face (the deployed grantCap base). -/
def grantCapWriteV3 : EffectVmDescriptor2 :=
  v3OfWithCapWrite EffectVmEmitAttenuateA.attenuateVmDescriptorGenuineNoRecomputeTick []

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
introduce grants the held edge as-is (the recipient is bounded by the introducer's membership-read cap).

INSERT-shaped after-spine deploy: the arity-2 map-ops are DROPPED (mirroring `delegateV3`) — the
cap-tree INSERT is FORCED by the deployed `effCapInsertV3` wrap (`CapInsertEmit.effCapInsertV3_forces_write8`),
not the scalar `insertWriteOpRot` (UNSAT against the deployed arity-7 fresh-key splice). -/
def introduceWriteV3 : EffectVmDescriptor2 :=
  v3OfWithCapWrite EffectVmEmitAttenuateA.attenuateVmDescriptorGenuineNoRecomputeTick []

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
    env.loc afterC ≡ env.loc beforeC + 1 [ZMOD 2013265921] := by
  subst hlast
  simp only [epochBumpGate, VmConstraint.holdsVm, EmittedExpr.eval] at h
  rw [hsel] at h
  exact (gate_modEq_iff (by ring)).mp h

/-- The rotated BEFORE-block `delegation_epoch` limb column (limb 30 of the before block at `base = w`). -/
def beforeEpochCol (w : Nat) : Nat := w + B_EPOCH

/-- The rotated AFTER-block `delegation_epoch` limb column (limb 30 of the after block at `base = w + B_SPAN`). -/
def afterEpochCol (w : Nat) : Nat := w + B_SPAN + B_EPOCH

/-- The rotated REVOKE-DELEGATION on the MOVING `revokeVmDescriptorGenuine` face (no `gCapPass` freeze) WITH
the cap-crown circuit leg: held-membership read + the ZERO-value REMOVE-write (`removeWriteOp`, reused from
`revokeCapabilityV3` — revoke deletes a slot, NO submask) AND the §14.EPOCH parent-epoch BUMP gate
(`epochBumpGate` on the rotated `B_EPOCH = 30` limbs). The genuine recompute frees `cap_root`;
`epochBumpGate` FORCES the committed AFTER epoch to be the BEFORE epoch + 1 (the freshness tick that
stales every child snapshot — the `RevokeDelegationEpochResidual` `delegationEpoch += 1` clause, now
in-circuit-forced).

REMOVE-shaped after-spine deploy: the arity-2 map-ops are DROPPED (mirroring `delegateV3`'s insert
drop) — the cap-tree REMOVE is FORCED by the deployed `effCapRemoveV3` wrap
(`CapRemoveEmit.effCapRemoveV3_forces_write8`: the removed-leaf membership in BEFORE is TRACE-FORCED
over the FULL committed 8-felt cap-root groups; the AFTER root is the deployed tombstone zero-fold),
not the scalar `removeWriteOpRot` (whose update-at-key shape cannot express the ZERO-digest tombstone
leaf and whose scalar root left the seven high felts unbound). Only the §14.EPOCH bump gate survives. -/
def revokeDelegationWriteV3 : EffectVmDescriptor2 :=
  v3OfWithCapWrite EffectVmEmitAttenuateA.attenuateVmDescriptorGenuineNoRecomputeTick
    [.base (epochBumpGate sel.REVOKE_DELEGATION
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
  , root    := scalarRootGroup (beforeDelegRootCol EFFECT_VM_WIDTH)
  , key     := .var (prmCol CAP_KEY)
  , value   := .var (prmCol HELD_MASK)
  , newRoot := scalarRootGroup (beforeDelegRootCol EFFECT_VM_WIDTH)
  , op      := .read }

/-- The refreshDelegation UPDATE-AT-KEY on the ROTATED DELEG-root limbs: the AFTER rotated DELEG-root IS
the GENUINE sorted update of the recomputed snapshot (`param[KEEP_MASK]`) at the child key
(`param[CAP_KEY]`) into the BEFORE rotated DELEG-root. `.write` is insert-or-update (key already present —
an overwrite), `writesTo` FUNCTIONAL under CR — a forged after-root is UNSAT. Note-spend-shaped: the
accumulator folds into the committed rotated state-commit, no v1-state continuity collision. -/
def delegUpdateWriteOpRot (s : Nat) : MapOp :=
  { guard   := .var s
  , root    := scalarRootGroup (beforeDelegRootCol EFFECT_VM_WIDTH)
  , key     := .var (prmCol CAP_KEY)
  , value   := .var (prmCol KEEP_MASK)
  , newRoot := scalarRootGroup (afterDelegRootCol EFFECT_VM_WIDTH)
  , op      := .write }

/-- The rotated REFRESH-DELEGATION on the MOVING genuine face (no `gCapPass` freeze — the rotated limb is
free to carry the deleg move): the arity-2 map-ops DROPPED (the UPDATE-shaped after-spine deploy —
mirroring `attenuateV3`'s update drop). The faithful 8-felt DELEG-tree UPDATE-AT-KEY is FORCED by the
deployed `effCapOpenWriteV3` wrap (`CapOpenEmit.effCapOpenWriteV3_forces_write8` — the update-at-key
after-spine over the FULL committed 8-felt root groups; the rotated cap-root group carries the DELEG
accumulator on a refresh row, refresh freezes `caps` on the v1 column), not the scalar
`delegReadOpRot`/`delegUpdateWriteOpRot` pair (whose arity-2 heap fold is UNSAT against the deployed
native-8-felt witness heaps and whose scalar root left the seven high felts unbound). The DELEG WRITE
stays in-circuit-forced (never the `delegRoot_runtime_column_pending` supplied digest). NO submask —
refresh re-arms an existing delegation (`granted = held`, non-amplification reflexive). -/
def refreshDelegationWriteV3 : EffectVmDescriptor2 :=
  v3OfWithCapWrite EffectVmEmitAttenuateA.attenuateVmDescriptorGenuineNoRecomputeTick []

/-- The rotated dynamic setField WITH its memory ops (the Blum write→read transport). -/
def setFieldDynV3 : EffectVmDescriptor2 :=
  v3OfWith setFieldDynV1Face [.memOp fieldWriteOp, .memOp fieldReadbackOp]

/-- **The custom COMMIT-TEETH column base** (the proof-bind flag-day rotation, 4 → 8 commitment
felts): the four member-local columns carrying `custom_proof_commitment` limbs 4..8 (the genuine
SECOND SQUEEZE BLOCK of the 8-felt `WideHash` commitment), appended at the END of the custom
member's graduated host width — the custom twin of the membership/sovereign teeth
(`CarrierComposed.withMembershipTeethPinsAt`), placed IN the host so the generic wraps
(`withDfaRcPins`, the gentian refuse weld, `wideAppend`) land past them with zero special-casing.
Rust twin: `trace_rotated::CUSTOM_COMMIT_TEETH_BASE` (`#guard`-pinned to 1619 below).

⚑ Defined against `v3Of` and not `v3OfWith … [.proofBind …]` since 2026-08-05: the widened bind
READS these columns, so defining the base in terms of a descriptor carrying it would be a
definitional cycle. `v3OfWith` only appends constraints, so the two widths are the same number. -/
def CUSTOM_COMMIT_TEETH_COL : Nat := (v3Of customV1Face).traceWidth

/-- **The VK-epoch PI exposure for the rotated Custom member — the faithful carrier flag day.**
Sixteen `.piBinding .first` constraints
publishing the `proofBind` op's bound binding as PUBLIC INPUTS of the descriptor:
the four LOW `custom_proof_commitment` limbs (`prmCol (CUSTOM_COMMIT + k)` = cols 72..75) at IR2
PI slots `39..42` (the first slots past the four rotated commit pins, `rotateV3` produces
`piCount = pi.V1_PI_COUNT + 4 = 39`), the four HIGH commitment limbs — the second squeeze block, on
the member-local COMMIT-TEETH columns (`CUSTOM_COMMIT_TEETH_COL + k`) — at slots `43..46`, the four
LOW `custom_program_vk_hash` limbs (`prmCol (CUSTOM_VK + k)` = cols 68..71) at slots `47..50`, and
the four HIGH vk limbs on member-local VK-TEETH columns (`CUSTOM_VK_TEETH_COL + k`) at slots
`51..54`, all
pinned on the FIRST (the lead Custom) row — the row the `generate_rotated_custom_wide` generator
lays the bound `(vk, commit)` on. Exposing these columns as PIs is THE change that lets the
per-turn FOLD connect the custom sub-proof leaf's 8-felt PI-commitment to the descriptor: the
binding (a verifying sub-proof of `E` whose PI commitment EQUALS these columns) is enforced at
the FOLD via these PIs + the custom-leaf recursion (`StarkSoundCustom` / `EngineBinding`, the
Lean model in `CustomApex`, axiom-clean), NOT by a row-local in-AIR gate — so the per-row
`proofBind` denotation stays `True` like `memOp`/`umemOp`
(`DescriptorIR2.VmConstraint2.holdsAt`). The descriptor now trace-carries and publishes the FULL
faithful VK8; a legacy low4 carrier is refused at the Rust versioned boundary
(`effect_vm_descriptors::require_custom_carrier_vk8`), never folded, padded, or silently widened. -/
def CUSTOM_VK_TEETH_COL : Nat := CUSTOM_COMMIT_TEETH_COL + 4

/-- ⚑ **THE ROTATED CUSTOM'S RECURSION SEAM, AT EIGHT LANES.** The low four limbs of each object sit
in the `param` block; the high four ride the teeth columns this member appends. Before 2026-08-05
this op named `param[CUSTOM_COMMIT]` and `param[CUSTOM_VK]` — LIMB 0 of each — while the sixteen
`customPiExposure` pins published all eight of both: the descriptor exposed the whole digest and
DECLARED one felt of it. Now the declaration is the same width as the exposure. -/
def customV3ProofBind : Dregg2.Circuit.DescriptorIR2.ProofBind :=
  customProofBindAt CUSTOM_COMMIT_TEETH_COL CUSTOM_VK_TEETH_COL

/-- The base of the sixteen custom exposure PIs: the FIRST slot past the four rotated commit pins,
`pi.V1_PI_COUNT + 4`. The Rust twin is `joint_turn_recursive::CUSTOM_COMMIT_PI_LO`.

⚑ These four bases were the LITERALS `46 / 50 / 54 / 58` until 2026-08-07, and that is a wound the
seven-slot PI compaction nearly shipped: `customV3.piCount` is `d.piCount + 16`, i.e. SYMBOLIC, so
when `V1_PI_COUNT` went 42 → 35 the member's declared count fell 66 → 59 while the pins stayed at
46..61 — three of them past the end of the vector, and every `piCount` `#guard` in this file still
green. A published index must cascade from the same place the count does. -/
def CUSTOM_EXPOSURE_PI_BASE : Nat := pi.V1_PI_COUNT + 4

def customPiExposure : List VmConstraint2 :=
  (List.range 4).map (fun k =>
    .base (.piBinding .first (prmCol (CUSTOM_COMMIT + k)) (CUSTOM_EXPOSURE_PI_BASE + k)))
  ++ (List.range 4).map (fun k =>
    .base (.piBinding .first (CUSTOM_COMMIT_TEETH_COL + k) (CUSTOM_EXPOSURE_PI_BASE + 4 + k)))
  ++ (List.range 4).map (fun k =>
    .base (.piBinding .first (prmCol (CUSTOM_VK + k)) (CUSTOM_EXPOSURE_PI_BASE + 8 + k)))
  ++ (List.range 4).map (fun k =>
    .base (.piBinding .first (CUSTOM_VK_TEETH_COL + k) (CUSTOM_EXPOSURE_PI_BASE + 12 + k)))

/-- The rotated CUSTOM (sel 8) WITH the recursive-proof-binding leg: the runtime passthrough face
lifted through `rotateV3`, carrying the `proofBind` op (`customProofBind`) that ties the row's
`custom_proof_commitment` to a verifying external sub-proof — the accumulator constraint the
per-row IR gained — PLUS (the VK epoch + the proof-bind flag day) the FOUR COMMIT-TEETH and FOUR
VK-TEETH columns (the 8-felt commitment and VK second squeeze blocks, appended at the end of the host) and the sixteen
`customPiExposure` PI bindings that publish the bound `(commit, vk)` so the per-turn FOLD can
connect the custom sub-proof leaf. The `proofBind` row gate stays `True`; the binding is
enforced at the fold (see `customPiExposure`).
This is THE last rotation-cohort member: with it the HONEST RESIDUE is EMPTY. -/
def customV3 : EffectVmDescriptor2 :=
  let d := v3OfWith customV1Face [.proofBind customV3ProofBind]
  { d with
    traceWidth  := d.traceWidth + 8
    piCount     := d.piCount + 16
    constraints := d.constraints ++ customPiExposure }

-- The commit-teeth base is the PRE-TEETH graduated host width — byte-pinned to the Rust twin
-- (`trace_rotated::CUSTOM_COMMIT_TEETH_BASE = CUSTOM_HOST_WIDTH = 1663`) and to the widened
-- member geometry (host 1671 = 1663 + 4 commit teeth + 4 VK teeth).
-- ⚑ FLAG DAY 178 → 184: 1619 → 1663. `+16` from `APPENDIX_SPAN` (two blocks × 8 columns) and `+28`
-- from graduation (the appendix gained 4 sites × 7 lane columns). The Rust twin MUST be re-pinned.
-- ⚑ FLAG DAY rc-FOLD: 1663 → 1679. `+2` from `C_SPAN` (43 → 45, the two rc-absorbing carriers) and
-- `+14` from graduation (the appendix gained 2 sites × 7 lane columns). Re-pin the Rust twin again.
-- ⚑ FLAG DAY FIELDS-CANONICITY (2026-07-31): 1679 → 1791. `+112` from `CANON9_SPAN` — the aux
-- region rides inside the appendix, PAST the caveat region, and contributes NO new hash site, so
-- graduation adds nothing. Re-pin the Rust twin (`trace_rotated::CUSTOM_HOST_WIDTH`).
-- ⚑ FLAG DAY KEY-NONET (2026-08-01, 184 → 187 limbs): 1791 → 1813. `+8` from `APPENDIX_SPAN`
-- (two blocks × 4 columns: `B_SPAN` 247 → 251) and `+14` from graduation (the appendix gained 2
-- sites × 7 lane columns: 136 → 138). Re-pin the Rust twin AGAIN — this literal is the review.
#guard CUSTOM_COMMIT_TEETH_COL == 1879
#guard CUSTOM_VK_TEETH_COL == 1883
#guard customV3.traceWidth == CUSTOM_COMMIT_TEETH_COL + 8

/-! ### The note-spend nullifier PI weld (the C4 last-flip-gate close).

The v1 hand-AIR (`circuit/src/effect_vm/air.rs`, D5) carries a per-row GATED cross-binding
`s_notespend · (param0 − PI[NOTESPEND_NULLIFIER])` in the WIDE `pi::` layout: the spend row's
folded nullifier (`param::NULLIFIER = param0`, column `prmCol 0`) MUST equal the published
`PI[NOTESPEND_NULLIFIER]` — the weld that forbids the EffectVM from spending a different
nullifier than the one the SCHEMA_NOTE_SPEND binding proof certified (the off-AIR verifier
reconstructs it from the binding proof's `fields[0]` and `verify_full_turn` step 8 cross-checks
the non-revocation proof's queried item against it).

(This paragraph wrote the offset as the literal `198` in three places until 2026-08-06 — a
pre-Phase-C number, stale since `OLD_COMMIT`/`NEW_COMMIT` widened 4 → 8 felts each. The slot
cascades from `OWNER_CELL_ID_BASE + OWNER_CELL_ID_LEN`, so it is named, never restated; the
Rust origin block, `circuit/src/effect_vm/pi.rs`'s `BASE_COUNT` docblock, says why.)

That cross-binding tooth lives ONLY in the v1 hand-AIR — `noteSpendVmDescriptor` (the Lean
per-effect descriptor) does NOT bind the nullifier to any PI (its `piCount = pi.V1_PI_COUNT` is
the v1 prefix only). So when the rotated leg retires the hand-AIR, the bare rotated PI vector omits
the nullifier and a note-spending turn with a freshness binding CANNOT rotate (it falls back to
v1 — the documented C4 boundary, `verify_full_turn` step 8 REFUSES the rotated leg).

`noteSpendV3` CLOSES that gate: it appends a FIFTH PI pin past the four rotated commit pins
(`rotateV3` produces `piCount = pi.V1_PI_COUNT + 4`), binding the spend row's `param0` (the folded
nullifier) to the new rotated PI slot `ROT_NULLIFIER_PI` on the FIRST row. The note-spend turn lays
the spend on row 0 (`generate_effect_vm_trace`'s `Effect::NoteSpend` arm + the trace generator's
`row[PARAM_BASE + param::NULLIFIER]` write are on row 0; `boundaryFirstPins` pins the first
row), so the first-row pin is the rotated analog of the v1 per-row gate. The SOUNDNESS TOOTH
(`noteSpendV3_rejects_nullifier_tamper`): a row whose `param0` differs from the published
`PI[ROT_NULLIFIER_PI]` FAILS the pin and is UNSAT — exactly the v1 `rejects_swap` adversarial test,
now at the rotated boundary. The Rust `verify_full_turn` step 8 reads that slot of the rotated leg
instead of refusing, so the no-double-spend cross-check (`queried_item == nullifier`) fires on the
rotated note-spend turn. -/

/-- The rotated nullifier-PI slot: the FIRST slot past the four rotated commit pins
(`rotateV3` appends OLD/NEW commit · height · caveat commit at `piCount..piCount+3`). Derived
from `pi.V1_PI_COUNT` rather than written as a literal, so the 2026-08-07 seven-slot compaction
(and any successor) cascades here instead of being restated. -/
def ROT_NULLIFIER_PI : Nat := pi.V1_PI_COUNT + 4

/-- The folded-nullifier parameter column (`param::NULLIFIER = param0`, `prmCol 0`) — the
spend row's single folded `fold_bytes32_to_bb(nullifier)` felt the v1 hand-AIR cross-binds. -/
def NULLIFIER_PARAM_COL : Nat := prmCol 0

/-- **`rotateV3WithNullifierPin`** — `rotateV3` PLUS the fifth appended PI pin welding the
spend row's folded nullifier (`prmCol 0`) to the rotated PI slot `ROT_NULLIFIER_PI` on
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
OLD/NEW commit · height · caveat commit at `piCount..piCount+3`) — the same arithmetic as
`ROT_NULLIFIER_PI` (transfer and note-spend never co-occur on one descriptor, so sharing the slot
index is sound). -/
def ROT_FEE_PI : Nat := pi.V1_PI_COUNT + 4

/-- The fee column (the after-block `RESERVED` state limb of the v1 sub-trace). The v1 columns sit
at fixed offsets inside `[0, EFFECT_VM_WIDTH)`, so this is `traceWidth`-independent. -/
def FEE_COL : Nat := EffectVmEmitTransfer.feeCol

/-- **`rotateV3WithFeePin`** — a rotated descriptor PLUS the fifth appended PI pin welding the fee
column (`feeCol = saCol state.RESERVED`, carrying the debited fee) to the rotated PI slot
`ROT_FEE_PI` on the LAST row (the after-block carries the post-fee balance, so the fee pin is a
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
`base = traceWidth + B_SPAN`). The deployed nullifier accumulator's POST root — the grow-gate's
`newRoot`. -/
def afterNullifierRootCol (w : Nat) : Nat := w + B_SPAN + 26

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
  , root    := beforeNullifierRootGroup
  , key     := .var NULLIFIER_PARAM_COL
  , value   := .const 0
  , newRoot := beforeNullifierRootGroup
  , op      := .absent }

/-- The SET-INSERT (the deployed `gNoteGrow` face): the AFTER nullifier root (limb 26 of the
after block) IS the genuine sorted write of `param0` into the BEFORE root. The note value
(`param::NOTE_VALUE_LO`) rides as the leaf value so a spent nullifier carries its note datum. -/
def nullifierInsertOp : MapOp :=
  { guard   := .var EffectVmEmitNoteSpend.SEL_NOTE_SPEND
  , root    := beforeNullifierRootGroup
  , key     := .var NULLIFIER_PARAM_COL
  , value   := .var (prmCol EffectVmEmitNoteSpend.param.NOTE_VALUE_LO)
  , newRoot := afterNullifierRootGroup
  , op      := .aafiInsert }  -- gap-#5 AAFI (F1 flip: op=4, matches the deployed TSV; two-path forces sorted-preservation)

/-- The spend row's DELEGATION-ANCESTOR revocation-id parameter column (`param3`, `prmCol 3` —
free on a noteSpend row: the spend arm fills only params 0..2). The witness generator parks the
spend's delegation-ancestor id here — the SAME `child_hash[0]` key domain `revokedInsertOp`
(§5.RV) grows the limb-37 revoked set with on RevokeDelegation turns.

CURRENT RESOLUTION (say it plainly): this column is a WITNESS column. The map-op below forces
"the OPENED key is absent from the committed revoked set"; it does NOT yet force "the opened
key IS the exercised capability's delegation ancestor" — that binding (a cross-constraint to
the cap-open lineage, or a published-PI pin the verifier cross-checks like the C4 nullifier
weld) is the named follow-up. Honest producers (the SDK/node — the only proof mints today)
park the true ancestor; the gate then refuses a spend under a revoked ancestor. -/
def SPEND_ANCESTOR_PARAM_COL : Nat := prmCol 3

/-- **The DELEGATION-ANCESTOR freshness tooth (felt-width #11 fold-in — the carve-out).**
The spend's delegation-ancestor id (`param3`) is a NON-MEMBER of the BEFORE revoked tree
(limb 37, `B_REVOKED_ROOT` — the set `revokedInsertOp` grows on RevokeDelegation turns); an
absent read leaves the root unchanged. Before this op the revoked set was only ever
*inserted* into (§5.RV) and never *opened* on spends, so a spend exercising a REVOKED
delegation chain still verified. Guarded by the spend selector, so non-spend / NoOp pad rows
contribute nothing. -/
def spendAncestorFreshOp : MapOp :=
  { guard   := .var EffectVmEmitNoteSpend.SEL_NOTE_SPEND
  , root    := beforeRevokedRootGroup
  , key     := .var SPEND_ANCESTOR_PARAM_COL
  , value   := .const 0
  , newRoot := beforeRevokedRootGroup
  , op      := .absent }

/-- **`noteSpendV3`** — the rotated note-spend WITH the nullifier PI weld AND the KERNEL-SET
GROW-GATE (the deployment-real set-insert + double-spend tooth). `piCount = 40` (the 39-PI
rotated prefix + the appended nullifier slot). Past the graduated `rotateV3WithNullifierPin`
descriptor, it appends the THREE map-ops that FORCE the spend's set discipline on the live wire:
`nullifierFreshOp` (the `.absent` double-spend tooth — `nf ∉ pre`), `nullifierInsertOp` (the
`.insert` set-insert — `after_root = insert(before_root, nf)`), and `spendAncestorFreshOp`
(the felt-width #11 fold-in: the spend's delegation-ancestor id is `.absent` from the limb-37
revoked set `revokedInsertOp` grows — a spend under a revoked delegation chain is UNSAT). The
first two repoint limb 26 from a turn-invariant witness limb into a FORCED, grown, fresh
nullifier root; the third finally OPENS limb 37 on the spend side. -/
def noteSpendV3 : EffectVmDescriptor2 :=
  let base := graduateV1 (rotateV3WithNullifierPin EffectVmEmitNoteSpend.noteSpendVmDescriptor)
  { base with
    constraints := base.constraints
      ++ [.mapOp nullifierFreshOp, .mapOp nullifierInsertOp, .mapOp spendAncestorFreshOp] }

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

/-- **`noteSpendV3_opens_delegation_ancestor` — the live descriptor OPENS the limb-37 revoked
set on every spend (felt-width #11 fold-in).** On a satisfying `noteSpendV3` witness whose
spend selector fires, the appended `spendAncestorFreshOp` holds: the spend's delegation-ancestor
id (`param3`) is ABSENT from the BEFORE revoked tree (limb 37 — the set the RevokeDelegation
grow-gate `revokedInsertOp` maintains). Under CR the opening is FUNCTIONAL
(`opensTo_functional` / `opensTo_some_excludes_none`), so a spend whose opened ancestor IS in
the revoked set has no bracketing witness and cannot satisfy the descriptor. (The residual — the
opened key column's binding to the exercised capability's genuine lineage — is documented at
`SPEND_ANCESTOR_PARAM_COL`.) -/
theorem noteSpendV3_opens_delegation_ancestor (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash noteSpendV3 minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length)
    (hspend : (envAt t i).loc EffectVmEmitNoteSpend.SEL_NOTE_SPEND = 1) :
    opensTo hash ((envAt t i).loc (EFFECT_VM_WIDTH + B_REVOKED_ROOT))
        ((envAt t i).loc SPEND_ANCESTOR_PARAM_COL) none := by
  have hrowc := hsat.rowConstraints i hi
  have hanc := hrowc (.mapOp spendAncestorFreshOp) (by simp [noteSpendV3])
  exact (hanc hspend).1

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
    env.loc NULLIFIER_PARAM_COL ≡ env.pub ROT_NULLIFIER_PI [ZMOD 2013265921] := by
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
    (hcanonParam : 0 ≤ env.loc NULLIFIER_PARAM_COL ∧ env.loc NULLIFIER_PARAM_COL < 2013265921)
    (hcanonPI : 0 ≤ env.pub ROT_NULLIFIER_PI ∧ env.pub ROT_NULLIFIER_PI < 2013265921)
    (htamper : env.loc NULLIFIER_PARAM_COL ≠ env.pub ROT_NULLIFIER_PI) :
    ¬ satisfiedVm hash (rotateV3WithNullifierPin
      EffectVmEmitNoteSpend.noteSpendVmDescriptor) env true isLast :=
  fun h => htamper (canon_eq_of_modEq hcanonParam hcanonPI
    (noteSpendV3_pins_nullifier hash env isLast h))

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
#guard ROT_NULLIFIER_PI == 39
#guard NULLIFIER_PARAM_COL == 68          -- PARAM_BASE (54+14) + param::NULLIFIER (0)
#guard noteSpendV3.piCount == 40
#guard (rotateV3WithNullifierPin EffectVmEmitNoteSpend.noteSpendVmDescriptor).piCount == 40
-- Graduation survives the appended pin.
#guard graduable (rotateV3WithNullifierPin EffectVmEmitNoteSpend.noteSpendVmDescriptor)
-- The rotated commit pins are UNDISTURBED at 34..37 (the fifth pin is strictly appended);
-- `noteSpendV3` carries the four rotated commit pins PLUS one more PI pin (the nullifier weld)
-- PLUS the two KERNEL-SET grow-gate map-ops (`nullifierFreshOp` `.absent` + `nullifierInsertOp`
-- `.insert` — the deployment-real set-insert + double-spend tooth) PLUS the delegation-ancestor
-- freshness op (`spendAncestorFreshOp` `.absent` on limb 37 — the felt-width #11 fold-in)
-- = +4 constraints in total.
#guard noteSpendV3.constraints.length == (v3Of EffectVmEmitNoteSpend.noteSpendVmDescriptor).constraints.length + 1 + 3
-- The grow-gate map-ops ARE present on `noteSpendV3` (the live wire now carries the set-insert
-- AND the limb-37 delegation-ancestor open).
#guard (mapOpsOf noteSpendV3).length == 3
-- The delegation-ancestor tooth: `.absent` (op=2) on the limb-37 revoked group, keyed by param3.
#guard spendAncestorFreshOp.op.code == 2
#guard SPEND_ANCESTOR_PARAM_COL == 71     -- PARAM_BASE (54+14) + 3
#guard revokedRootGroupCol EFFECT_VM_WIDTH 0 == EFFECT_VM_WIDTH + B_REVOKED_ROOT
#guard B_REVOKED_ROOT == 37
-- BOTH POLARITIES of the soundness tooth, executable on the toy environment: a row whose
-- param0 equals `PI[ROT_NULLIFIER_PI]` PASSES the pin; a tampered one FAILS it. (`decEnv` toy:
-- param col 68 carries `n`, the nullifier PI carries `p`. The PI index is written as the constant,
-- not as a literal — the 2026-08-07 seven-slot compaction moved it 46 → 39 and a literal here would
-- have made both poles read an all-zero slot, i.e. the match pole would have gone red and the
-- MISMATCH pole would have stayed green for the wrong reason.)
#guard (let env : VmRowEnv := ⟨fun c => if c == 68 then 5 else 0, fun _ => 0,
                              fun k => if k == ROT_NULLIFIER_PI then 5 else 0, fun _ => 0⟩;
        decide (env.loc NULLIFIER_PARAM_COL = env.pub ROT_NULLIFIER_PI))   -- match ⇒ pin holds
#guard (let env : VmRowEnv := ⟨fun c => if c == 68 then 5 else 0, fun _ => 0,
                              fun k => if k == ROT_NULLIFIER_PI then 9 else 0, fun _ => 0⟩;
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
four rotated commit pins (`piCount = pi.V1_PI_COUNT + 4`), the same arithmetic as
`ROT_NULLIFIER_PI` (noteCreate and noteSpend never co-occur on one row, so sharing the slot is
sound). -/
def ROT_COMMITMENT_KEY_PI : Nat := pi.V1_PI_COUNT + 4

/-- The note-commitment key parameter column (`param0`, `prmCol 0`) — the noteCreate row's
single published note-commitment felt (`Effect::NoteCreate { commitment }` ⇒ `row[PARAM_BASE+0]`). -/
def COMMITMENT_KEY_PARAM_COL : Nat := prmCol 0

/-- The rotated BEFORE-block `commitments_root` limb column (limb 27 of the before block at
`base = traceWidth`). The deployed commitments accumulator's PRE root. -/
def beforeCommitmentsRootCol (w : Nat) : Nat := w + B_COMMITMENTS_ROOT

/-- The rotated AFTER-block `commitments_root` limb column (limb 27 of the after block at
`base = traceWidth + B_SPAN`). The deployed commitments accumulator's POST root — the grow-gate's
`newRoot`. -/
def afterCommitmentsRootCol (w : Nat) : Nat := w + B_SPAN + B_COMMITMENTS_ROOT

/-- **`rotateV3WithCommitmentKeyPin`** — `rotateV3` PLUS the fifth appended PI pin welding the note
commitment (`prmCol 0`) to `ROT_COMMITMENT_KEY_PI` on the FIRST row. Structurally identical to
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
  , root    := beforeCommitmentsRootGroup
  , key     := .var COMMITMENT_KEY_PARAM_COL
  , value   := .var (prmCol EffectVmEmitNoteCreate.param.NOTE_VALUE_LO)
  , newRoot := afterCommitmentsRootGroup
  , op      := .aafiInsert }  -- gap-#5 AAFI (F1 flip: op=4, matches the deployed TSV; two-path forces sorted-preservation)

/-- **`noteCreateV3`** — the rotated noteCreate WITH the commitment PI weld AND the KERNEL-SET
GROW-GATE (the deployment-real commitments set-insert). `piCount = 40`. Past the graduated
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
#guard ROT_COMMITMENT_KEY_PI == 39
#guard COMMITMENT_KEY_PARAM_COL == 68
#guard noteCreateV3.piCount == 40
#guard (mapOpsOf noteCreateV3).length == 1
#guard beforeCommitmentsRootCol EFFECT_VM_WIDTH == EFFECT_VM_WIDTH + 27
#guard afterCommitmentsRootCol EFFECT_VM_WIDTH == EFFECT_VM_WIDTH + 263 + 27

/-! ## §5.RV — the revoke REVOKED-SET GROW-GATE (the deployment-real revoked set-insert; hole #3).

`docs/reference/GAP5-AAFI-CUTOVER-PLAN.md` §1.4: the deployed `revokeVmDescriptor` (the Stage-3
runtime passthrough row + nonce TICK) carried `revoked_root` (limb 37, `B_REVOKED_ROOT`) as a
PRODUCER-SUPPLIED committed limb with NO gate forcing it — Lean hole #3/#139: "a node can supply an
empty root and the commitment faithfully records the lie; a light client cannot detect it". There
was NO deployed insert gate to flip, so this lands the revoked insert DIRECTLY as AAFI-native.

These two `MapOp`s CLONE the noteSpend grow-gate onto limb 37, guarded by the revoke selector
(`SEL_REVOKE_DELEGATION = 30`). The inserted KEY is the revoked child-capability hash the runtime
parks in `param0` (`trace.rs:604` — "the trace arm parks `child_hash[0]` into `params[0]`"), so the
gate's key IS the revoked credential id:

  * **`revokedFreshOp`** (`.absent`) — the NO-DOUBLE-REVOKE tooth: the revoked id (`param0`) is a
    NON-MEMBER of the BEFORE revoked tree (limb 37); the root is unchanged by an absent read. Under
    CR (`opensTo_none_of_gap` / the pointer bracket) an already-revoked id has no bracketing witness
    and is UNSAT.
  * **`revokedInsertOp`** (`.aafiInsert`, op=4) — the AAFI-NATIVE SET-INSERT: the AFTER revoked root
    (limb 37 of the after block) IS the genuine two-path AAFI insert of `param0` into the BEFORE
    root. The scalar denotation is `writesTo` (after-root FORCED, no longer producer-supplied — hole
    #3 CLOSED); the deployed op=4 AIR additionally forces the sorted append-order / no-shift via the
    two-path opening + pointer-bracket range gate (`MapOpsColumnLayout.aafiInsert_forces_imtInsert`),
    so a frozen / forged / empty revoked root cannot satisfy the descriptor. -/

/-- The revoked child-capability key parameter column (`param0`, `prmCol 0`) — the revoke row's
revoked credential id (`child_hash[0]`). Mirrors `NULLIFIER_PARAM_COL`. -/
def REVOKED_KEY_PARAM_COL : Nat := prmCol 0

/-- The rotated BEFORE-block `revoked_root` scalar limb column (limb 37 of the before block). -/
def beforeRevokedRootCol (w : Nat) : Nat := w + B_REVOKED_ROOT

/-- The rotated AFTER-block `revoked_root` scalar limb column (limb 37 of the after block) — the
grow-gate's forced `newRoot` (hole #3: no longer a free producer witness). -/
def afterRevokedRootCol (w : Nat) : Nat := w + B_SPAN + B_REVOKED_ROOT

/-- The NO-DOUBLE-REVOKE tooth: the revoked id (`param0`) is a NON-MEMBER of the BEFORE revoked tree
(limb 37); an absent read leaves the root unchanged. -/
def revokedFreshOp : MapOp :=
  { guard   := .var EffectVmEmitRevokeDelegation.SEL_REVOKE_DELEGATION
  , root    := beforeRevokedRootGroup
  , key     := .var REVOKED_KEY_PARAM_COL
  , value   := .const 0
  , newRoot := beforeRevokedRootGroup
  , op      := .absent }

/-- The AAFI-NATIVE SET-INSERT (op=4): the AFTER revoked root (limb 37 of the after block) IS the
genuine AAFI two-path insert of `param0` into the BEFORE root. The revoked set is a pure membership
set, so the leaf value is `0`. Guarded by the revoke selector. -/
def revokedInsertOp : MapOp :=
  { guard   := .var EffectVmEmitRevokeDelegation.SEL_REVOKE_DELEGATION
  , root    := beforeRevokedRootGroup
  , key     := .var REVOKED_KEY_PARAM_COL
  , value   := .const 0
  , newRoot := afterRevokedRootGroup
  , op      := .aafiInsert }

/-- **`revokeV3`** — the rotated revoke WITH the REVOKED-SET GROW-GATE (the deployment-real revoked
set-insert). Past the graduated `v3Of` revoke descriptor it appends the two map-ops that FORCE the
revoked set-insert on the live wire — repointing limb 37 from a producer-supplied witness limb into
a FORCED, grown, fresh revoked root (hole #3 closed). Mirrors `noteSpendV3` (`.absent` fresh tooth +
the AAFI-native insert). -/
def revokeV3 : EffectVmDescriptor2 :=
  let base := v3Of EffectVmEmitRevokeDelegation.revokeVmDescriptor
  { base with
    constraints := base.constraints ++ [.mapOp revokedFreshOp, .mapOp revokedInsertOp] }

/-- **`revokeV3_grow_gate_forces_set_insert` — the live descriptor FORCES the revoked set-insert +
no-double-revoke (hole #3 closed).** On a satisfying `revokeV3` witness whose revoke selector fires,
the two appended map-ops hold: (1) the revoked id (`param0`) is ABSENT from the BEFORE revoked tree
(limb 37) — the no-double-revoke tooth; and (2) the AFTER revoked root IS the genuine insert of that
id into the BEFORE root (`writesTo`). Under CR these are FUNCTIONAL, so a frozen or forged after-root
(the producer-supplied lie hole #3 documented), or an already-revoked id, cannot satisfy the
descriptor. -/
theorem revokeV3_grow_gate_forces_set_insert (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash revokeV3 minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length)
    (hrevoke : (envAt t i).loc EffectVmEmitRevokeDelegation.SEL_REVOKE_DELEGATION = 1) :
    (opensTo hash ((envAt t i).loc (beforeRevokedRootCol EFFECT_VM_WIDTH))
        ((envAt t i).loc REVOKED_KEY_PARAM_COL) none)
    ∧ writesTo hash ((envAt t i).loc (beforeRevokedRootCol EFFECT_VM_WIDTH))
        ((envAt t i).loc REVOKED_KEY_PARAM_COL) 0
        ((envAt t i).loc (afterRevokedRootCol EFFECT_VM_WIDTH)) := by
  have hrowc := hsat.rowConstraints i hi
  have hfresh := hrowc (.mapOp revokedFreshOp) (by simp [revokeV3])
  have hins := hrowc (.mapOp revokedInsertOp) (by simp [revokeV3])
  have ha := hfresh hrevoke
  have hw := hins hrevoke
  exact ⟨ha.1, hw⟩

#assert_axioms revokeV3_grow_gate_forces_set_insert

-- The revoke grow-gate carries the two map-ops on the revoked_root limb (37); the AAFI insert emits
-- op=4 (`aafi_insert`), the fresh tooth op=2 (`absent`).
#guard (mapOpsOf revokeV3).length == 2
#guard revokedInsertOp.op.code == 4
#guard revokedFreshOp.op.code == 2
#guard REVOKED_KEY_PARAM_COL == 68
#guard beforeRevokedRootCol EFFECT_VM_WIDTH == EFFECT_VM_WIDTH + 37
#guard afterRevokedRootCol EFFECT_VM_WIDTH == EFFECT_VM_WIDTH + 263 + 37
-- Lane 0 of the revoked root group IS the scalar limb 37 (the projection the scalar writesTo forces).
#guard revokedRootGroupCol EFFECT_VM_WIDTH 0 == EFFECT_VM_WIDTH + 37

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
four rotated commit pins (`piCount = pi.V1_PI_COUNT + 4`), the same arithmetic as
`ROT_NULLIFIER_PI` (these descriptors and noteSpend never co-occur on one row, so sharing the slot
is sound). -/
def ROT_NEW_CELL_KEY_PI : Nat := pi.V1_PI_COUNT + 4

/-- The new-cell key parameter column (`param0`, `prmCol 0`) — the create/factory/spawn row's
single folded new-cell identity felt (`create_hash[0]`). -/
def NEW_CELL_KEY_PARAM_COL : Nat := prmCol 0

/-- The rotated BEFORE-block `cells_root` limb column (limb 0 of the before block at
`base = traceWidth`). The deployed accounts accumulator's PRE root — the openable
sorted-Poseidon2 root the grow-gate opens against. -/
def beforeCellsRootCol (w : Nat) : Nat := w + 0

/-- The rotated AFTER-block `cells_root` limb column (limb 0 of the after block at
`base = traceWidth + B_SPAN`). The deployed accounts accumulator's POST root — the grow-gate's
`newRoot`. -/
def afterCellsRootCol (w : Nat) : Nat := w + B_SPAN + 0

/-- **`rotateV3WithNewCellKeyPin`** — `rotateV3` PLUS the fifth appended PI pin welding the
new-cell key (column `keyCol`) to `ROT_NEW_CELL_KEY_PI` on the FIRST row. Structurally identical
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
  , root    := beforeCellsRootGroup
  , key     := .var keyCol
  , value   := .const 0
  , newRoot := beforeCellsRootGroup
  , op      := .absent }

/-- The SET-INSERT: the AFTER cells root (limb 0 of the after block) IS the genuine sorted write of
the new-cell key (`keyCol`) into the BEFORE root. The key rides as its own leaf value (a born-empty
cell). -/
def cellsInsertOp (sel keyCol : Nat) : MapOp :=
  { guard   := .var sel
  , root    := beforeCellsRootGroup
  , key     := .var keyCol
  , value   := .var keyCol
  , newRoot := afterCellsRootGroup
  , op      := .aafiInsert }  -- gap-#6 AAFI (op=4, matches the deployed TSV; two-path forces sorted-preservation — installs the ImtSorted invariant cellsFreshOp presupposes)

/-- The factory's new-cell key column (`param1`, the derived child VK — `CHILD_VK_DERIVED`); factory's
`param0` carries the factory VK, so the child id is `param1`. -/
def FACTORY_CHILD_KEY_PARAM_COL : Nat := prmCol 1

/-- **`createCellV3`** — the rotated createCell WITH the new-cell-key PI weld AND the ACCOUNTS-SET
GROW-GATE. `piCount = 40`. Past the graduated `rotateV3WithNewCellKeyPin` descriptor it appends the
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
- limb 25 (cap-tree): the cap handoff INSERT-shaped after-spine deploy — the arity-2 map-ops
  (`anchorReadOpRot` + `insertWriteOpRot`) are DROPPED (mirroring `delegateV3`); the cap-tree INSERT is
  FORCED by the deployed `effCapInsertV3` wrap (`CapInsertEmit.effCapInsertV3_forces_write8` — the
  spliced-leaf membership in the REBUILT AFTER tree over the FULL committed 8-felt cap-root groups),
  not the scalar pair (UNSAT against the deployed arity-7 `CanonicalCapTree::insert_witness`).

The cap handoff (the parent→child CAPABILITY confer) was the named PHASE-D residual on `spawnV3` (frozen
`cap_root`/gCapPass); freeing limb 25 and riding the keystone wrap FORCES it, exactly as `delegateV3`. -/
def spawnWriteV3 : EffectVmDescriptor2 :=
  let base := graduateV1 (rotateV3WithNewCellKeyPinCapWrite NEW_CELL_KEY_PARAM_COL
    EffectVmEmitSpawn.spawnActorVmDescriptor)
  { base with constraints := base.constraints
      ++ [.mapOp (cellsFreshOp EffectVmEmitSpawn.SEL_SPAWN_RT NEW_CELL_KEY_PARAM_COL),
          .mapOp (cellsInsertOp EffectVmEmitSpawn.SEL_SPAWN_RT NEW_CELL_KEY_PARAM_COL)] }

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

-- (`spawnWriteV3_forces_write` — the arity-2 map-op cap-handoff theorem — is DELETED: the scalar
-- `anchorReadOpRot`/`insertWriteOpRot` pair was shape-UNSAT against the deployed arity-7
-- `CanonicalCapTree::insert_witness`. The cap handoff is now FORCED by the deployed `effCapInsertV3`
-- wrap: `CapInsertEmit.effCapInsertV3_forces_write8`, consumed by `RotatedKernelRefinementBirth`.)

#assert_axioms createCellV3_grow_gate_forces_set_insert
#assert_axioms factoryV3_grow_gate_forces_set_insert
#assert_axioms spawnV3_grow_gate_forces_set_insert
#assert_axioms spawnWriteV3_grow_gate_forces_set_insert

-- The new-cell-key pin lands at PI slot 46; each rotated create-family descriptor publishes 39 PIs.
#guard ROT_NEW_CELL_KEY_PI == 39
#guard NEW_CELL_KEY_PARAM_COL == 68
#guard createCellV3.piCount == 40
#guard factoryV3.piCount == 40
#guard spawnV3.piCount == 40
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
def B_RECORD_DIGEST : Nat := layoutGroupCol .authority 0

/-- The rotated AFTER-block base offset: exactly one verified block span past BEFORE. -/
def AFTER_BLOCK_OFF : Nat := B_SPAN

/-- **H1: the 7 headroom authority limb offsets** (offsets 12..=18 = r11..r17) carrying limb-1..7 of
the faithful 8-felt authority digest (`compute_authority_digest_8`), beside limb-0 at
`B_RECORD_DIGEST = 24`. These previously-unwelded headroom limbs now ride the absorption chain and are
WELDED (continuity freeze for value effects / record-pin8 for movers) so all 8 limbs are forced. -/
def authorityHeadroomOffs : List Nat := [12, 13, 14, 15, 16, 17, 18]

/-- The 7 continuity `colEq` freezes welding each headroom authority limb BEFORE↔AFTER (value cohort). -/
def authorityHeadroomFreezes (w : Nat) : List VmConstraint :=
  authorityHeadroomOffs.map (fun off => colEq (w + off) (w + AFTER_BLOCK_OFF + off))

/-- **v10: the 14 faithful-8-felt completion-limb offsets** — the 7 perms extras (pre-iroot limbs
38..=44 = `permsHash[1..7]`) and the 7 vk extras (45..=51 = `vkHash[1..7]`). For a VALUE turn the
permissions / VK are UNCHANGED, so each completion limb is frozen BEFORE↔AFTER — closing the GENTIAN
fail-open for the perms/vk halves (no unwelded wide-open limb can smuggle a ~31-bit-colliding authority
into NEW_COMMIT during an innocuous value move). -/
def permsVKCompletionOffs : List Nat :=
  [38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51]

/-- The 14 continuity `colEq` freezes welding each v10 perms/vk completion limb BEFORE↔AFTER. -/
def permsVKCompletionFreezes (w : Nat) : List VmConstraint :=
  permsVKCompletionOffs.map (fun off => colEq (w + off) (w + AFTER_BLOCK_OFF + off))

/-- **The 8 completion lanes (1..8) of `fields[slot]`** — the written slot's window, projected
through the verified layout's `Dregg2.Circuit.Emit.fieldLaneCol`, which is the SINGLE SOURCE for a
fields lane column.

⚑ **NEVER write `113 + 8·slot`.** The nonet is deliberately NON-CONTIGUOUS: lanes 1..7 keep their
historical window `113 + 7·slot .. +6` (UNMOVED by the flag day, exactly like the `fields` root group
already reuses headroom 19..23), and the NINTH lane of slot `j` is the flag-day column `176 + j`.
`fieldLaneCol_nodup` (RotatedLayout) machine-checks that the 72 lane columns are pairwise distinct. -/
def fieldsSlotLanes (slot : Fin 8) : List Nat :=
  (List.finRange 8).map (fun l => fieldLaneCol slot l.succ)

-- Slot 0's window: the historical seven, then the ninth lane at the first ex-pad column.
#guard fieldsSlotLanes 0 == [113, 114, 115, 116, 117, 118, 119, 176]
#guard fieldsSlotLanes 7 == [162, 163, 164, 165, 166, 167, 168, 183]
#guard ((List.finRange 8).flatMap fieldsSlotLanes).length == 64

/-- **All 64 fields[0..7] completion-lane offsets** — the eight flat fields' lanes 1..8 of the
`field_limbs9` NONET (`fields[j]` lanes 1..7 → `113 + 7·j .. +6`, lane 8 → `176 + j`; lane 0 rides
the welded limb `4 + j`). These lanes carry the higher bytes of each 32-byte record field.

⚑ **FLAG DAY 2026-07-31 (56 → 64), and this is the point of the whole 178 → 184 bump.** The
docstring here used to record a WOUND: eight lanes carry `8 · log₂ p = 247.26` bits against a 32-byte
field's 256, so **no 8-lane encoding of 32 bytes is injective under any chunking** — pigeonhole,
independent of what the lanes carry. Every earlier repair (an eight-way Horner fold, a `u32 % p`
chunking, a Poseidon2 image over an injective preimage) moved the attacker's COST and never reached
injectivity; the last priced out at a 2^92.7 collision. Since the `fields[0..7]` lanes are the only
binding those fields have (they are excluded from the byte-exact authority residue —
`cell/src/commitment.rs`, "bound by their own limbs"), the deficit reached
`TurnReceipt::{pre,post}_state_hash`.

**Nine lanes is the minimum and the encoder now exists**: `Dregg2.Circuit.FieldLanes9`'s
`fieldToLanes9` is an EXPLICIT BIJECTION onto its image with a total decoder and a machine-checked
left inverse (`lanes9ToField_fieldToLanes9`), so `fieldToLanes9_injective` is an injectivity theorem,
not a hash bound. Lanes 0 and 1 are byte-identical to the old `field_limbs8` (the kernel u64 lane),
so every weld constant, `setfield_encoder_window_gate` and every app encoder survives verbatim.

⚑ The residual that REMAINS: `metatheory/` still does not model the deployed Rust projector — neither
`field_limbs9` nor `bytes32_to_9_limbs` has a `def` here, and every setField capstone takes the
encoder's effect as a HYPOTHESIS (`hval : env.loc (prmCol VALUE) = v`) rather than deriving it. What
this file supplies is the COLUMN geometry and the freeze/publish teeth over it; the Lean-side
injectivity of the encoding lives in `FieldLanes9`, and `circuit/tests/field_lanes9_injective.rs`
asserts the deployed Rust reproduces its Lean-COMPUTED vectors. The two are joined by that test, not
by a theorem — say it at that resolution.

An explicit list, in exactly `rotated196.fieldsOctet`'s order (the historical 56 first, then the
eight ninth lanes), so the non-vacuity `fin_cases` discharges reduce and every pre-flag-day
constraint keeps its emission position. -/
def fieldsCompletionOffs : List Nat :=
  [113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128,
   129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144,
   145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160,
   161, 162, 163, 164, 165, 166, 167, 168,
   176, 177, 178, 179, 180, 181, 182, 183]

-- ⚑ THE LITERAL IS THE VERIFIED LAYOUT'S, not a second copy that agrees today: this list is exactly
-- `rotated196.fieldsOctet`, whose membership in a legal (disjoint, in-bounds) tiling is
-- `native_decide`-checked in `RotatedLayout.lean`. A geometry change that forgets this list fails HERE.
#guard fieldsCompletionOffs == rotated196.fieldsOctet
#guard fieldsCompletionOffs.length == 64
-- …and it is exactly the union of the eight per-slot windows (no lane orphaned, none invented).
#guard fieldsCompletionOffs.all (fun off => ((List.finRange 8).flatMap fieldsSlotLanes).contains off)
#guard ((List.finRange 8).flatMap fieldsSlotLanes).all (fun c => fieldsCompletionOffs.contains c)

/-- The 64 continuity `colEq` freezes welding each fields[0..7] completion lane BEFORE↔AFTER. For a
VALUE turn that does NOT write a flat field (transfer/burn/mint/bridgeMint/incrementNonce/emitEvent/
noteSpend/…) EVERY flat field is UNCHANGED, so each completion lane is frozen — closing the GENTIAN
fail-open for the fields halves (no unwelded wide-open completion can smuggle a forged higher-byte
field into NEW_COMMIT during an innocuous value move). ⚑ The eight NINTH lanes are in this list, so
the flag day widened the tooth rather than leaving eight new wide-open columns. -/
def fieldsCompletionFreezes (w : Nat) : List VmConstraint :=
  fieldsCompletionOffs.map (fun off => colEq (w + off) (w + AFTER_BLOCK_OFF + off))

/-- The fields completion freezes EXCLUDING the written slot `slot`'s 8 lanes — setField[0..7]'s 56
freezes (the SEVEN OTHER flat fields × 8 completion lanes each). The written slot's lane 0 is FORCED
by `gFieldWriteP1`; its eight completion lanes 1..8 are PUBLISHED by `withSetFieldCompletionPins`.
Freezing them here would be UNSOUND: a large-value write (`FieldElement = [u8;32]`) moves them off
zero, and `colEq (before = after)` would reject the honest write.

⚑ The excluded window is `fieldsSlotLanes slot` — the `fieldLaneCol` projection, NOT an arithmetic
range. It is two disjoint pieces (`113 + 7·slot .. +6` and the single column `176 + slot`), and a
range predicate cannot express that. -/
def fieldsCompletionFreezesExcept (slot : Fin 8) (w : Nat) : List VmConstraint :=
  (fieldsCompletionOffs.filter (fun off => !(fieldsSlotLanes slot).contains off)).map
    (fun off => colEq (w + off) (w + AFTER_BLOCK_OFF + off))

-- The freeze-EXCEPT wrap frees EXACTLY the written slot's eight lanes and freezes the other 56.
#guard (fieldsCompletionFreezesExcept 0 186).length == 56
#guard (fieldsCompletionFreezesExcept 7 186).length == 56
#guard (fieldsCompletionFreezes 186).length == 64

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
  -- wide-open authority into NEW_COMMIT) PLUS the 64 v14 fields[0..7] completion-lane freezes (every
  -- flat field UNCHANGED on a non-field-writing value turn — no forged higher-byte field can ride an
  -- innocuous value move). ONE appended right-operand so v1 stays the left operand.
  { r with constraints :=
      r.constraints ++ (frozenAuthorityColEqs d.traceWidth ++ fieldsCompletionFreezes d.traceWidth) }

/-- The continuity welds (r23 · lifecycle · perms · vk · mode · fields-root + the seven H1 headroom
authority limbs + the 64 v14 fields[0..7] completion lanes) are the only constraints past
`rotateV3`'s — so a VALUE turn cannot smuggle an authority-shape OR a forged field-completion change
into NEW_COMMIT. -/
theorem rotateV3FrozenAuthority_constraints (d : EffectVmDescriptor) :
    (rotateV3FrozenAuthority d).constraints
      = (rotateV3 d).constraints
          ++ (frozenAuthorityColEqs d.traceWidth ++ fieldsCompletionFreezes d.traceWidth) := rfl

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
        ≡ env.loc (d.traceWidth + AFTER_BLOCK_OFF + B_RECORD_DIGEST) [ZMOD 2013265921]
    ∧ env.loc (d.traceWidth + B_LIFECYCLE)
        ≡ env.loc (d.traceWidth + AFTER_BLOCK_OFF + B_LIFECYCLE) [ZMOD 2013265921] := by
  obtain ⟨hc, _, _⟩ := h
  refine ⟨?_, ?_⟩
  · have hmem : colEq (d.traceWidth + B_RECORD_DIGEST)
        (d.traceWidth + AFTER_BLOCK_OFF + B_RECORD_DIGEST) ∈ (rotateV3FrozenAuthority d).constraints := by
      rw [rotateV3FrozenAuthority_constraints]
      exact List.mem_append_right _ (List.mem_append_left _ (by simp [frozenAuthorityColEqs]))
    exact (colEq_holds_iff env isFirst isLast _ _ hlast).mp (hc _ hmem)
  · have hmem : colEq (d.traceWidth + B_LIFECYCLE)
        (d.traceWidth + AFTER_BLOCK_OFF + B_LIFECYCLE) ∈ (rotateV3FrozenAuthority d).constraints := by
      rw [rotateV3FrozenAuthority_constraints]
      exact List.mem_append_right _ (List.mem_append_left _ (by simp [frozenAuthorityColEqs]))
    exact (colEq_holds_iff env isFirst isLast _ _ hlast).mp (hc _ hmem)

/-- **(authority drift ⇒ UNSAT)** — the NEGATIVE TOOTH: a row whose AFTER `r23` differs from the BEFORE
`r23` (a value turn smuggling an authority change into NEW_COMMIT) does NOT satisfy
`rotateV3FrozenAuthority d`. This is the light-client bite: `verify_vm_descriptor2` alone rejects it,
no trusted post-cell needed. -/
theorem rotateV3FrozenAuthority_rejects_drift (hash : List ℤ → ℤ) (d : EffectVmDescriptor)
    (env : VmRowEnv) (isFirst isLast : Bool) (hlast : isLast = false)
    (hcanonBefore : 0 ≤ env.loc (d.traceWidth + B_RECORD_DIGEST)
        ∧ env.loc (d.traceWidth + B_RECORD_DIGEST) < 2013265921)
    (hcanonAfter : 0 ≤ env.loc (d.traceWidth + AFTER_BLOCK_OFF + B_RECORD_DIGEST)
        ∧ env.loc (d.traceWidth + AFTER_BLOCK_OFF + B_RECORD_DIGEST) < 2013265921)
    (hdrift : env.loc (d.traceWidth + B_RECORD_DIGEST)
        ≠ env.loc (d.traceWidth + AFTER_BLOCK_OFF + B_RECORD_DIGEST)) :
    ¬ satisfiedVm hash (rotateV3FrozenAuthority d) env isFirst isLast :=
  fun h => hdrift (canon_eq_of_modEq hcanonBefore hcanonAfter
    (rotateV3FrozenAuthority_freezes hash d env isFirst isLast hlast h).1)

/-- **The fields[0..7] completion lanes are FROZEN on a satisfying TRANSITION row of the shared value
wrap.** For any of the 64 fields completion offsets (the eight NINTH lanes included), a row
satisfying `rotateV3FrozenAuthority d` (a
non-field-writing VALUE turn) carries AFTER completion = BEFORE completion — the v13 fields GENTIAN
weld: no forged higher-byte field can ride an innocuous value move into NEW_COMMIT. -/
theorem rotateV3FrozenAuthority_freezes_fields (hash : List ℤ → ℤ) (d : EffectVmDescriptor)
    (env : VmRowEnv) (isFirst isLast : Bool) (hlast : isLast = false)
    (h : satisfiedVm hash (rotateV3FrozenAuthority d) env isFirst isLast)
    (off : Nat) (hoff : off ∈ fieldsCompletionOffs) :
    env.loc (d.traceWidth + off) ≡ env.loc (d.traceWidth + AFTER_BLOCK_OFF + off) [ZMOD 2013265921] := by
  obtain ⟨hc, _, _⟩ := h
  have hmem : colEq (d.traceWidth + off) (d.traceWidth + AFTER_BLOCK_OFF + off)
      ∈ (rotateV3FrozenAuthority d).constraints := by
    rw [rotateV3FrozenAuthority_constraints]
    exact List.mem_append_right _ (List.mem_append_right _
      (List.mem_map.mpr ⟨off, hoff, rfl⟩))
  exact (colEq_holds_iff env isFirst isLast _ _ hlast).mp (hc _ hmem)

/-- **TOOTH (fields-completion forge ⇒ UNSAT)** — a VALUE turn whose AFTER field completion lane
differs from BEFORE (a forged higher-byte field smuggled into NEW_COMMIT during an innocuous value
move) does NOT satisfy the shared value wrap. The light-client bite for the fields halves:
`verify_vm_descriptor2` alone rejects it, no trusted post-cell needed. -/
theorem rotateV3FrozenAuthority_rejects_fields_forge (hash : List ℤ → ℤ) (d : EffectVmDescriptor)
    (env : VmRowEnv) (isFirst isLast : Bool) (hlast : isLast = false)
    (off : Nat) (hoff : off ∈ fieldsCompletionOffs)
    (hcanonBefore : 0 ≤ env.loc (d.traceWidth + off)
        ∧ env.loc (d.traceWidth + off) < 2013265921)
    (hcanonAfter : 0 ≤ env.loc (d.traceWidth + AFTER_BLOCK_OFF + off)
        ∧ env.loc (d.traceWidth + AFTER_BLOCK_OFF + off) < 2013265921)
    (hforge : env.loc (d.traceWidth + off) ≠ env.loc (d.traceWidth + AFTER_BLOCK_OFF + off)) :
    ¬ satisfiedVm hash (rotateV3FrozenAuthority d) env isFirst isLast :=
  fun h => hforge (canon_eq_of_modEq hcanonBefore hcanonAfter
    (rotateV3FrozenAuthority_freezes_fields hash d env isFirst isLast hlast h off hoff))

#assert_axioms rotateV3FrozenAuthority_freezes_fields
#assert_axioms rotateV3FrozenAuthority_rejects_fields_forge

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
def v3OfFrozen (d : EffectVmDescriptor)
    (hAdm : ∀ s ∈ (rotateV3FrozenAuthority d).hashSites,
        ChipArityAdmitted s.inputs.length := by graduate_arity) :
    EffectVmDescriptor2 :=
  graduateV1 (rotateV3FrozenAuthority d) hAdm

-- The fee pin lands at PI slot 46 (one past the four rotated commit pins 34..37) and the rotated
-- fee'd transfer publishes 39 PIs over the SAME rotated width as the unfee'd transfer.
#guard (rotateV3WithFeePin (rotateV3FrozenAuthority EffectVmEmitTransfer.transferFeeVmDescriptor)).piCount == 40
#guard (rotateV3WithFeePin (rotateV3FrozenAuthority EffectVmEmitTransfer.transferFeeVmDescriptor)).traceWidth
        == EffectVmEmitTransfer.transferVmDescriptor.traceWidth + APPENDIX_SPAN

/-- **`transferFeeV3`** — the graduated rotated fee'd transfer descriptor (the deployed fee'd cohort
member; the frozen-authority + fee-pinned analog of `transferVmDescriptor2R24 = v3OfFrozen
transferVmDescriptor`). `piCount = 40`: the four rotated commit pins + the appended fee pin. The fee
column (`feeCol = saCol state.RESERVED`) is forced equal to the published fee PI on the last row, and
the augmented balance-lo gate forces the fee debit into the proven balance flow (`new = old −
transfer − fee`), so NEW_COMMIT binds the POST-fee balance and a ledgerless client needs no trusted
`+ fee` reconstruction. -/
def transferFeeV3 : EffectVmDescriptor2 :=
  graduateV1 (rotateV3WithFeePin (rotateV3FrozenAuthority EffectVmEmitTransfer.transferFeeVmDescriptor))

#guard transferFeeV3.piCount == 40
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
    (hf : Satisfied2Faithful permOut hash (v3OfFrozen d (sitesFit_admitted (graduable_spec (graduable_rotateV3FrozenAuthority hgrad)).2.1)) minit mfin maddrs t) :
    ∀ i, i < t.rows.length →
      satisfiedVm hash d (envAt t i) (i == 0) (i + 1 == t.rows.length) := by
  intro i hi
  exact rotateV3FrozenAuthority_satisfiedVm_v1 hash d _ _ _
    (satisfied2Faithful_satisfiedVm permOut hash (rotateV3FrozenAuthority d) minit mfin maddrs t
      (graduable_rotateV3FrozenAuthority hgrad) hf i hi)

/-! ### The setField[0..7] frozen wrap — fields freezes EXCLUDING the written slot.

setField[0..7] WRITES its flat field, so the shared `rotateV3FrozenAuthority` (which freezes all 56
fields completion lanes) would over-freeze the written slot and reject an honest large-value write
(`FieldElement = [u8;32]`). This wrap keeps the authority freezes verbatim but swaps the fields
freezes for `fieldsCompletionFreezesExcept slot` (the OTHER seven flat fields, 49 lanes). The written
slot's lane 0 is FORCED by `gFieldWriteP1`; its seven completion lanes 1..7 are the ONE named residual
(the setField VALUE8 weld — forcing them to the declared value8 params — is the deliberately-gated
follow-on). Structurally identical to `rotateV3FrozenAuthority` (additive over `rotateV3`), so the
per-effect setField keystones lift verbatim. -/
def rotateV3FrozenAuthoritySetField (slot : Fin 8) (d : EffectVmDescriptor) : EffectVmDescriptor :=
  let r := rotateV3 d
  { r with constraints :=
      r.constraints
        ++ (frozenAuthorityColEqs d.traceWidth ++ fieldsCompletionFreezesExcept slot d.traceWidth) }

theorem rotateV3FrozenAuthoritySetField_constraints (slot : Fin 8) (d : EffectVmDescriptor) :
    (rotateV3FrozenAuthoritySetField slot d).constraints
      = (rotateV3 d).constraints
          ++ (frozenAuthorityColEqs d.traceWidth ++ fieldsCompletionFreezesExcept slot d.traceWidth) := rfl

theorem graduable_rotateV3FrozenAuthoritySetField {slot : Fin 8} {d : EffectVmDescriptor}
    (h : graduable d = true) : graduable (rotateV3FrozenAuthoritySetField slot d) = true := by
  have hr := graduable_rotateV3 h
  unfold rotateV3FrozenAuthoritySetField
  unfold graduable at hr ⊢
  simpa using hr

/-- The v1 denotation survives the setField continuity welds (the per-effect setField faithfulness
lifts through, exactly as for the shared authority wrap). -/
theorem rotateV3FrozenAuthoritySetField_satisfiedVm_v1 (slot : Fin 8) (hash : List ℤ → ℤ)
    (d : EffectVmDescriptor) (env : VmRowEnv) (isFirst isLast : Bool)
    (h : satisfiedVm hash (rotateV3FrozenAuthoritySetField slot d) env isFirst isLast) :
    satisfiedVm hash d env isFirst isLast := by
  apply rotateV3_satisfiedVm_v1 hash d env isFirst isLast
  obtain ⟨hc, hsites, hr⟩ := h
  refine ⟨fun c hc' => hc c ?_, hsites, hr⟩
  rw [rotateV3FrozenAuthoritySetField_constraints]
  exact List.mem_append_left _ hc'

/-- **`v3OfFrozenSetField slot d`** — the graduated setField[0..7] descriptor (the fields-freeze-except
variant of `v3OfFrozen`). Same width/piCount/graduability (the freezes are appended `colEq`s, no new
column), so every setField `#guard` and per-effect value theorem lifts verbatim. -/
def v3OfFrozenSetField (slot : Fin 8) (d : EffectVmDescriptor)
    (hAdm : ∀ s ∈ (rotateV3FrozenAuthoritySetField slot d).hashSites,
        ChipArityAdmitted s.inputs.length := by graduate_arity) : EffectVmDescriptor2 :=
  graduateV1 (rotateV3FrozenAuthoritySetField slot d) hAdm

/-- A `Satisfied2` witness of the setField frozen graduation yields the full v1 denotation on every
row (the setField analog of `rotV3Frozen_sound_v1`). -/
theorem rotV3FrozenSetField_sound_v1 (slot : Fin 8) (permOut : List ℤ → List ℤ) (hash : List ℤ → ℤ)
    (d : EffectVmDescriptor)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hgrad : graduable d = true)
    (hf : Satisfied2Faithful permOut hash (v3OfFrozenSetField slot d (sitesFit_admitted (graduable_spec (graduable_rotateV3FrozenAuthoritySetField hgrad)).2.1)) minit mfin maddrs t) :
    ∀ i, i < t.rows.length →
      satisfiedVm hash d (envAt t i) (i == 0) (i + 1 == t.rows.length) := by
  intro i hi
  exact rotateV3FrozenAuthoritySetField_satisfiedVm_v1 slot hash d _ _ _
    (satisfied2Faithful_satisfiedVm permOut hash (rotateV3FrozenAuthoritySetField slot d) minit mfin maddrs t
      (graduable_rotateV3FrozenAuthoritySetField hgrad) hf i hi)

/-- **`setFieldV3 slot`** — the rotated tick-faced setField (the registry member). setField[0..7] is a
VALUE effect, so it carries the authority-frame freeze AND the v13 fields completion freezes for the
seven OTHER flat fields (`v3OfFrozenSetField`); its own written slot's lane 0 is `gFieldWriteP1`-forced
and its 8 completion lanes are PUBLISHED by `withSetFieldCompletionPins`. -/
def setFieldV3 (slot : Fin 8) : EffectVmDescriptor2 := v3OfFrozenSetField slot (setFieldTickFace slot)

/-- **The nonce TICK holds on a satisfying non-NoOp setField row.** A row satisfying the rotated
tick-faced setField, with `s_noop = 0`, carries `after_nonce = before_nonce + 1` (the runtime
tick) — the rotated re-statement of the transfer/noteSpend nonce gate, now on setField. -/
theorem setFieldV3_pins_nonce_tick (slot : Fin 8) (hash : List ℤ → ℤ) (env : VmRowEnv)
    (isFirst isLast : Bool) (hlast : isLast = false) (hnoop : env.loc sel.NOOP = 0)
    (h : satisfiedVm hash (rotateV3 (setFieldTickFace slot)) env isFirst isLast) :
    env.loc (saCol state.NONCE) ≡ env.loc (sbCol state.NONCE) + 1 [ZMOD 2013265921] := by
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
  exact (gate_modEq_iff (by ring)).mp hg

/-- **ANTI-GHOST (wrong nonce delta ⇒ UNSAT)** — the C7 soundness tooth for setField. A non-NoOp
row whose nonce delta is NOT the tick (`after_nonce ≠ before_nonce + 1`) does NOT satisfy the
rotated tick-faced setField: the swapped tick gate REJECTS it. A forged passthrough
(`after = before`) is the special case the FREEZE descriptor wrongly accepted; it is now UNSAT. -/
theorem setFieldTick_rejects_wrong_nonce_delta (slot : Fin 8) (hash : List ℤ → ℤ) (env : VmRowEnv)
    (isFirst isLast : Bool) (hlast : isLast = false) (hnoop : env.loc sel.NOOP = 0)
    (hcanonAfter : 0 ≤ env.loc (saCol state.NONCE) ∧ env.loc (saCol state.NONCE) < 2013265921)
    (hcanonBeforeTick : 0 ≤ env.loc (sbCol state.NONCE) + 1
      ∧ env.loc (sbCol state.NONCE) + 1 < 2013265921)
    (hwrong : env.loc (saCol state.NONCE) ≠ env.loc (sbCol state.NONCE) + 1) :
    ¬ satisfiedVm hash (rotateV3 (setFieldTickFace slot)) env isFirst isLast :=
  fun h => hwrong (canon_eq_of_modEq hcanonAfter hcanonBeforeTick
    (setFieldV3_pins_nonce_tick slot hash env isFirst isLast hlast hnoop h))

/-- **The corrected WRITE binds the runtime value column on the ACTIVE row.** A row satisfying the
rotated param1-corrected setField with `s_set_field = 1` (the active setField row) carries
`fields[slot]_after = param1` (the runtime NEW_VALUE) — the selector-gated write gate, on the
active row, reads the column the trace generator wrote the value to. (On NoOp rows
`s_set_field = 0` the gate vanishes, so the binding is exactly the runtime's gated semantics.) -/
theorem setFieldV3_pins_value (slot : Fin 8) (hash : List ℤ → ℤ) (env : VmRowEnv)
    (isFirst isLast : Bool) (hlast : isLast = false) (hactive : env.loc SEL_SET_FIELD_COL = 1)
    (h : satisfiedVm hash (rotateV3 (setFieldTickFace slot)) env isFirst isLast) :
    env.loc (saCol (state.FIELD_BASE + slot.val)) ≡ env.loc (prmCol RUNTIME_VALUE_PARAM)
      [ZMOD 2013265921] := by
  subst hlast
  have hmem : VmConstraint.gate (gFieldWriteP1 slot) ∈ (rotateV3 (setFieldTickFace slot)).constraints := by
    apply List.mem_append_left
    show _ ∈ setFieldRowGatesTick slot
    simp [setFieldRowGatesTick]
  have hg := h.1 _ hmem
  simp only [VmConstraint.holdsVm, gFieldWriteP1, EffectVmEmitTransfer.eSub,
    EffectVmEmitTransfer.eSA, EffectVmEmitTransfer.ePrm, EmittedExpr.eval] at hg
  rw [hactive] at hg
  exact (gate_modEq_iff (by ring)).mp hg

/-- **ANTI-GHOST (wrong written value ⇒ UNSAT)** — the C7 param-column soundness tooth for
setField. An ACTIVE setField row (`s_set_field = 1`) whose written field does NOT equal `param1`
(the runtime value column) does NOT satisfy the corrected descriptor: the gated write gate, on the
active row, REJECTS it. -/
theorem setFieldP1_rejects_wrong_value (slot : Fin 8) (hash : List ℤ → ℤ) (env : VmRowEnv)
    (isFirst isLast : Bool) (hlast : isLast = false) (hactive : env.loc SEL_SET_FIELD_COL = 1)
    (hcanonAfter : 0 ≤ env.loc (saCol (state.FIELD_BASE + slot.val))
      ∧ env.loc (saCol (state.FIELD_BASE + slot.val)) < 2013265921)
    (hcanonParam : 0 ≤ env.loc (prmCol RUNTIME_VALUE_PARAM)
      ∧ env.loc (prmCol RUNTIME_VALUE_PARAM) < 2013265921)
    (hwrong : env.loc (saCol (state.FIELD_BASE + slot.val)) ≠ env.loc (prmCol RUNTIME_VALUE_PARAM)) :
    ¬ satisfiedVm hash (rotateV3 (setFieldTickFace slot)) env isFirst isLast :=
  fun h => hwrong (canon_eq_of_modEq hcanonAfter hcanonParam
    (setFieldV3_pins_value slot hash env isFirst isLast hlast hactive h))

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

/-- **`mintV3`** — the rotated tick-faced BridgeMint (the `mintVmDescriptor2R24` registry member). -/
def mintV3 : EffectVmDescriptor2 := v3OfFrozen mintTickFace

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
    env.loc (saCol state.NONCE) ≡ env.loc (sbCol state.NONCE) + 1 [ZMOD 2013265921] := by
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
  exact (gate_modEq_iff (by ring)).mp hg

/-- **ANTI-GHOST (wrong nonce delta ⇒ UNSAT)** — the C7 soundness tooth for BridgeMint. -/
theorem mintTick_rejects_wrong_nonce_delta (hash : List ℤ → ℤ) (env : VmRowEnv)
    (isFirst isLast : Bool) (hlast : isLast = false) (hnoop : env.loc sel.NOOP = 0)
    (hcanonAfter : 0 ≤ env.loc (saCol state.NONCE) ∧ env.loc (saCol state.NONCE) < 2013265921)
    (hcanonBeforeTick : 0 ≤ env.loc (sbCol state.NONCE) + 1
      ∧ env.loc (sbCol state.NONCE) + 1 < 2013265921)
    (hwrong : env.loc (saCol state.NONCE) ≠ env.loc (sbCol state.NONCE) + 1) :
    ¬ satisfiedVm hash (rotateV3 mintTickFace) env isFirst isLast :=
  fun h => hwrong (canon_eq_of_modEq hcanonAfter hcanonBeforeTick
    (mintV3_pins_nonce_tick hash env isFirst isLast hlast hnoop h))

/-- **The corrected CREDIT binds the runtime value column.** A row satisfying the rotated
param1-corrected BridgeMint carries `bal_lo_after = bal_lo_before + param1` (the runtime
value_lo) — the credit gate now reads the column the trace generator credited from. -/
theorem mintV3_pins_credit (hash : List ℤ → ℤ) (env : VmRowEnv) (isFirst isLast : Bool)
    (hlast : isLast = false)
    (h : satisfiedVm hash (rotateV3 mintTickFace) env isFirst isLast) :
    env.loc (saCol state.BALANCE_LO)
      ≡ env.loc (sbCol state.BALANCE_LO) + env.loc (prmCol RUNTIME_VALUE_PARAM)
        [ZMOD 2013265921] := by
  subst hlast
  have hmem : VmConstraint.gate gBalLoCreditP1 ∈ (rotateV3 mintTickFace).constraints := by
    apply List.mem_append_left
    show _ ∈ mintTickFace.constraints
    simp [mintTickFace, mintRowGatesTick]
  have hg := h.1 _ hmem
  simp only [VmConstraint.holdsVm, gBalLoCreditP1, EffectVmEmitTransfer.eSub,
    EffectVmEmitTransfer.eSA, EffectVmEmitTransfer.eSB, EffectVmEmitTransfer.ePrm,
    EmittedExpr.eval] at hg
  exact (gate_modEq_iff (by ring)).mp hg

/-- **ANTI-GHOST (wrong credit ⇒ UNSAT)** — the C7 param-column soundness tooth for BridgeMint.
A row whose post-balance is NOT `before + param1` (the runtime value_lo) is UNSAT. -/
theorem mintP1_rejects_wrong_credit (hash : List ℤ → ℤ) (env : VmRowEnv) (isFirst isLast : Bool)
    (hlast : isLast = false)
    (hcanonAfter : 0 ≤ env.loc (saCol state.BALANCE_LO)
      ∧ env.loc (saCol state.BALANCE_LO) < 2013265921)
    (hcanonCredit : 0 ≤ env.loc (sbCol state.BALANCE_LO) + env.loc (prmCol RUNTIME_VALUE_PARAM)
      ∧ env.loc (sbCol state.BALANCE_LO) + env.loc (prmCol RUNTIME_VALUE_PARAM) < 2013265921)
    (hwrong : env.loc (saCol state.BALANCE_LO)
      ≠ env.loc (sbCol state.BALANCE_LO) + env.loc (prmCol RUNTIME_VALUE_PARAM)) :
    ¬ satisfiedVm hash (rotateV3 mintTickFace) env isFirst isLast :=
  fun h => hwrong (canon_eq_of_modEq hcanonAfter hcanonCredit
    (mintV3_pins_credit hash env isFirst isLast hlast h))

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
#guard mintV3.traceWidth ==
  EFFECT_VM_WIDTH + APPENDIX_SPAN + (CHIP_OUT_LANES - 1) *
    (rotateV3FrozenAuthority mintTickFace).hashSites.length
#guard (setFieldV3 0).piCount == 39
#guard mintV3.piCount == 39
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
#guard (let env : VmRowEnv := ⟨fun c => if c == 56 then 5 else if c == 78 then 6 else 0, fun _ => 0, fun _ => 0, fun _ => 0⟩;
        decide ((EffectVmEmitTransfer.gNonce).eval env.loc = 0))   -- tick (5→6) ⇒ gate holds
#guard (let env : VmRowEnv := ⟨fun c => if c == 56 then 5 else if c == 78 then 5 else 0, fun _ => 0, fun _ => 0, fun _ => 0⟩;
        decide ((EffectVmEmitTransfer.gNonce).eval env.loc ≠ 0))   -- passthrough (5→5) ⇒ gate REJECTS
-- The corrected WRITE/CREDIT gates read `prmCol 1` (NEW_VALUE / value_lo = col PARAM_BASE+1 = 69),
-- NOT `prmCol 0` (FIELD_INDEX / MINT_HASH = col 68). Positional witness + both polarities.
#guard prmCol RUNTIME_VALUE_PARAM == 69
-- setField WRITE (selector-gated by s_set_field = col SEL_SET_FIELD_COL = 2): on the ACTIVE row
-- (s_set_field = 1), field0_after (saCol FIELD_BASE = 79) == param1 (69). Match holds; mismatch
-- rejects. On a NoOp row (s_set_field = 0) the gate VANISHES (third guard).
#guard (let env : VmRowEnv := ⟨fun c => if c == 2 then 1 else if c == 79 then 7 else if c == 69 then 7 else 0, fun _ => 0, fun _ => 0, fun _ => 0⟩;
        decide ((gFieldWriteP1 0).eval env.loc = 0))   -- active + (field0_after == param1) ⇒ holds
#guard (let env : VmRowEnv := ⟨fun c => if c == 2 then 1 else if c == 79 then 7 else if c == 69 then 9 else 0, fun _ => 0, fun _ => 0, fun _ => 0⟩;
        decide ((gFieldWriteP1 0).eval env.loc ≠ 0))   -- active + (field0_after ≠ param1) ⇒ REJECTS
#guard (let env : VmRowEnv := ⟨fun c => if c == 79 then 7 else if c == 69 then 9 else 0, fun _ => 0, fun _ => 0, fun _ => 0⟩;
        decide ((gFieldWriteP1 0).eval env.loc = 0))   -- NoOp (s_set_field = 0) ⇒ gate VANISHES
-- mint CREDIT: bal_lo_after (76) == bal_lo_before (54) + param1 (69). Honest credit holds; wrong rejects.
#guard (let env : VmRowEnv := ⟨fun c => if c == 54 then 100 else if c == 76 then 130 else if c == 69 then 30 else 0, fun _ => 0, fun _ => 0, fun _ => 0⟩;
        decide (gBalLoCreditP1.eval env.loc = 0))   -- 130 == 100 + 30 ⇒ holds
#guard (let env : VmRowEnv := ⟨fun c => if c == 54 then 100 else if c == 76 then 999 else if c == 69 then 30 else 0, fun _ => 0, fun _ => 0, fun _ => 0⟩;
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
    env.loc (d.traceWidth + AFTER_BLOCK_OFF + off) ≡ env.pub (rotateV3 d).piCount [ZMOD 2013265921] := by
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
    (hcanonLimb : 0 ≤ env.loc (d.traceWidth + AFTER_BLOCK_OFF + off)
      ∧ env.loc (d.traceWidth + AFTER_BLOCK_OFF + off) < 2013265921)
    (hcanonPI : 0 ≤ env.pub (rotateV3 d).piCount ∧ env.pub (rotateV3 d).piCount < 2013265921)
    (hwrong : env.loc (d.traceWidth + AFTER_BLOCK_OFF + off) ≠ env.pub (rotateV3 d).piCount) :
    ¬ satisfiedVm hash (rotateV3WithRecordPin off d) env isFirst true :=
  fun h => hwrong (canon_eq_of_modEq hcanonLimb hcanonPI
    (rotateV3WithRecordPin_pins off hash d env isFirst h))

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
    env.loc col ≡ const [ZMOD 2013265921] := by
  subst hlast
  simp only [discForceGate, VmConstraint.holdsVm, EmittedExpr.eval] at h
  rw [hsel] at h
  exact (gate_modEq_iff (by ring)).mp h

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
    env.loc (afterDiscCol d.traceWidth) ≡ afterC [ZMOD 2013265921] :=
  discForceGate_forces env isFirst isLast hlast sel (afterDiscCol d.traceWidth) afterC hsel
    (h.1 _ (rotateV3WithDiscGate_afterMem sel beforeC? afterC d))

/-- **TOOTH — `rotateV3WithDiscGate_rejects_wrong_after`.** An ACTIVE row whose AFTER disc is NOT the
mandated `afterC` (a frozen seal, a Destroyed→Live resurrection, a wrong-disc archive) does NOT satisfy
`rotateV3WithDiscGate` — UNSAT for a ledgerless client, no anchor. -/
theorem rotateV3WithDiscGate_rejects_wrong_after (sel : Nat) (beforeC? : Option ℤ) (afterC : ℤ)
    (hash : List ℤ → ℤ) (d : EffectVmDescriptor) (env : VmRowEnv) (isFirst isLast : Bool)
    (hlast : isLast = false)
    (hsel : env.loc sel = 1)
    (hcanonAfter : 0 ≤ env.loc (afterDiscCol d.traceWidth)
      ∧ env.loc (afterDiscCol d.traceWidth) < 2013265921)
    (hcanonConst : 0 ≤ afterC ∧ afterC < 2013265921)
    (hwrong : env.loc (afterDiscCol d.traceWidth) ≠ afterC) :
    ¬ satisfiedVm hash (rotateV3WithDiscGate sel beforeC? afterC d) env isFirst isLast :=
  fun h => hwrong (canon_eq_of_modEq hcanonAfter hcanonConst
    (rotateV3WithDiscGate_forces_after sel beforeC? afterC hash d env isFirst isLast hlast hsel h))

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
    env.loc afterCol ≡ env.loc paramCol [ZMOD 2013265921] := by
  subst hlast
  simp only [permsVKWeldGate, VmConstraint.holdsVm, EmittedExpr.eval] at h
  rw [hsel] at h
  exact (gate_modEq_iff (by ring)).mp h

/-- The AFTER perms-digest force column for a mover of width `w` (limb `B_PERMS` of the AFTER block). -/
def afterPermsCol (w : Nat) : Nat := w + AFTER_BLOCK_OFF + B_PERMS
/-- The AFTER vk-digest force column (limb `B_VK` of the AFTER block). -/
def afterVKCol (w : Nat) : Nat := w + AFTER_BLOCK_OFF + B_VK
/-- The in-circuit declared-param column the live setPerms / setVK row anchors `permsHash[0]` /
`vkHash[0]` into (`params[0]`, `prmCol 0`) — itself bound (all 8 limbs) into the PI-anchored
`effects_hash`. -/
def declaredParamCol : Nat := prmCol 0

/-- The FIRST perms-digest COMPLETION limb (post REVOKED-ROOT flag day: `revoked_root` took base limb
37, shifting every limb ≥ 37 by +1). The 7 faithful completion felts `permsHash[1..7]` ride limbs
38..=44; the committed lane-0 stays at `B_PERMS`. THE SINGLE SOURCE for this offset — the producer
(`turn::rotation_witness`, `write_lanes([B_PERMS, 38..=44])`) reads it from the generated layout, so
the constraint and the witness CANNOT disagree. They did once: this weld sat at 37 (i.e. ON
`revoked_root` lane-0) while the producer wrote at 38, and every honest setPermissions turn was UNSAT. -/
def B_PERMS_COMPLETION : Nat := layoutGroupCol .perms 1
/-- The FIRST vk-digest COMPLETION limb; the 7 felts `vkHash[1..7]` ride limbs 45..=51 (committed lane-0
stays at `B_VK`). Same single-source contract as `B_PERMS_COMPLETION`. -/
def B_VK_COMPLETION : Nat := layoutGroupCol .vk 1

/-- **v10**: the FIRST faithful-8-felt completion COLUMN for the perms digest in the AFTER block. -/
def afterPermsExtraCol (w : Nat) : Nat := w + AFTER_BLOCK_OFF + B_PERMS_COMPLETION
/-- **v10**: the FIRST faithful-8-felt completion COLUMN for the vk digest in the AFTER block. -/
def afterVKExtraCol (w : Nat) : Nat := w + AFTER_BLOCK_OFF + B_VK_COMPLETION

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
    env.loc afterCol ≡ env.loc declaredParamCol [ZMOD 2013265921] :=
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
    (hcanonAfter : 0 ≤ env.loc afterCol ∧ env.loc afterCol < 2013265921)
    (hcanonParam : 0 ≤ env.loc declaredParamCol ∧ env.loc declaredParamCol < 2013265921)
    (hforged : env.loc afterCol ≠ env.loc declaredParamCol) :
    ¬ satisfiedVm hash (rotateV3WithPermsVKGate sel afterCol d) env isFirst isLast :=
  fun h => hforged (canon_eq_of_modEq hcanonAfter hcanonParam
    (rotateV3WithPermsVKGate_forces sel afterCol hash d env isFirst isLast hlast hsel h))

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
    env.loc afterCol ≡ env.loc payloadCol [ZMOD 2013265921] := by
  subst hlast
  simp only [lifecyclePayloadHashGate, VmConstraint.holdsVm, EmittedExpr.eval] at h
  rw [hsel] at h
  exact (gate_modEq_iff (by ring)).mp h

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
    env.loc (afterLifecycleCol d.traceWidth) ≡ env.loc declaredLifecyclePayloadCol [ZMOD 2013265921] :=
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
    (hcanonAfter : 0 ≤ env.loc (afterLifecycleCol d.traceWidth)
      ∧ env.loc (afterLifecycleCol d.traceWidth) < 2013265921)
    (hcanonPayload : 0 ≤ env.loc declaredLifecyclePayloadCol
      ∧ env.loc declaredLifecyclePayloadCol < 2013265921)
    (hforged : env.loc (afterLifecycleCol d.traceWidth) ≠ env.loc declaredLifecyclePayloadCol) :
    ¬ satisfiedVm hash (rotateV3WithLifecyclePayloadGate sel beforeC? afterC d) env isFirst isLast :=
  fun h => hforged (canon_eq_of_modEq hcanonAfter hcanonPayload
    (rotateV3WithLifecyclePayloadGate_forces sel beforeC? afterC hash d env isFirst isLast hlast hsel h))

/-- The AFTER-disc gate is STILL forced under the payload-gate layer (the payload weld is appended past
the disc gates, so the disc-gate membership survives) — the composed mover forces BOTH the disc (state)
AND the payload felt. -/
theorem rotateV3WithLifecyclePayloadGate_forces_disc (sel : Nat) (beforeC? : Option ℤ) (afterC : ℤ)
    (hash : List ℤ → ℤ) (d : EffectVmDescriptor) (env : VmRowEnv) (isFirst isLast : Bool)
    (hlast : isLast = false)
    (hsel : env.loc sel = 1)
    (h : satisfiedVm hash (rotateV3WithLifecyclePayloadGate sel beforeC? afterC d) env isFirst isLast) :
    env.loc (afterDiscCol d.traceWidth) ≡ afterC [ZMOD 2013265921] := by
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
    env.loc (afterModeCol d.traceWidth) ≡ afterC [ZMOD 2013265921] :=
  discForceGate_forces env isFirst isLast hlast sel (afterModeCol d.traceWidth) afterC hsel
    (h.1 _ (rotateV3WithModeGate_mem sel afterC d))

/-- **TOOTH — `rotateV3WithModeGate_rejects_unpromoted`.** An ACTIVE row whose committed AFTER mode is
NOT the mandated `afterC` (a makeSovereign whose committed mode stays `Hosted(0)` — an un-promoted
sovereign) does NOT satisfy `rotateV3WithModeGate` — UNSAT for a ledgerless client, no anchor. -/
theorem rotateV3WithModeGate_rejects_unpromoted (sel : Nat) (afterC : ℤ)
    (hash : List ℤ → ℤ) (d : EffectVmDescriptor) (env : VmRowEnv) (isFirst isLast : Bool)
    (hlast : isLast = false)
    (hsel : env.loc sel = 1)
    (hcanonAfter : 0 ≤ env.loc (afterModeCol d.traceWidth)
      ∧ env.loc (afterModeCol d.traceWidth) < 2013265921)
    (hcanonConst : 0 ≤ afterC ∧ afterC < 2013265921)
    (hwrong : env.loc (afterModeCol d.traceWidth) ≠ afterC) :
    ¬ satisfiedVm hash (rotateV3WithModeGate sel afterC d) env isFirst isLast :=
  fun h => hwrong (canon_eq_of_modEq hcanonAfter hcanonConst
    (rotateV3WithModeGate_forces_after sel afterC hash d env isFirst isLast hlast hsel h))

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
    env.loc afterCol ≡ env.loc declaredFieldsRootCol [ZMOD 2013265921] :=
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
    (hcanonAfter : 0 ≤ env.loc afterCol ∧ env.loc afterCol < 2013265921)
    (hcanonParam : 0 ≤ env.loc declaredFieldsRootCol ∧ env.loc declaredFieldsRootCol < 2013265921)
    (hforged : env.loc afterCol ≠ env.loc declaredFieldsRootCol) :
    ¬ satisfiedVm hash (rotateV3WithFieldsRootGate sel afterCol d) env isFirst isLast :=
  fun h => hforged (canon_eq_of_modEq hcanonAfter hcanonParam
    (rotateV3WithFieldsRootGate_forces sel afterCol hash d env isFirst isLast hlast hsel h))

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
    env.loc (d.traceWidth + AFTER_BLOCK_OFF + off) ≡ anchor [ZMOD 2013265921] := by
  have hpin := rotateV3WithRecordPin_pins off hash d env isFirst h
  unfold PayloadAnchored at hanchor
  calc env.loc (d.traceWidth + AFTER_BLOCK_OFF + off)
      ≡ env.pub (rotateV3 d).piCount [ZMOD 2013265921] := hpin
    _ = anchor := hanchor

/-- **TOOTH — `rotateV3WithPayloadColumn_rejects_forged` (LIGHT-CLIENT).** A LAST row whose committed
AFTER payload sub-limb is NOT the verifier-recomputed `anchor` (a refusal forged to a different
`fields_root` audit; a cellSeal forged to a different `reason_hash`/`sealed_at`; an emitEvent forged to a
different topic/payload) does NOT satisfy `rotateV3WithPayloadColumn off d` once the verifier anchors the
slot — UNSAT for a LEDGERLESS client, no trusted post-cell. This is the residual CONVERTED: the forged
payload that the bare record pin accepted (producer-free PI) is now REJECTED (verifier-anchored PI). -/
theorem rotateV3WithPayloadColumn_rejects_forged (off : Nat) (hash : List ℤ → ℤ)
    (d : EffectVmDescriptor) (env : VmRowEnv) (isFirst : Bool) (anchor : ℤ)
    (hanchor : PayloadAnchored env d anchor)
    (hcanonLimb : 0 ≤ env.loc (d.traceWidth + AFTER_BLOCK_OFF + off)
      ∧ env.loc (d.traceWidth + AFTER_BLOCK_OFF + off) < 2013265921)
    (hcanonAnchor : 0 ≤ anchor ∧ anchor < 2013265921)
    (hforged : env.loc (d.traceWidth + AFTER_BLOCK_OFF + off) ≠ anchor) :
    ¬ satisfiedVm hash (rotateV3WithPayloadColumn off d) env isFirst true :=
  fun h => hforged (canon_eq_of_modEq hcanonLimb hcanonAnchor
    (rotateV3WithPayloadColumn_forces_anchor off hash d env isFirst anchor hanchor h))

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
    (hcanonLimb : 0 ≤ env.loc (EffectVmEmitCellSeal.cellSealVmDescriptor.traceWidth + AFTER_BLOCK_OFF + B_LIFECYCLE)
      ∧ env.loc (EffectVmEmitCellSeal.cellSealVmDescriptor.traceWidth + AFTER_BLOCK_OFF + B_LIFECYCLE) < 2013265921)
    (hcanonAnchor : 0 ≤ anchor ∧ anchor < 2013265921)
    (hforged : env.loc (EffectVmEmitCellSeal.cellSealVmDescriptor.traceWidth + AFTER_BLOCK_OFF + B_LIFECYCLE)
      ≠ anchor) :
    ¬ satisfiedVm hash (rotateV3WithPayloadColumn B_LIFECYCLE EffectVmEmitCellSeal.cellSealVmDescriptor)
      env isFirst true :=
  rotateV3WithPayloadColumn_rejects_forged B_LIFECYCLE hash _ env isFirst anchor hanchor
    hcanonLimb hcanonAnchor hforged

#assert_axioms cellSealV3_payload_rejects_forged

/-! ### §5.PC.EH — THE effects_hash SUB-CASE (emitEvent / pipelinedSend / exercise).

⚑ **THE PARAGRAPH THAT STOOD HERE WAS FALSE, AND IT WAS THE STATED REASON THESE THREE EFFECTS HAVE
NO DECLARED-PAYLOAD COLUMN.** It read: *"the v1 descriptor pi-binds that slot to the row's
`compute_effects_hash` of the declared params — the SAME perms/VK chain (`prmCol i → effects_hash
→ PI`) … So `verify_vm_descriptor2` ALONE already checks the declared hash against a
producer-non-free PI."* It reasoned from the **v1 hand-AIR**, which is **RETIRED**
(`circuit/src/effect_vm/air.rs:7-10`: *"The v1 hand-AIR (`EffectVmAir` + its `StarkAir` impl) is
RETIRED; the rotated IR-v2 multi-table descriptor is the sole effect-VM circuit"*). Nothing
inherited that binding. The correction was already written twenty lines from its own restatement,
in `sdk/src/full_turn_proof.rs:870-897`.

**MEASURED at HEAD (2026-07-30), four independent ways:**

1. **No descriptor binds the slot.** `PI[16..20)` (`pi.rs::EFFECTS_HASH_BASE = 16`,
   `EFFECTS_HASH_LEN = 4`) carries ZERO `piBinding` in any deployed member.
   `circuit/tests/vk_epoch_misc_light_client_binding.rs:196-210` asserts exactly this as a
   PRECONDITION: `(16..20).all(|p| !bound_pis.contains(&p))`.
2. **The witness columns are gone, and the deletion is a machine-derived proof they were
   unconstrained.** `compute_effects_hash_4`'s two witness felts landed at `AUX_BASE + 4/5`
   = abs. cols 94/95 (`trace.rs:1118-1119`). `e1_compact_generated.rs`'s kill-set is *"every column
   at index ≥ 90 referenced by NO surviving constraint / hash site / range"*, and it deletes
   `[90, 98)` in **all 57** wide members. Cols 94/95 were droppable **because** nothing read them.
3. **Only the PROVER computes it.** `compute_effects_hash_4` has exactly one non-test caller —
   `circuit/src/effect_vm/trace.rs:1289`, the trace generator, writing `public_inputs[16..20]`.
   No verifier calls it on the deployed path.
4. **`pi.rs` says so in its own audit note.** `AUDIT[stage1-pi-only-bound]` (`pi.rs:862-867`):
   `PI[EFFECTS_HASH_BASE+1..+4]` is *"bound only by the executor's PI matching loop … not by
   per-row AIR constraints"* — and since the hand-AIR's retirement that now covers position 0 too.

**What actually holds the value up.** On the **full node**, `verify_and_commit_proof_rotated`
(`turn/src/executor/proof_verify.rs:711`) re-derives the pre-state from the ledger, converts the
turn's own effects (`:773`), REGENERATES the trace and the whole PI vector, and substitutes ITS
vector into `verify_batch` (`:1745`). A proof minted over different effects diverges the
Fiat–Shamir transcript and fails. That is real — and it means **the proof adds nothing the host did
not already compute**. On the **ledgerless** path (`sdk/src/full_turn_proof.rs:4460`) the PI vector
comes off the wire and is **free**.

**And the row cannot carry the preimage anyway.** `NUM_PARAMS = 8` (`columns.rs:233`), and
`trace.rs:754-766` parks only the **low 4 felts** of `topic_hash` and the **low 4** of
`payload_hash` into `params[0..8]` — while `effects_hash_inputs` absorbs **all 8 limbs of each**
(tag + 16 = 17 felts). Nine of emitEvent's seventeen preimage felts are **not columns at all**. So
the old text's "the topic/payload digests ride the row's params OFF-trace" was true; its inference
that a PI binding compensated was not.

**Consequence, stated at current resolution:** a turn's rotated proof establishes that two
committed cell-states are joined by a chain of legal balance/nonce moves in one effect family, and
**not what the effects were**. `vk_epoch_misc_light_client_binding.rs` asserts the hole open, on
purpose, in three tests whose green depends on the forgery being ACCEPTED — see
`Dregg2.Circuit.Emit.EffectVmEffectsHashPin` for the pin that must invert them.

**These three effects therefore DO need a declared block.** Being STATELESS / FREEZE-ALL
(`emitEvent` rides `v3OfFrozen = rotateV3FrozenAuthority`; every authority limb is frozen to the
BEFORE) removes the AFTER SUB-LIMB to forge — it does not put the declaration on the wire. The
declaration is the whole content of these effects, and today it is published by nobody and
constrained by nothing. -/

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
limb-0 record pin (`B_RECORD_DIGEST` → PI 39) forces ONLY limb-0; this appends 7 last-row PI pins binding
the 7 HEADROOM authority limbs (AFTER-block offsets 12..=18 = limb-1..7 of the faithful 8-felt
`compute_authority_digest_8`) to the next 7 PIs (40..46), bumping `piCount 40→47`. The deployed verifier
anchors `PI[39..46] = compute_authority_digest_8(post_cell)[0..7]` (step-6b, the 8-felt generalization of
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
faithful-8-felt extras (`extra0 .. extra0+6`, the pre-iroot limbs 38..=44 for perms / 45..=51 for vk,
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
    (envAt t row).loc (extra0 + i) ≡ (envAt t row).loc (prmCol (i + 1)) [ZMOD 2013265921] := by
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
    (hcanonAfter : 0 ≤ (envAt t row).loc (extra0 + i)
      ∧ (envAt t row).loc (extra0 + i) < 2013265921)
    (hcanonParam : 0 ≤ (envAt t row).loc (prmCol (i + 1))
      ∧ (envAt t row).loc (prmCol (i + 1)) < 2013265921)
    (hforged : (envAt t row).loc (extra0 + i) ≠ (envAt t row).loc (prmCol (i + 1))) :
    ¬ Satisfied2 hash (withPermsVK8Weld sel extra0 g) minit mfin maddrs t :=
  fun h => hforged (canon_eq_of_modEq hcanonAfter hcanonParam
    (withPermsVK8Weld_forces hash sel extra0 g h row hrow hnotlast hsel i hi))

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
(`afterPermsExtraCol … + i` = limb 38..=44, the faithful `permsHash[1..7]`) EQUALS its declared param
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
      ≡ (envAt t row).loc (prmCol (i + 1)) [ZMOD 2013265921] :=
  withPermsVK8Weld_forces hash _ _ _ h row hrow hnotlast hsel i hi

/-- **FORCE-LEMMA #2 (vk) — `setVKV3_forces8_extras`.** On an ACTIVE TRANSITION setVK row of a
`Satisfied2 hash setVKV3` witness, EACH of the 7 committed AFTER vk COMPLETION limbs
(`afterVKExtraCol … + i` = limb 45..=51, the faithful `vkHash[1..7]`) EQUALS its declared param
`prmCol (i + 1)` — the full 8-felt close for setVK. -/
theorem setVKV3_forces8_extras (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (h : Satisfied2 hash setVKV3 minit mfin maddrs t)
    (row : Nat) (hrow : row < t.rows.length) (hnotlast : row + 1 ≠ t.rows.length)
    (hsel : (envAt t row).loc EffectVmEmitSetVK.SEL_SET_VK = 1)
    (i : Nat) (hi : i < 7) :
    (envAt t row).loc (afterVKExtraCol EffectVmEmitSetVK.setVKVmDescriptor.traceWidth + i)
      ≡ (envAt t row).loc (prmCol (i + 1)) [ZMOD 2013265921] :=
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
  , root    := beforeFieldsRootGroup
  , key     := .const refusalAuditKeyFelt
  , value   := .var REFUSAL_AUDIT_FELT_COL
  , newRoot := afterFieldsRootGroup
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
#guard afterFieldsRootCol EFFECT_VM_WIDTH == EFFECT_VM_WIDTH + 263 + 36
-- BOTH POLARITIES of the write tooth's GUARD on the toy environment: the write fires under the refusal
-- selector (col 52 = 1) and is inert without it (the gate contributes nothing on a non-refusal pad row).
#guard (let env : VmRowEnv := ⟨fun c => if c == 52 then 1 else 0, fun _ => 0, fun _ => 0, fun _ => 0⟩;
        decide (refusalFieldsWriteOp.guard.eval env.loc = 1))    -- selector fires ⇒ write asserted
#guard (let env : VmRowEnv := ⟨fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0⟩;
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
    env.loc (afterDiscCol EffectVmEmitCellSeal.cellSealVmDescriptor.traceWidth) ≡ discSealed
      [ZMOD 2013265921] :=
  rotateV3WithDiscGate_forces_after _ _ _ hash _ env isFirst isLast hlast hsel h

/-- **TOOTH — `cellSealV3_rejects_frozen` (LIVE).** A cellSeal whose AFTER disc stays `Live(0)` (the
FROZEN seal — the headline lifecycle forgery) is UNSAT for a ledgerless client. -/
theorem cellSealV3_rejects_frozen (hash : List ℤ → ℤ) (env : VmRowEnv) (isFirst isLast : Bool)
    (hlast : isLast = false)
    (hsel : env.loc EffectVmEmitCellSeal.SEL_CELLSEAL = 1)
    (hfrozen : env.loc (afterDiscCol EffectVmEmitCellSeal.cellSealVmDescriptor.traceWidth) = discLive) :
    ¬ satisfiedVm hash (rotateV3WithDiscGate EffectVmEmitCellSeal.SEL_CELLSEAL (some discLive)
      discSealed EffectVmEmitCellSeal.cellSealVmDescriptor) env isFirst isLast := by
  refine rotateV3WithDiscGate_rejects_wrong_after _ _ _ hash _ env isFirst isLast hlast hsel ?_ ?_ ?_
  · rw [hfrozen]; decide
  · decide
  · rw [hfrozen]; decide

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
  refine rotateV3WithDiscGate_rejects_wrong_after _ _ _ hash _ env isFirst isLast hlast hsel ?_ ?_ ?_
  · rw [hres]; decide
  · decide
  · rw [hres]; decide

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
      ≡ env.loc declaredLifecyclePayloadCol [ZMOD 2013265921] :=
  rotateV3WithLifecyclePayloadGate_forces _ _ _ hash _ env isFirst isLast hlast hsel h

/-- **TOOTH — `cellSealV3_payload_rejects_forged_lightclient` (LIVE, LIGHT-CLIENT).** A cellSeal forged to
differ ONLY in the sealing PAYLOAD — a different `reason_hash` / `sealed_at`, so the committed AFTER
`lifecycle_felt` (limb 29) ≠ the in-circuit `payloadHash([disc, reason_hash, block_height])` — is UNSAT
through the deployed descriptor ALONE, NO off-cell anchor. This CONVERTS the §6 named residual: the forged
payload the record pin accepted (producer-free PI) is now REJECTED in-circuit. -/
theorem cellSealV3_payload_rejects_forged_lightclient (hash : List ℤ → ℤ) (env : VmRowEnv)
    (isFirst isLast : Bool) (hlast : isLast = false)
    (hsel : env.loc EffectVmEmitCellSeal.SEL_CELLSEAL = 1)
    (hcanonAfter : 0 ≤ env.loc (afterLifecycleCol EffectVmEmitCellSeal.cellSealVmDescriptor.traceWidth)
      ∧ env.loc (afterLifecycleCol EffectVmEmitCellSeal.cellSealVmDescriptor.traceWidth) < 2013265921)
    (hcanonPayload : 0 ≤ env.loc declaredLifecyclePayloadCol
      ∧ env.loc declaredLifecyclePayloadCol < 2013265921)
    (hforged : env.loc (afterLifecycleCol EffectVmEmitCellSeal.cellSealVmDescriptor.traceWidth)
      ≠ env.loc declaredLifecyclePayloadCol) :
    ¬ satisfiedVm hash (rotateV3WithLifecyclePayloadGate EffectVmEmitCellSeal.SEL_CELLSEAL
      (some discLive) discSealed EffectVmEmitCellSeal.cellSealVmDescriptor) env isFirst isLast :=
  rotateV3WithLifecyclePayloadGate_rejects_forged _ _ _ hash _ env isFirst isLast hlast hsel
    hcanonAfter hcanonPayload hforged

/-- **TOOTH — `cellDestroyV3_payload_rejects_forged_lightclient` (LIVE).** A cellDestroy forged to differ in
the death-certificate payload (`death_certificate_hash` / `destroyed_at`) folded into `lifecycle_felt` is
UNSAT ledgerless — the in-circuit payload weld bites. -/
theorem cellDestroyV3_payload_rejects_forged_lightclient (hash : List ℤ → ℤ) (env : VmRowEnv)
    (isFirst isLast : Bool) (hlast : isLast = false)
    (hsel : env.loc EffectVmEmitCellDestroy.SEL_CELLDESTROY = 1)
    (hcanonAfter : 0 ≤ env.loc (afterLifecycleCol EffectVmEmitCellDestroy.cellDestroyVmDescriptor.traceWidth)
      ∧ env.loc (afterLifecycleCol EffectVmEmitCellDestroy.cellDestroyVmDescriptor.traceWidth) < 2013265921)
    (hcanonPayload : 0 ≤ env.loc declaredLifecyclePayloadCol
      ∧ env.loc declaredLifecyclePayloadCol < 2013265921)
    (hforged : env.loc (afterLifecycleCol EffectVmEmitCellDestroy.cellDestroyVmDescriptor.traceWidth)
      ≠ env.loc declaredLifecyclePayloadCol) :
    ¬ satisfiedVm hash (rotateV3WithLifecyclePayloadGate EffectVmEmitCellDestroy.SEL_CELLDESTROY
      none discDestroyed EffectVmEmitCellDestroy.cellDestroyVmDescriptor) env isFirst isLast :=
  rotateV3WithLifecyclePayloadGate_rejects_forged _ _ _ hash _ env isFirst isLast hlast hsel
    hcanonAfter hcanonPayload hforged

/-- **TOOTH — `receiptArchiveV3_payload_rejects_forged_lightclient` (LIVE).** A receiptArchive forged to
differ in the archival checkpoint (`checkpoint_hash` / `archived_through`) folded into `lifecycle_felt` is
UNSAT ledgerless. -/
theorem receiptArchiveV3_payload_rejects_forged_lightclient (hash : List ℤ → ℤ) (env : VmRowEnv)
    (isFirst isLast : Bool) (hlast : isLast = false)
    (hsel : env.loc EffectVmEmitReceiptArchive.SEL_RECEIPT_ARCHIVE_RT = 1)
    (hcanonAfter : 0 ≤ env.loc
        (afterLifecycleCol EffectVmEmitReceiptArchive.receiptArchiveActorVmDescriptor.traceWidth)
      ∧ env.loc
        (afterLifecycleCol EffectVmEmitReceiptArchive.receiptArchiveActorVmDescriptor.traceWidth)
        < 2013265921)
    (hcanonPayload : 0 ≤ env.loc declaredLifecyclePayloadCol
      ∧ env.loc declaredLifecyclePayloadCol < 2013265921)
    (hforged : env.loc
      (afterLifecycleCol EffectVmEmitReceiptArchive.receiptArchiveActorVmDescriptor.traceWidth)
      ≠ env.loc declaredLifecyclePayloadCol) :
    ¬ satisfiedVm hash (rotateV3WithLifecyclePayloadGate EffectVmEmitReceiptArchive.SEL_RECEIPT_ARCHIVE_RT
      none discArchived EffectVmEmitReceiptArchive.receiptArchiveActorVmDescriptor) env isFirst isLast :=
  rotateV3WithLifecyclePayloadGate_rejects_forged _ _ _ hash _ env isFirst isLast hlast hsel
    hcanonAfter hcanonPayload hforged

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
      ≡ env.loc declaredParamCol [ZMOD 2013265921] :=
  rotateV3WithPermsVKGate_forces _ _ hash _ env isFirst isLast hlast hsel h

/-- **TOOTH — `setPermsV3_rejects_forged` (LIVE).** A setPermissions whose committed AFTER perms-digest
≠ the declared (PI-anchored) param — a forged post-permissions binding ARBITRARY permissions into
NEW_COMMIT — is UNSAT for a ledgerless client. The headline setPermissions authority forgery, closed
in-circuit with no trusted post-cell. -/
theorem setPermsV3_rejects_forged (hash : List ℤ → ℤ) (env : VmRowEnv) (isFirst isLast : Bool)
    (hlast : isLast = false)
    (hsel : env.loc EffectVmEmitSetPermissions.SEL_SET_PERMS = 1)
    (hcanonAfter : 0 ≤ env.loc (afterPermsCol EffectVmEmitSetPermissions.setPermsVmDescriptor.traceWidth)
      ∧ env.loc (afterPermsCol EffectVmEmitSetPermissions.setPermsVmDescriptor.traceWidth) < 2013265921)
    (hcanonParam : 0 ≤ env.loc declaredParamCol ∧ env.loc declaredParamCol < 2013265921)
    (hforged : env.loc (afterPermsCol EffectVmEmitSetPermissions.setPermsVmDescriptor.traceWidth)
      ≠ env.loc declaredParamCol) :
    ¬ satisfiedVm hash (rotateV3WithPermsVKGate EffectVmEmitSetPermissions.SEL_SET_PERMS
      (afterPermsCol EffectVmEmitSetPermissions.setPermsVmDescriptor.traceWidth)
      EffectVmEmitSetPermissions.setPermsVmDescriptor) env isFirst isLast :=
  rotateV3WithPermsVKGate_rejects_forged _ _ hash _ env isFirst isLast hlast hsel
    hcanonAfter hcanonParam hforged

/-- **TOOTH — `setVKV3_rejects_forged` (LIVE).** A setVK whose committed AFTER vk-digest ≠ the declared
(PI-anchored) param — a forged post-VK (the upgrade-safety forgery: binding an ARBITRARY verification
key into NEW_COMMIT) — is UNSAT for a ledgerless client, no trusted post-cell. -/
theorem setVKV3_rejects_forged (hash : List ℤ → ℤ) (env : VmRowEnv) (isFirst isLast : Bool)
    (hlast : isLast = false)
    (hsel : env.loc EffectVmEmitSetVK.SEL_SET_VK = 1)
    (hcanonAfter : 0 ≤ env.loc (afterVKCol EffectVmEmitSetVK.setVKVmDescriptor.traceWidth)
      ∧ env.loc (afterVKCol EffectVmEmitSetVK.setVKVmDescriptor.traceWidth) < 2013265921)
    (hcanonParam : 0 ≤ env.loc declaredParamCol ∧ env.loc declaredParamCol < 2013265921)
    (hforged : env.loc (afterVKCol EffectVmEmitSetVK.setVKVmDescriptor.traceWidth)
      ≠ env.loc declaredParamCol) :
    ¬ satisfiedVm hash (rotateV3WithPermsVKGate EffectVmEmitSetVK.SEL_SET_VK
      (afterVKCol EffectVmEmitSetVK.setVKVmDescriptor.traceWidth)
      EffectVmEmitSetVK.setVKVmDescriptor) env isFirst isLast :=
  rotateV3WithPermsVKGate_rejects_forged _ _ hash _ env isFirst isLast hlast hsel
    hcanonAfter hcanonParam hforged

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
      ≡ modeSovereign [ZMOD 2013265921] :=
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
  refine rotateV3WithModeGate_rejects_unpromoted _ _ hash _ env isFirst isLast hlast hsel ?_ ?_ ?_
  · rw [hunpromoted]; decide
  · decide
  · rw [hunpromoted]; decide

/-- **TOOTH — `setFieldDynV3_rejects_forged` (LIVE).** A dynamic setField whose committed AFTER
`fields_root` sub-limb ≠ the declared post-`fields_root` param — a forged post-`fields_root` (the
dynamic write committed to an arbitrary overflow map) — is UNSAT for a ledgerless client. -/
theorem setFieldDynV3_rejects_forged (hash : List ℤ → ℤ) (env : VmRowEnv) (isFirst isLast : Bool)
    (hlast : isLast = false)
    (hsel : env.loc EffectVmEmitSetField.SEL_SET_FIELD = 1)
    (hcanonAfter : 0 ≤ env.loc (afterFieldsRootCol setFieldDynV1Face.traceWidth)
      ∧ env.loc (afterFieldsRootCol setFieldDynV1Face.traceWidth) < 2013265921)
    (hcanonParam : 0 ≤ env.loc declaredFieldsRootCol ∧ env.loc declaredFieldsRootCol < 2013265921)
    (hforged : env.loc (afterFieldsRootCol setFieldDynV1Face.traceWidth)
      ≠ env.loc declaredFieldsRootCol) :
    ¬ satisfiedVm hash (rotateV3WithFieldsRootGate EffectVmEmitSetField.SEL_SET_FIELD
      (afterFieldsRootCol setFieldDynV1Face.traceWidth) setFieldDynV1Face) env isFirst isLast :=
  rotateV3WithFieldsRootGate_rejects_forged _ _ hash _ env isFirst isLast hlast hsel
    hcanonAfter hcanonParam hforged

#assert_axioms makeSovereignV3_forces_sovereign
#assert_axioms makeSovereignV3_rejects_unpromoted
#assert_axioms setFieldDynV3_rejects_forged

-- The mode / fields-root force-cols land at AFTER limb 35 / 36 (= traceWidth + B_SPAN + 35 / +36).
#guard afterModeCol EFFECT_VM_WIDTH == EFFECT_VM_WIDTH + 263 + 35
#guard afterFieldsRootCol EFFECT_VM_WIDTH == EFFECT_VM_WIDTH + 263 + 36
#guard beforeModeCol EFFECT_VM_WIDTH == EFFECT_VM_WIDTH + 35
#guard declaredFieldsRootCol == prmCol 0
#guard decide (modeHosted ≠ modeSovereign)

-- The perms/vk force-cols land at AFTER limb 33 / 34 (= traceWidth + B_SPAN + 33 / +34).
#guard afterPermsCol EFFECT_VM_WIDTH == EFFECT_VM_WIDTH + 263 + 33
#guard afterVKCol EFFECT_VM_WIDTH == EFFECT_VM_WIDTH + 263 + 34
#guard declaredParamCol == prmCol 0

-- The disc discriminants are pairwise distinct (the gate distinguishes lifecycle states).
#guard decide (discLive ≠ discSealed)
#guard decide (discSealed ≠ discDestroyed)
#guard decide (discDestroyed ≠ discArchived)
#guard decide (discLive ≠ discArchived)
-- The disc force-cols land at AFTER limb 32 (= traceWidth + B_SPAN + 32) and BEFORE limb 32.
#guard afterDiscCol EFFECT_VM_WIDTH == EFFECT_VM_WIDTH + 263 + 32
#guard beforeDiscCol EFFECT_VM_WIDTH == EFFECT_VM_WIDTH + 32

#assert_axioms graduable_rotateV3WithRecordPin
#assert_axioms rotateV3WithRecordPin_pins
#assert_axioms rotateV3WithRecordPin_rejects_wrong_post
#assert_axioms rotateV3WithRecordPin_satisfiedVm_v1

-- The record pin lands at PI slot 46 (one past the four rotated commit pins 34..37); each forced
-- descriptor publishes 39 PIs, and graduation survives the appended pin.
#guard (rotateV3 EffectVmEmitCellSeal.cellSealVmDescriptor).piCount == 39
#guard cellSealV3.piCount == 40
#guard cellUnsealV3.piCount == 40
#guard cellDestroyV3.piCount == 40
#guard setPermsV3.piCount == 47
#guard setVKV3.piCount == 47
#guard refusalV3.piCount == 40
#guard receiptArchiveV3.piCount == 40
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
-- tw+47+29; with tw = 186 that is col 262; the record-pin PI carries the recomputed post felt). A row
-- whose AFTER limb equals that PI PASSES the pin; a frozen / wrong one FAILS it (the forgery is
-- rejected). The PI index is `pi.V1_PI_COUNT + 4` (the first slot past the four rotated commit pins),
-- written symbolically so the 2026-08-07 seven-slot compaction cascaded instead of silently pointing
-- both poles at an all-zero slot.
#guard (let off := B_LIFECYCLE; let tw := (186 : Nat); let recPi := pi.V1_PI_COUNT + 4;
        let env : VmRowEnv := ⟨fun c => if c == tw + B_SPAN + off then 1 else 0, fun _ => 0,
                               fun k => if k == recPi then 1 else 0, fun _ => 0⟩;
        decide (env.loc (tw + B_SPAN + off) = env.pub recPi))   -- sealed (1) == the pin ⇒ pin holds
#guard (let off := B_LIFECYCLE; let tw := (186 : Nat); let recPi := pi.V1_PI_COUNT + 4;
        let env : VmRowEnv := ⟨fun c => if c == tw + B_SPAN + off then 0 else 0, fun _ => 0,
                               fun k => if k == recPi then 1 else 0, fun _ => 0⟩;
        decide (env.loc (tw + B_SPAN + off) ≠ env.pub recPi))   -- frozen-Live (0) ≠ sealed ⇒ REJECTS

/-! ## §v12 — THE DIRECT CARRIER-OCTET PI PINS (factory `child_vk` · hatchery `contract_hash`).

The RESOLVED-FORK direct-pin lane (NOT the `CarrierOctetGates` eqGate wrap): the v12 carrier octets
are already COMMITTED columns (STEP-2 producer fill, `rotation_witness.rs::produce` /
`commitment.rs::compute_rotated_pre_limbs`), so pinning the AFTER-block octet directly to TAIL PIs
PUBLISHES it — SAT-by-construction (a forged post-state that changed the octet mismatches the
committed `state_commit`). Structurally identical to `withRecordPin8Headroom2` (the AFTER-block
authority-limb pins), so the apex consumes the `rotV3_publishes`-shape forcing below. -/

/-- In-block base of the v12 `child_vk` carrier octet (limbs 89..=96 — REVOKED-ROOT +1: the
fields completion lanes 113..168 ride PAST it, so it no longer tracks `B_IROOT`). Rust
twin `trace_rotated::B_CHILD_VK_OCTET`. The hatchery-INVARIANT carrier rides this octet
(`invariant_digest === child_vk`), so it consumes the SAME pins. -/
def B_CHILD_VK_OCTET : Nat := 89
/-- In-block base of the v12 `contract_hash` carrier octet (limbs 97..=104, REVOKED-ROOT +1). Rust
twin `trace_rotated::B_CONTRACT_HASH_OCTET`. -/
def B_CONTRACT_HASH_OCTET : Nat := 97
/-- In-block base of the committed `public_key` carrier octet (limbs 105..=112, REVOKED-ROOT +1 —
was 104). The one octet non-zero on a generic turn (the operated cell's owner key), so it moves every
turn's `state_commit`. Rust twin `trace_rotated::B_PUBKEY_OCTET`; the app-root octet list is
`[B_CHILD_VK_OCTET, B_CONTRACT_HASH_OCTET, B_PUBKEY_OCTET] = [89, 97, 105]`. -/
def B_PUBKEY_OCTET : Nat := 105

/-! ### ⚑ THE CARRIER-OCTET NINTH LANES (KEY-NONET FLAG DAY 2026-08-01)

Each carrier octet holds 32 bytes. Eight BabyBear lanes carry `8 · log₂ p = 247.26` bits against
256, so NO eight-lane packing of 32 bytes is injective — and the deployed one is not injective
*trivially*, dropping bits 6-7 of every fourth byte (`Dregg2.Circuit.KeyLanes9`, which exhibits two
distinct keys with an identical fully-canonical octet, and notes that bit 7 of byte 31 is Ed25519's
SIGN bit, so a key and its negation collide and the negation is a keypair the attacker holds).

`KeyLanes9.keyToLanes9` is the base-`2^29` NONET that repairs it; these are its ninth-lane columns.
They are PROJECTED from the verified layout, never re-typed: `RotatedLayout.octetLaneCol o 8`. -/

/-- `child_vk`'s ninth lane (in-block limb 184). -/
def B_CHILD_VK_NINTH_LANE : Nat := (rotated196.octetLaneCol 0 8).getD 0
/-- `contract_hash`'s ninth lane (in-block limb 185). -/
def B_CONTRACT_HASH_NINTH_LANE : Nat := (rotated196.octetLaneCol 1 8).getD 0
/-- ⚑ **THE OWNER KEY's ninth lane** (in-block limb 186) — the column
`Emit.KeyCanonicity9Emit.deployedKeyCanon9Cols` puts lane 8 of the nonet on. Rust twin
`trace_rotated::B_PUBKEY_NINTH_LANE`, generated by `EmitLayoutManifest`. -/
def B_PUBKEY_NINTH_LANE : Nat := (rotated196.octetLaneCol 2 8).getD 0

-- Re-typed by hand against the committed layout: the literals ARE the review (`trace_rotated.rs`'s
-- own doctrine, paid for when nine pins were "re-expressed" as `x == x` at the 178 → 184 flag day).
#guard B_CHILD_VK_NINTH_LANE == 184
#guard B_CONTRACT_HASH_NINTH_LANE == 185
#guard B_PUBKEY_NINTH_LANE == 186
-- ⚑ AND EACH IS AN ABSORBED PRE-LIMB. This is the whole reason the extent had to grow: an appendix
-- column is not in `preLimbsAt`, so `wireCommitR` never folds it and `state_commit` would still bind
-- only the eight lanes — 232 bits of a 256-bit key. `KeyCanonicity9Emit.lane8_is_absorbed_iff` is
-- the same fact as a theorem rather than a guard.
#guard B_CHILD_VK_NINTH_LANE < rotatedNumPreLimbs
#guard B_CONTRACT_HASH_NINTH_LANE < rotatedNumPreLimbs
#guard B_PUBKEY_NINTH_LANE < rotatedNumPreLimbs
-- ...and none of them aliases an octet lane or any other committed limb (the layout's `disjoint`
-- obligation already forces this; checked here at the emit's own names).
#guard [B_CHILD_VK_OCTET, B_CONTRACT_HASH_OCTET, B_PUBKEY_OCTET].all
  (fun b => (List.range 8).all fun k =>
    [B_CHILD_VK_NINTH_LANE, B_CONTRACT_HASH_NINTH_LANE, B_PUBKEY_NINTH_LANE].all
      (fun n => n != b + k))

/-- **THE APP-ROOT WELD FIELD OCTET in-block base.** The AFTER rotated block's directly-committed
`fields[0..8]` lane-0 octet: field register `r(state.FIELD_BASE + i)` rides in-block offset
`CUSTOM_APP_FIELD_ROT_BASE + i`, per `weldsAt` (`colEq (base + 4) (stateBase + state.FIELD_BASE)`,
… `colEq (base + 11) (stateBase + state.FIELD_BASE + 7)`). So a consumer derives an octet index from
a state register slot by `octet_index_of_register r = r - state.FIELD_BASE`. Rust twin
`trace_rotated::CUSTOM_APP_FIELD_ROT_BASE`. -/
def CUSTOM_APP_FIELD_ROT_BASE : Nat := 4
/-- Width of the app-root field octet (8 field lane-0 limbs). Rust twin
`trace_rotated::CUSTOM_APP_FIELD_OCTET_LEN`. -/
def CUSTOM_APP_FIELD_OCTET_LEN : Nat := 8

#guard B_CHILD_VK_OCTET == 89
#guard B_CONTRACT_HASH_OCTET == 97
#guard B_PUBKEY_OCTET == 105
#guard CUSTOM_APP_FIELD_OCTET_LEN == 8
-- The app-root octet in-block base IS the block offset `weldsAt` aligns with the state field base:
-- `weldsAt base stateBase` maps `base + CUSTOM_APP_FIELD_ROT_BASE + i ↔ stateBase + state.FIELD_BASE + i`
-- for every field lane `i < 8` (see `weldsAt` above, `colEq (base + 4) (stateBase + state.FIELD_BASE)`).
#guard CUSTOM_APP_FIELD_ROT_BASE == 4
-- The octet spans in-block offsets `CUSTOM_APP_FIELD_ROT_BASE .. +7` = `4..11`, exactly the range
-- `weldsAt` maps to `stateBase + state.FIELD_BASE .. +7` (its `colEq (base+4) … (base+11)` field welds).
#guard CUSTOM_APP_FIELD_ROT_BASE + CUSTOM_APP_FIELD_OCTET_LEN - 1 == 11

/-- **`withAfterOctetPins g octetBase`** — APPEND 8 `.piBinding .last` pins publishing the AFTER-block
committed carrier octet (`EFFECT_VM_WIDTH + AFTER_BLOCK_OFF + octetBase + k`, `k < 8`) as 8 TAIL PIs
(`g.piCount + k`), bumping `piCount` by 8. Mirrors `withRecordPin8Headroom2` exactly — additive, no
site / range / mem-op / map-op touched, so every existing forcing keystone lifts by
`List.mem_append_left` (the peel below). -/
def withAfterOctetPins (g : EffectVmDescriptor2) (octetBase : Nat) : EffectVmDescriptor2 :=
  { g with
    piCount := g.piCount + 8
    constraints := g.constraints ++ (List.range 8).map (fun k =>
      VmConstraint2.base (.piBinding .last (EFFECT_VM_WIDTH + AFTER_BLOCK_OFF + (octetBase + k))
        (g.piCount + k))) }

/-- The 8 octet pins are the ONLY constraints past the inner descriptor's (single `++`). -/
theorem withAfterOctetPins_constraints (g : EffectVmDescriptor2) (octetBase : Nat) :
    (withAfterOctetPins g octetBase).constraints
      = g.constraints ++ (List.range 8).map (fun k =>
          VmConstraint2.base (.piBinding .last (EFFECT_VM_WIDTH + AFTER_BLOCK_OFF + (octetBase + k))
            (g.piCount + k))) := rfl

/-- The octet pins are `.piBinding`s, so they contribute NO mem-op (the mem log is unchanged). -/
theorem memOpsOf_withAfterOctetPins (g : EffectVmDescriptor2) (octetBase : Nat) :
    memOpsOf (withAfterOctetPins g octetBase) = memOpsOf g := by
  simp [memOpsOf, withAfterOctetPins, List.filterMap_append, List.filterMap_map]

/-- The octet pins contribute NO map-op (the map log is unchanged). -/
theorem mapOpsOf_withAfterOctetPins (g : EffectVmDescriptor2) (octetBase : Nat) :
    mapOpsOf (withAfterOctetPins g octetBase) = mapOpsOf g := by
  simp [mapOpsOf, withAfterOctetPins, List.filterMap_append, List.filterMap_map]

/-- **THE PEEL** — `Satisfied2 (withAfterOctetPins g octetBase) ⟹ Satisfied2 g`. The wrap only APPENDS
`.piBinding` constraints (and bumps `piCount`): the inner constraints stay members
(`List.mem_append_left`), sites / ranges / mem / map logs are unchanged, so every existing per-effect
soundness lemma lifts to the wrapped descriptor by peeling the wrap first. Mirrors
`satisfied2_of_withRecordPin8Headroom2`. -/
theorem satisfied2_of_withAfterOctetPins (hash : List ℤ → ℤ) (g : EffectVmDescriptor2) (octetBase : Nat)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (h : Satisfied2 hash (withAfterOctetPins g octetBase) minit mfin maddrs t) :
    Satisfied2 hash g minit mfin maddrs t := by
  have hmem : memLog (withAfterOctetPins g octetBase) t = memLog g t := by
    simp [memLog, memOpsOf_withAfterOctetPins]
  have hmap : mapLog (withAfterOctetPins g octetBase) t = mapLog g t := by
    simp [mapLog, mapOpsOf_withAfterOctetPins]
  exact
    { rowConstraints := fun i hi c hc => h.rowConstraints i hi c (by
        rw [withAfterOctetPins_constraints]; exact List.mem_append_left _ hc)
    , rowHashes := h.rowHashes
    , rowRanges := h.rowRanges
    , memAddrsNodup := h.memAddrsNodup
    , memClosed := fun op hop => h.memClosed op (by rw [hmem]; exact hop)
    , memDisciplined := by rw [← hmem]; exact h.memDisciplined
    , memBalanced := by rw [← hmem]; exact h.memBalanced
    , memTableFaithful := by rw [← hmem]; exact h.memTableFaithful
    , mapTableFaithful := by rw [← hmap]; exact h.mapTableFaithful }

/-- **`withAfterOctetPins_publishes` — THE `rotV3_publishes`-shape forcing.** On any LAST row of a
`Satisfied2` witness, each of the 8 published TAIL PIs (`g.piCount + k`) EQUALS its committed
AFTER-block octet column — so the apex reads the committed carrier octet off the PI vector, and a
forged post-state octet (a laundered `child_vk` / `contract_hash`) is UNSAT (it would break both the
pin and the committed `state_commit`). -/
theorem withAfterOctetPins_publishes (hash : List ℤ → ℤ) (g : EffectVmDescriptor2) (octetBase : Nat)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hsat : Satisfied2 hash (withAfterOctetPins g octetBase) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hlast : i + 1 = t.rows.length) :
    ∀ k : Fin 8, (envAt t i).loc (EFFECT_VM_WIDTH + AFTER_BLOCK_OFF + (octetBase + k.val))
      ≡ (envAt t i).pub (g.piCount + k.val) [ZMOD 2013265921] := by
  intro k
  have hlastt : (i + 1 == t.rows.length) = true := by simp [hlast]
  have hin : VmConstraint2.base
      (.piBinding .last (EFFECT_VM_WIDTH + AFTER_BLOCK_OFF + (octetBase + k.val)) (g.piCount + k.val))
      ∈ (withAfterOctetPins g octetBase).constraints := by
    rw [withAfterOctetPins_constraints]
    exact List.mem_append_right _ (List.mem_map.mpr ⟨k.val, List.mem_range.mpr k.isLt, rfl⟩)
  have h := hsat.rowConstraints i hi _ hin
  simp only [VmConstraint2.holdsAt, hlastt, holdsVm_piLast_true] at h
  exact h

#assert_axioms satisfied2_of_withAfterOctetPins
#assert_axioms withAfterOctetPins_publishes

/-! ### §FIELDS-ROOT-PI — publish the native post-state fields-map root for custom folds.

`withAfterOctetPins` can only publish a contiguous block of rotated columns.  The faithful
`fields_root` group is deliberately non-contiguous (`36, 66, 67, 19..23` within the AFTER block),
so using the octet helper here would publish the wrong statement.  This wrapper names the real
`fieldsRootGroupCol` projection lane-by-lane.  The Custom direct-IR2 fold uses these eight PIs to
connect an application's authenticated map-opening root to the exact post-state root already
absorbed by the wide state commitment.
-/

/-- Append eight LAST-row PI pins for the faithful AFTER `fields_root` digest. -/
def withAfterFieldsRootPins (g : EffectVmDescriptor2) : EffectVmDescriptor2 :=
  { g with
    piCount := g.piCount + 8
    constraints := g.constraints ++ (List.finRange 8).map (fun i =>
      VmConstraint2.base (.piBinding .last
        (fieldsRootGroupCol (EFFECT_VM_WIDTH + AFTER_BLOCK_OFF) i)
        (g.piCount + i.val))) }

theorem withAfterFieldsRootPins_constraints (g : EffectVmDescriptor2) :
    (withAfterFieldsRootPins g).constraints
      = g.constraints ++ (List.finRange 8).map (fun i =>
          VmConstraint2.base (.piBinding .last
            (fieldsRootGroupCol (EFFECT_VM_WIDTH + AFTER_BLOCK_OFF) i)
            (g.piCount + i.val))) := rfl

/-- The fields-root pins are observational: they do not add memory operations. -/
theorem memOpsOf_withAfterFieldsRootPins (g : EffectVmDescriptor2) :
    memOpsOf (withAfterFieldsRootPins g) = memOpsOf g := by
  simp [memOpsOf, withAfterFieldsRootPins, List.filterMap_append, List.filterMap_map]

/-- The fields-root pins are observational: they do not add map operations. -/
theorem mapOpsOf_withAfterFieldsRootPins (g : EffectVmDescriptor2) :
    mapOpsOf (withAfterFieldsRootPins g) = mapOpsOf g := by
  simp [mapOpsOf, withAfterFieldsRootPins, List.filterMap_append, List.filterMap_map]

/-- Peeling the additive fields-root publication recovers the authored inner relation. -/
theorem satisfied2_of_withAfterFieldsRootPins (hash : List ℤ → ℤ) (g : EffectVmDescriptor2)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (h : Satisfied2 hash (withAfterFieldsRootPins g) minit mfin maddrs t) :
    Satisfied2 hash g minit mfin maddrs t := by
  have hmem : memLog (withAfterFieldsRootPins g) t = memLog g t := by
    simp [memLog, memOpsOf_withAfterFieldsRootPins]
  have hmap : mapLog (withAfterFieldsRootPins g) t = mapLog g t := by
    simp [mapLog, mapOpsOf_withAfterFieldsRootPins]
  exact
    { rowConstraints := fun i hi c hc => h.rowConstraints i hi c (by
        rw [withAfterFieldsRootPins_constraints]; exact List.mem_append_left _ hc)
    , rowHashes := h.rowHashes
    , rowRanges := h.rowRanges
    , memAddrsNodup := h.memAddrsNodup
    , memClosed := fun op hop => h.memClosed op (by rw [hmem]; exact hop)
    , memDisciplined := by rw [← hmem]; exact h.memDisciplined
    , memBalanced := by rw [← hmem]; exact h.memBalanced
    , memTableFaithful := by rw [← hmem]; exact h.memTableFaithful
    , mapTableFaithful := by rw [← hmap]; exact h.mapTableFaithful }

/-- Any satisfying wrapped trace publishes every lane of the exact post-state fields root. -/
theorem withAfterFieldsRootPins_publishes (hash : List ℤ → ℤ) (g : EffectVmDescriptor2)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hsat : Satisfied2 hash (withAfterFieldsRootPins g) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hlast : i + 1 = t.rows.length) :
    ∀ k : Fin 8,
      (envAt t i).loc (fieldsRootGroupCol (EFFECT_VM_WIDTH + AFTER_BLOCK_OFF) k)
        ≡ (envAt t i).pub (g.piCount + k.val) [ZMOD 2013265921] := by
  intro k
  have hlastt : (i + 1 == t.rows.length) = true := by simp [hlast]
  have hin : VmConstraint2.base
      (.piBinding .last (fieldsRootGroupCol (EFFECT_VM_WIDTH + AFTER_BLOCK_OFF) k)
        (g.piCount + k.val)) ∈ (withAfterFieldsRootPins g).constraints := by
    rw [withAfterFieldsRootPins_constraints]
    exact List.mem_append_right _
      (List.mem_map.mpr ⟨k, List.mem_finRange k, rfl⟩)
  have h := hsat.rowConstraints i hi _ hin
  simp only [VmConstraint2.holdsAt, hlastt, holdsVm_piLast_true] at h
  exact h

#assert_axioms satisfied2_of_withAfterFieldsRootPins
#assert_axioms withAfterFieldsRootPins_publishes

/-! ### §VALUE8 — THE setField WRITTEN-SLOT COMPLETION-LANE PINS (`withSetFieldCompletionPins`).

The deployed setField members ride `v3OfFrozen (setFieldTickFace slot)` (freeze-ALL): every one of the
64 fields completion lanes is frozen BEFORE↔AFTER, so an honest LARGE-value write (`FieldElement =
[u8;32]` with nonzero high bytes) is REJECTED — the R1 completeness seam
(`setfield_completion_lane_forge::honest_large_value_setfield_fails_the_deployed_freeze`), and the
written slot's high 224 bits are left UNBOUND by the light-client view (the ORPHAN-SWEEP §5.2 residual;
`keystone_descriptor_deployment_gate.rs:62/69`, reason "deploy: VALUE8 setField weld").

The FIX — freeze-EXCEPT + VALUE9. `setFieldV3 slot = v3OfFrozenSetField slot (setFieldTickFace slot)`
freezes the OTHER seven slots (56 lanes) but FREES the written slot's 8 completion lanes
(`fieldsSlotLanes slot` — `113 + 7·slot .. +6` PLUS the ninth lane `176 + slot`), so an honest large
write is no longer over-frozen. `withSetFieldCompletionPins` then PUBLISHES those exact eight freed
lanes (`EFFECT_VM_WIDTH + AFTER_BLOCK_OFF + fieldLaneCol slot k.succ`, `k : Fin 8`) as eight TAIL PIs
— binding them to the declared lane vector the executor derives, so (a) the high 224 bits are no
longer an unconstrained free felt (a forge that moves them off the published value is UNSAT — the
`_rejects_forged_pi` tooth), and (b) a slot-i proof publishes slot-i's completion value at these PIs,
so it verifies UNIQUELY under descriptor-i (a slot-j descriptor pins slot-j's frozen completion lanes
to the SAME PI slots, which the slot-i trace violates). Structurally identical to
`withAfterOctetPins` (8-lane variant) — additive, no site / range / mem-op / map-op touched, so every
existing setField forcing keystone lifts by `List.mem_append_left` (the peel below).

⚑ **What the ninth pin buys, and what it does NOT.** With eight lanes the published vector could not
determine the field — `fieldToLanes8` cannot be injective at 247.26 bits against 256 (pigeonhole), so
two distinct 32-byte values shared a legal PI vector and the light client could not tell them apart.
With `Dregg2.Circuit.FieldLanes9.fieldToLanes9_injective`, the lane vector DOES determine the value.
That is a fact about the Lean encoder; this file pins the COLUMNS the deployed producer must fill,
and `circuit/tests/field_lanes9_injective.rs` is what ties the deployed Rust to it. No theorem here
derives the Rust encoder — the capstones still take `hval` as a hypothesis.

⚑ THIS IS THE DEPLOYED SHAPE, NOT A STAGING SET. `v3RegistryBare`'s setField members ARE
`withSetFieldCompletionPins slot (withSelectorGate SEL_SET_FIELD (setFieldV3 slot))`, so the 1-felt
registry, both wide registries and the umem weld all carry it. The parallel
`v3RegistrySetFieldValue8` staging registry that once sat beside the live wire is DELETED. -/

/-- **`withSetFieldCompletionPins slot g`** — APPEND 8 `.piBinding .last` pins publishing the written
slot's freed AFTER-block completion lanes (`EFFECT_VM_WIDTH + AFTER_BLOCK_OFF + fieldLaneCol slot
k.succ`, `k : Fin 8`) as 8 TAIL PIs (`g.piCount + k`), bumping `piCount` by 8. The nonet mirror of
`withAfterOctetPins`.

⚑ **FLAG DAY 2026-07-31 (7 pins → 8).** The lane columns come from `fieldLaneCol`, the verified
layout's projection — the eighth pin publishes the NINTH lane at `176 + slot`, which is NOT
`setFieldCompletionBase slot + 7`. The old `setFieldCompletionBase` (`113 + 7·slot`) is DELETED
rather than kept beside the projection: an arithmetic base cannot name a non-contiguous window, and
a second shape that agrees on seven of eight lanes is exactly the pair that disagrees later. -/
def withSetFieldCompletionPins (slot : Fin 8) (g : EffectVmDescriptor2) : EffectVmDescriptor2 :=
  { g with
    piCount := g.piCount + 8
    constraints := g.constraints ++ (List.finRange 8).map (fun k =>
      VmConstraint2.base (.piBinding .last
        (EFFECT_VM_WIDTH + AFTER_BLOCK_OFF + fieldLaneCol slot k.succ) (g.piCount + k.val))) }

/-- The 8 completion pins are the ONLY constraints past the inner descriptor's (single `++`). -/
theorem withSetFieldCompletionPins_constraints (slot : Fin 8) (g : EffectVmDescriptor2) :
    (withSetFieldCompletionPins slot g).constraints
      = g.constraints ++ (List.finRange 8).map (fun k =>
          VmConstraint2.base (.piBinding .last
            (EFFECT_VM_WIDTH + AFTER_BLOCK_OFF + fieldLaneCol slot k.succ) (g.piCount + k.val))) := rfl

/-- The completion pins are `.piBinding`s, so they contribute NO mem-op (the mem log is unchanged). -/
theorem memOpsOf_withSetFieldCompletionPins (slot : Fin 8) (g : EffectVmDescriptor2) :
    memOpsOf (withSetFieldCompletionPins slot g) = memOpsOf g := by
  simp [memOpsOf, withSetFieldCompletionPins, List.filterMap_append, List.filterMap_map]

/-- The completion pins contribute NO map-op (the map log is unchanged). -/
theorem mapOpsOf_withSetFieldCompletionPins (slot : Fin 8) (g : EffectVmDescriptor2) :
    mapOpsOf (withSetFieldCompletionPins slot g) = mapOpsOf g := by
  simp [mapOpsOf, withSetFieldCompletionPins, List.filterMap_append, List.filterMap_map]

/-- **THE PEEL** — `Satisfied2 (withSetFieldCompletionPins slot g) ⟹ Satisfied2 g`. The wrap only
APPENDS `.piBinding` constraints (and bumps `piCount`): the inner constraints stay members
(`List.mem_append_left`), sites / ranges / mem / map logs are unchanged, so every existing setField
soundness lemma lifts to the wrapped descriptor by peeling the wrap first. Mirrors
`satisfied2_of_withAfterOctetPins`. -/
theorem satisfied2_of_withSetFieldCompletionPins (hash : List ℤ → ℤ) (slot : Fin 8)
    (g : EffectVmDescriptor2)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (h : Satisfied2 hash (withSetFieldCompletionPins slot g) minit mfin maddrs t) :
    Satisfied2 hash g minit mfin maddrs t := by
  have hmem : memLog (withSetFieldCompletionPins slot g) t = memLog g t := by
    simp [memLog, memOpsOf_withSetFieldCompletionPins]
  have hmap : mapLog (withSetFieldCompletionPins slot g) t = mapLog g t := by
    simp [mapLog, mapOpsOf_withSetFieldCompletionPins]
  exact
    { rowConstraints := fun i hi c hc => h.rowConstraints i hi c (by
        rw [withSetFieldCompletionPins_constraints]; exact List.mem_append_left _ hc)
    , rowHashes := h.rowHashes
    , rowRanges := h.rowRanges
    , memAddrsNodup := h.memAddrsNodup
    , memClosed := fun op hop => h.memClosed op (by rw [hmem]; exact hop)
    , memDisciplined := by rw [← hmem]; exact h.memDisciplined
    , memBalanced := by rw [← hmem]; exact h.memBalanced
    , memTableFaithful := by rw [← hmem]; exact h.memTableFaithful
    , mapTableFaithful := by rw [← hmap]; exact h.mapTableFaithful }

/-- **`withSetFieldCompletionPins_publishes`.** On any LAST row of a `Satisfied2` witness, each of the 8
published TAIL PIs (`g.piCount + k`) EQUALS its committed AFTER-block completion lane — so the light
client reads the written slot's high 224 bits off the PI vector, and a forged completion lane (a
laundered high-byte field) is UNSAT (it would break both the pin and the committed `state_commit`).
⚑ `k : Fin 8` now, and lane `8` is the flag-day NINTH column `176 + slot`. -/
theorem withSetFieldCompletionPins_publishes (hash : List ℤ → ℤ) (slot : Fin 8)
    (g : EffectVmDescriptor2)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hsat : Satisfied2 hash (withSetFieldCompletionPins slot g) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hlast : i + 1 = t.rows.length) :
    ∀ k : Fin 8, (envAt t i).loc (EFFECT_VM_WIDTH + AFTER_BLOCK_OFF + fieldLaneCol slot k.succ)
      ≡ (envAt t i).pub (g.piCount + k.val) [ZMOD 2013265921] := by
  intro k
  have hlastt : (i + 1 == t.rows.length) = true := by simp [hlast]
  have hin : VmConstraint2.base
      (.piBinding .last (EFFECT_VM_WIDTH + AFTER_BLOCK_OFF + fieldLaneCol slot k.succ)
        (g.piCount + k.val)) ∈ (withSetFieldCompletionPins slot g).constraints := by
    rw [withSetFieldCompletionPins_constraints]
    exact List.mem_append_right _ (List.mem_map.mpr ⟨k, List.mem_finRange k, rfl⟩)
  have h := hsat.rowConstraints i hi _ hin
  simp only [VmConstraint2.holdsAt, hlastt, holdsVm_piLast_true] at h
  exact h

/-- **TOOTH (completion-lane forge ⇒ UNSAT)** — a written-slot completion lane that DIFFERS from its
published PI (a forged high-byte value smuggled into NEW_COMMIT) does NOT satisfy the wrap. The
light-client bite for the setField VALUE8 half: `verify_vm_descriptor2` alone rejects it. -/
theorem withSetFieldCompletionPins_rejects_forged_pi (hash : List ℤ → ℤ) (slot : Fin 8)
    (g : EffectVmDescriptor2) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (i : Nat) (hi : i < t.rows.length) (hlast : i + 1 = t.rows.length) (k : Fin 8)
    (hcanonLoc : 0 ≤ (envAt t i).loc (EFFECT_VM_WIDTH + AFTER_BLOCK_OFF + fieldLaneCol slot k.succ)
      ∧ (envAt t i).loc (EFFECT_VM_WIDTH + AFTER_BLOCK_OFF + fieldLaneCol slot k.succ) < 2013265921)
    (hcanonPI : 0 ≤ (envAt t i).pub (g.piCount + k.val)
      ∧ (envAt t i).pub (g.piCount + k.val) < 2013265921)
    (hforged : (envAt t i).loc (EFFECT_VM_WIDTH + AFTER_BLOCK_OFF + fieldLaneCol slot k.succ)
      ≠ (envAt t i).pub (g.piCount + k.val)) :
    ¬ Satisfied2 hash (withSetFieldCompletionPins slot g) minit mfin maddrs t :=
  fun hsat => hforged (canon_eq_of_modEq hcanonLoc hcanonPI
    (withSetFieldCompletionPins_publishes hash slot g minit mfin maddrs t hsat i hi hlast k))

#assert_axioms satisfied2_of_withSetFieldCompletionPins
#assert_axioms withSetFieldCompletionPins_publishes
#assert_axioms withSetFieldCompletionPins_rejects_forged_pi

-- ⚑ `setFieldValue8V3` is DELETED. It was the freeze-EXCEPT setField + the completion pins WITHOUT
-- the selector gate — a near-twin of what `v3RegistryBare` now actually deploys
-- (`withSetFieldCompletionPins slot (withSelectorGate SEL_SET_FIELD (setFieldV3 slot))`). Two shapes
-- that agree today are two shapes that disagree later, and a name carrying "Value8" that is NOT the
-- deployed value8 member is the worse half of the pair. Its witnesses are restated below on the
-- DEPLOYED wrap, so nothing is lost.
--
-- The freeze-EXCEPT setField carries the same 46-PI rotated prefix as the old freeze-ALL member; the
-- VALUE8 weld appends 8 (was 7 — the ninth lane), so the deployed bare member is 54 PIs (58 after
-- the uniform rc wrap). ⚑ FLAG DAY: every setField VK and every consumer reading PI slot ≥ 53 moves.
#guard (setFieldV3 0).piCount == 39
#guard (withSetFieldCompletionPins 0 (withSelectorGate EffectVmEmitSetField.SEL_SET_FIELD
  (setFieldV3 0))).piCount == 47
#guard (withSetFieldCompletionPins 7 (withSelectorGate EffectVmEmitSetField.SEL_SET_FIELD
  (setFieldV3 7))).piCount == 47
-- The eight published lane columns really are the NONET's, ninth lane included (not `113 + 8·slot`).
#guard (List.finRange 8).map (fun k => fieldLaneCol 0 k.succ) == [113, 114, 115, 116, 117, 118, 119, 176]
#guard (List.finRange 8).map (fun k => fieldLaneCol 5 k.succ) == [148, 149, 150, 151, 152, 153, 154, 181]
-- Additive: width / tables / sites / ranges are the freeze-EXCEPT member's (the pins add no column).
#guard (withSetFieldCompletionPins 3 (setFieldV3 3)).traceWidth == (setFieldV3 3).traceWidth
#guard (withSetFieldCompletionPins 3 (setFieldV3 3)).tables.length == (setFieldV3 3).tables.length
#guard (withSetFieldCompletionPins 3 (setFieldV3 3)).hashSites.length == 0
  && (withSetFieldCompletionPins 3 (setFieldV3 3)).ranges.length == 0
-- The pins are `.piBinding`s: no mem-op / map-op is added past the freeze-EXCEPT member's.
#guard (memOpsOf (withSetFieldCompletionPins 5 (setFieldV3 5))).length
  == (memOpsOf (setFieldV3 5)).length
#guard (mapOpsOf (withSetFieldCompletionPins 5 (setFieldV3 5))).length
  == (mapOpsOf (setFieldV3 5)).length

/-! ### The DSL rc-EMIT (`withDfaRcPins`) — the `Witnessed{Dfa}` route-commitment PI exposure.

A `Witnessed{Dfa}` caveat (a DSL `CellProgram` predicate — e.g. the relay router
`dregg-dfa-routing-v1`) is verified OFF-AIR by the executor's `DslCircuitDfaVerifier`; the deployed
turn descriptor previously emitted NO PI for it, so a pure light client could not connect the
re-proven DSL leaf (`circuit-prove::dsl_leaf_adapter`) to the deployed leg — the named BIG-BANG
piece (`dsl_leaf_adapter.rs` module doc; the Lean refutation is `Dregg2.Circuit.DslBackingAttack`).

The emit: the caveat region carries a 4-felt DFA ROUTE-COMMITMENT carrier at `C_RC_OFF` (offsets
39..42, past the MANIFEST fold's carrier at 38). The producer fills it with
`custom_proof_pi_commitment(DfaProofWire.public_inputs)` — the SAME derivation the custom carrier's
`custom_proof_commitment` binds, term-for-term — on a Dfa-gated turn, ZERO otherwise (the absent
sentinel: a turn WITHOUT a Dfa caveat publishes zeros and still proves; the
executor/verifier anchors the published value, real-or-zero, off the turn's own witnessed
predicates). `withDfaRcPins` publishes the carrier as 4 TAIL PIs (`g.piCount + k`), the Dfa twin of
`customPiExposure` — applied to EVERY `v3Registry` member (the caveat is a precondition, not an
effect: any cap-authorized turn can carry it), so the per-turn FOLD can `connect` the DSL sub-proof
leaf's in-circuit PI-commitment to the deployed leg at these slots (the dual-expose the fold lane
mints).

⚑ **THE rc-FOLD FLAG DAY, and what it repairs.** These pins used to be the WHOLE emit, and the
doc here used to say — correctly — that they are "satisfiable at any uniformly-filled value". That
is precisely `UnforcedPiPins`'s definition of an unforced pin: the carrier was read by NO other
constraint, so the prover chose the column AND the published slot, and a real adversary moves
both. `dropUnforcedPins` deleted all 144 of them (4 per member) as part of the 159 — the right
call on the emit as it stood, and it took the `CarrierWitness::Dsl` fold arm down with it
(`ivc_turn_chain::dsl_rc_claim_pi_lo` locates the rc slot BY the pin and fails closed).

The repair is NOT to exempt the pins from the subtraction, and NOT to teach the fold to accept an
unpinned slot: it is to make the columns genuinely FORCED. `caveatV3SitesAt` now absorbs the
carrier into the PUBLISHED caveat commitment (`caveatCommitRc`, two further chip sites), so:

  * the four columns are read by NON-pin constraints with a row denotation (chip lookups after
    graduation) ⇒ they are in `UnforcedPiPins.forcedCols` ⇒ the pins survive the subtraction on
    their own merits, with the subtraction itself unchanged;
  * `rotV3_caveat_binds_manifest_and_rc` / `rotV3_moved_rc_moves_the_published_caveat_commit`:
    an adversary that moves the carrier AND every PI these pins publish still moves PI
    `piCount + 3`, which the verifier reconstructs from the turn's own witnessed predicates. -/

-- `CAVEAT_REGION_OFF` (= `2 * B_SPAN`) is defined with the other span constants in §1, so the whole
-- file can name it; it used to be minted HERE, ~5700 lines after the first `+ 478` that meant it.

/-- **`withDfaRcPins g`** — APPEND 4 `.piBinding .last` pins publishing the caveat-region DFA
route-commitment carrier (`EFFECT_VM_WIDTH + CAVEAT_REGION_OFF + C_RC_OFF + k`, `k < 4`) as 4 TAIL
PIs (`g.piCount + k`), bumping `piCount` by 4. Mirrors `withAfterOctetPins` exactly — additive, no
site / range / mem-op / map-op touched, so every existing forcing keystone lifts by
`List.mem_append_left` (the peel below). -/
def withDfaRcPins (g : EffectVmDescriptor2) : EffectVmDescriptor2 :=
  { g with
    piCount := g.piCount + 4
    constraints := g.constraints ++ (List.range 4).map (fun k =>
      VmConstraint2.base (.piBinding .last (EFFECT_VM_WIDTH + CAVEAT_REGION_OFF + (C_RC_OFF + k))
        (g.piCount + k))) }

/-- The 4 rc pins are the ONLY constraints past the inner descriptor's (single `++`) — the
`strips_to` shape apex re-keys peel through. -/
theorem withDfaRcPins_constraints (g : EffectVmDescriptor2) :
    (withDfaRcPins g).constraints
      = g.constraints ++ (List.range 4).map (fun k =>
          VmConstraint2.base (.piBinding .last (EFFECT_VM_WIDTH + CAVEAT_REGION_OFF + (C_RC_OFF + k))
            (g.piCount + k))) := rfl

/-- The rc pins are `.piBinding`s, so they contribute NO mem-op (the mem log is unchanged). -/
theorem memOpsOf_withDfaRcPins (g : EffectVmDescriptor2) :
    memOpsOf (withDfaRcPins g) = memOpsOf g := by
  simp [memOpsOf, withDfaRcPins, List.filterMap_append, List.filterMap_map]

/-- The rc pins contribute NO map-op (the map log is unchanged). -/
theorem mapOpsOf_withDfaRcPins (g : EffectVmDescriptor2) :
    mapOpsOf (withDfaRcPins g) = mapOpsOf g := by
  simp [mapOpsOf, withDfaRcPins, List.filterMap_append, List.filterMap_map]

/-- **THE PEEL — `Satisfied2 (withDfaRcPins g) ⟹ Satisfied2 g`.** The wrap only APPENDS
`.piBinding` constraints (and bumps `piCount`): the inner constraints stay members
(`List.mem_append_left`), sites / ranges / mem / map logs are unchanged, so every existing
per-effect soundness lemma lifts to the wrapped descriptor by peeling the wrap first. Mirrors
`satisfied2_of_withAfterOctetPins`. -/
theorem satisfied2_of_withDfaRcPins (hash : List ℤ → ℤ) (g : EffectVmDescriptor2)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (h : Satisfied2 hash (withDfaRcPins g) minit mfin maddrs t) :
    Satisfied2 hash g minit mfin maddrs t := by
  have hmem : memLog (withDfaRcPins g) t = memLog g t := by
    simp [memLog, memOpsOf_withDfaRcPins]
  have hmap : mapLog (withDfaRcPins g) t = mapLog g t := by
    simp [mapLog, mapOpsOf_withDfaRcPins]
  exact
    { rowConstraints := fun i hi c hc => h.rowConstraints i hi c (by
        rw [withDfaRcPins_constraints]; exact List.mem_append_left _ hc)
    , rowHashes := h.rowHashes
    , rowRanges := h.rowRanges
    , memAddrsNodup := h.memAddrsNodup
    , memClosed := fun op hop => h.memClosed op (by rw [hmem]; exact hop)
    , memDisciplined := by rw [← hmem]; exact h.memDisciplined
    , memBalanced := by rw [← hmem]; exact h.memBalanced
    , memTableFaithful := by rw [← hmem]; exact h.memTableFaithful
    , mapTableFaithful := by rw [← hmap]; exact h.mapTableFaithful }

/-- **`withDfaRcPins_publishes` — the `rotV3_publishes`-shape forcing.** On any LAST row of a
`Satisfied2` witness, each of the 4 published TAIL PIs (`g.piCount + k`) EQUALS its caveat-region
route-commitment carrier column — so the fold reads the carrier off the PI vector: a leg claiming a
DIFFERENT rc than the one the trace carries is UNSAT, and the fold's `connect` to the re-proven DSL
leaf's in-circuit commitment makes an unwitnessed Dfa predicate a LIGHT-CLIENT refusal, not just a
re-executor one. -/
theorem withDfaRcPins_publishes (hash : List ℤ → ℤ) (g : EffectVmDescriptor2)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hsat : Satisfied2 hash (withDfaRcPins g) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hlast : i + 1 = t.rows.length) :
    ∀ k : Fin 4, (envAt t i).loc (EFFECT_VM_WIDTH + CAVEAT_REGION_OFF + (C_RC_OFF + k.val))
      ≡ (envAt t i).pub (g.piCount + k.val) [ZMOD 2013265921] := by
  intro k
  have hlastt : (i + 1 == t.rows.length) = true := by simp [hlast]
  have hin : VmConstraint2.base
      (.piBinding .last (EFFECT_VM_WIDTH + CAVEAT_REGION_OFF + (C_RC_OFF + k.val)) (g.piCount + k.val))
      ∈ (withDfaRcPins g).constraints := by
    rw [withDfaRcPins_constraints]
    exact List.mem_append_right _ (List.mem_map.mpr ⟨k.val, List.mem_range.mpr k.isLt, rfl⟩)
  have h := hsat.rowConstraints i hi _ hin
  simp only [VmConstraint2.holdsAt, hlastt, holdsVm_piLast_true] at h
  exact h

/-- **THE PIN/FOLD TIE (the anti-vacuity statement).** The four columns `withDfaRcPins` publishes
are LITERALLY the list `caveatCommitRc` absorbs — by `rfl`, not by a naming convention. If the
region layout ever moves one without the other, THIS breaks. -/
theorem withDfaRcPins_pins_the_folded_columns (base : Nat) (a : Assignment) :
    (List.range 4).map (fun k => a (base + (C_RC_OFF + k))) = rcAt base a := rfl

/-- **EVERY PUBLISHED rc SLOT IS A FOLDED COLUMN.** On the LAST row of a `Satisfied2` witness of
the wrapped member, published PI `g.piCount + k` equals entry `k` of the very list the PUBLISHED
caveat commitment absorbs. The pin no longer sits BESIDE the fold; it sits ON it — which is why
the pin now survives `dropUnforcedPins` and why the move-both adversary is refused. -/
theorem withDfaRcPins_publishes_a_folded_column (hash : List ℤ → ℤ) (g : EffectVmDescriptor2)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hsat : Satisfied2 hash (withDfaRcPins g) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hlast : i + 1 = t.rows.length) :
    ∀ k : Fin 4,
      (rcAt (EFFECT_VM_WIDTH + CAVEAT_REGION_OFF) (envAt t i).loc).getD k.val 0
        ≡ (envAt t i).pub (g.piCount + k.val) [ZMOD 2013265921] := by
  intro k
  have h := withDfaRcPins_publishes hash g minit mfin maddrs t hsat i hi hlast k
  have hget : (rcAt (EFFECT_VM_WIDTH + CAVEAT_REGION_OFF) (envAt t i).loc).getD k.val 0
      = (envAt t i).loc (EFFECT_VM_WIDTH + CAVEAT_REGION_OFF + (C_RC_OFF + k.val)) := by
    fin_cases k <;> rfl
  rw [hget]
  exact h

#assert_axioms satisfied2_of_withDfaRcPins
#assert_axioms withDfaRcPins_publishes
#assert_axioms withDfaRcPins_pins_the_folded_columns
#assert_axioms withDfaRcPins_publishes_a_folded_column

/-- **`factoryV3Carriers`** — the deployed `factoryVmDescriptor2R24` WITH the two direct carrier-octet
pin cohorts TAIL-appended after PI 46: the `child_vk8` octet (limbs 89..=96, PI 47..54 — factory's
installed child VK, which the hatchery-INVARIANT carrier also rides) then the `contract_hash8` octet
(limbs 97..=104, PI 48..55 — the hatchery-mint `HpresProof::Attested` content hash, ZERO on a plain
factory turn). `piCount 40 → 56`. Both pins publish the STEP-2-filled octet; the SDK/executor thread
the material (`child_vk` = the executor's `effective_vk`; `contract_hash` at the hatchery-mint site). -/
def factoryV3Carriers : EffectVmDescriptor2 :=
  withAfterOctetPins (withAfterOctetPins factoryV3 B_CHILD_VK_OCTET) B_CONTRACT_HASH_OCTET

-- The two octet cohorts land the child_vk pins at PI 40..47 and the contract_hash pins at 48..55.
#guard factoryV3.piCount == 40
#guard factoryV3Carriers.piCount == 56
-- The grow-gate map-ops (accounts set-insert) survive the additive octet pins (they are `.piBinding`s).
#guard (mapOpsOf factoryV3Carriers).length == 2
-- traceWidth / tables / sites are untouched by the additive pins (registry invariants hold).
#guard factoryV3Carriers.traceWidth == factoryV3.traceWidth
#guard factoryV3Carriers.tables.length == 5

/-! ### The BRIDGE-MINT FELT MINT-HASH PIN (`mintV3BridgeHash`) — the bridge carrier's
deployed-leg exposure (STEP 3 of the felt-domain mint_hash thread).

The BridgeMint row's `mint_hash` (`param0`, col `prmCol 0`) was, until the STEP-1 executor
re-align, the byte-domain `hash_to_bb(blake3(nullifier ‖ postcard(source_root) ‖ dest ‖ asset))`
— read by ZERO constraints and recomputable by NO circuit (the 68297080e named residual: pinning
it would be a dead-end exposure the felt-domain note-spend leaf could never connect). Since the
re-align it is the FELT-DOMAIN `note_spend_mint_hash_felt` = `hash_fact(hash_fact(nullifier,
[root, dest_fed, asset]), [value_lo, value_hi])` over the SIX compressed felts the executor's
`apply_bridge_mint` enforces the real note-spend STARK against (`verify_note_spend_dsl_full`) —
the SAME identity the recursion note-spend leaf (`circuit-prove::note_spend_leaf_adapter`)
recomputes IN-AIR and exposes at its claim lane 6.

`withMintHashPin` publishes that column as ONE appended PI (the bridge twin of the noteSpend
nullifier weld — a FIRST-row pin on `prmCol 0`, the mint row is row 0), so the per-turn FOLD can
`connect` the deployed leg's published mint identity to the re-proven note-spend leaf's exposed
lane: a leg claiming a mint identity no verifying note-spend backs is UNSAT at the binding node.
The THIRD-EDGE tie (teeth == committed-authority): the published PI is the trace's `param0`,
which `effects_hash` absorbs (PI-bound), and the VERIFIER's reconstruction recomputes it from the
turn's OWN `PortableNoteProof` via `convert_turn_effects_to_vm` — executor-derived, never a
prover-chosen free PI. Rust producer twin: `trace_rotated.rs`'s BridgeMint arm (PI 46, pre-rc). -/

/-- The bridge-mint mint-hash parameter column (`param::MINT_HASH = param0`, `prmCol 0`) — the
mint row's felt-domain mint identity (the STEP-1 re-aligned `note_spend_mint_hash_felt`). -/
def MINT_HASH_PARAM_COL : Nat := prmCol 0

/-- **`withMintHashPin g`** — APPEND one `.piBinding .first` pin publishing the mint row's
`mint_hash` param (`prmCol 0`) as ONE TAIL PI (`g.piCount`), bumping `piCount` by 1. Mirrors
`withAfterOctetPins` exactly — additive, no site / range / mem-op / map-op touched, so every
existing forcing keystone lifts by `List.mem_append_left` (the peel below). -/
def withMintHashPin (g : EffectVmDescriptor2) : EffectVmDescriptor2 :=
  { g with
    piCount := g.piCount + 1
    constraints := g.constraints
      ++ [VmConstraint2.base (.piBinding .first MINT_HASH_PARAM_COL g.piCount)] }

/-- The mint-hash pin is the ONLY constraint past the inner descriptor's (single `++`). -/
theorem withMintHashPin_constraints (g : EffectVmDescriptor2) :
    (withMintHashPin g).constraints
      = g.constraints
        ++ [VmConstraint2.base (.piBinding .first MINT_HASH_PARAM_COL g.piCount)] := rfl

/-- The pin is a `.piBinding`, so it contributes NO mem-op (the mem log is unchanged). -/
theorem memOpsOf_withMintHashPin (g : EffectVmDescriptor2) :
    memOpsOf (withMintHashPin g) = memOpsOf g := by
  simp [memOpsOf, withMintHashPin, List.filterMap_append]

/-- The pin contributes NO map-op (the map log is unchanged). -/
theorem mapOpsOf_withMintHashPin (g : EffectVmDescriptor2) :
    mapOpsOf (withMintHashPin g) = mapOpsOf g := by
  simp [mapOpsOf, withMintHashPin, List.filterMap_append]

/-- **THE PEEL** — `Satisfied2 (withMintHashPin g) ⟹ Satisfied2 g`. The wrap only APPENDS one
`.piBinding` constraint (and bumps `piCount`): the inner constraints stay members
(`List.mem_append_left`), sites / ranges / mem / map logs are unchanged, so every existing
per-effect soundness lemma lifts to the wrapped descriptor by peeling the wrap first. Mirrors
`satisfied2_of_withAfterOctetPins`. -/
theorem satisfied2_of_withMintHashPin (hash : List ℤ → ℤ) (g : EffectVmDescriptor2)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (h : Satisfied2 hash (withMintHashPin g) minit mfin maddrs t) :
    Satisfied2 hash g minit mfin maddrs t := by
  have hmem : memLog (withMintHashPin g) t = memLog g t := by
    simp [memLog, memOpsOf_withMintHashPin]
  have hmap : mapLog (withMintHashPin g) t = mapLog g t := by
    simp [mapLog, mapOpsOf_withMintHashPin]
  exact
    { rowConstraints := fun i hi c hc => h.rowConstraints i hi c (by
        rw [withMintHashPin_constraints]; exact List.mem_append_left _ hc)
    , rowHashes := h.rowHashes
    , rowRanges := h.rowRanges
    , memAddrsNodup := h.memAddrsNodup
    , memClosed := fun op hop => h.memClosed op (by rw [hmem]; exact hop)
    , memDisciplined := by rw [← hmem]; exact h.memDisciplined
    , memBalanced := by rw [← hmem]; exact h.memBalanced
    , memTableFaithful := by rw [← hmem]; exact h.memTableFaithful
    , mapTableFaithful := by rw [← hmap]; exact h.mapTableFaithful }

/-- **`withMintHashPin_publishes` — the `rotV3_publishes`-shape forcing.** On the FIRST row of a
`Satisfied2` witness, the published TAIL PI (`g.piCount`) EQUALS the mint row's `mint_hash`
param column — so the fold reads the mint identity off the PI vector: a leg publishing a
DIFFERENT identity than the one its trace (and `effects_hash`) carries is UNSAT, and the fold's
`connect` to the re-proven note-spend leaf's in-AIR-recomputed lane 6 makes an unbacked bridge
mint a LIGHT-CLIENT refusal, not just a re-executor one. -/
theorem withMintHashPin_publishes (hash : List ℤ → ℤ) (g : EffectVmDescriptor2)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hsat : Satisfied2 hash (withMintHashPin g) minit mfin maddrs t)
    (h0 : 0 < t.rows.length) :
    (envAt t 0).loc MINT_HASH_PARAM_COL ≡ (envAt t 0).pub g.piCount [ZMOD 2013265921] := by
  have hin : VmConstraint2.base (.piBinding .first MINT_HASH_PARAM_COL g.piCount)
      ∈ (withMintHashPin g).constraints := by
    rw [withMintHashPin_constraints]
    exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
  have h := hsat.rowConstraints 0 h0 _ hin
  have hfirstt : ((0 : Nat) == 0) = true := rfl
  simp only [VmConstraint2.holdsAt, hfirstt, holdsVm_piFirst_true] at h
  exact h

/-- **TOOTH** — a published mint identity that is NOT the trace's mint row `param0` is UNSAT. -/
theorem withMintHashPin_rejects_forged_pi (hash : List ℤ → ℤ) (g : EffectVmDescriptor2)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (h0 : 0 < t.rows.length)
    (hcanonParam : 0 ≤ (envAt t 0).loc MINT_HASH_PARAM_COL
      ∧ (envAt t 0).loc MINT_HASH_PARAM_COL < 2013265921)
    (hcanonPI : 0 ≤ (envAt t 0).pub g.piCount ∧ (envAt t 0).pub g.piCount < 2013265921)
    (hforged : (envAt t 0).loc MINT_HASH_PARAM_COL ≠ (envAt t 0).pub g.piCount) :
    ¬ Satisfied2 hash (withMintHashPin g) minit mfin maddrs t :=
  fun hsat => hforged (canon_eq_of_modEq hcanonParam hcanonPI
    (withMintHashPin_publishes hash g minit mfin maddrs t hsat h0))

#assert_axioms satisfied2_of_withMintHashPin
#assert_axioms withMintHashPin_publishes
#assert_axioms withMintHashPin_rejects_forged_pi

/-- **`mintV3BridgeHash`** — the deployed `mintVmDescriptor2R24` WITH the felt mint-hash pin
TAIL-appended after the 39-PI rotated prefix (PI 39; `piCount 39 → 40`). The inner member is the
UNCHANGED gated bridge-mint (`withSelectorGate selM.MINT mintV3`); the pin publishes the STEP-1
felt-domain mint identity the producer fills (`trace_rotated.rs` BridgeMint arm). The
supply-mint member (`supplyMintV3`, `sel.MINT`) is NOT pinned — its `(target, slot)` mint_hash
stays a byte-domain fold with no fold-connect consumer. -/
def mintV3BridgeHash : EffectVmDescriptor2 :=
  withMintHashPin (withSelectorGate EffectVmEmitMint.selM.MINT mintV3)

-- The pin lands at PI 46 (the first slot past the four rotated commit pins — the SAME arithmetic
-- as `ROT_NULLIFIER_PI`/`ROT_FEE_PI`; bridge-mint never co-occurs with note-spend/fee on one
-- descriptor, so sharing the slot index is sound); rc rides 47..50 on the deployed wrap.
#guard mintV3.piCount == 39
#guard mintV3BridgeHash.piCount == 40
-- traceWidth / tables / sites / ops are untouched by the additive pin (registry invariants hold).
#guard mintV3BridgeHash.traceWidth == mintV3.traceWidth
#guard mintV3BridgeHash.tables.length == mintV3.tables.length
#guard (mapOpsOf mintV3BridgeHash).length == (mapOpsOf mintV3).length
#guard (memOpsOf mintV3BridgeHash).length == (memOpsOf mintV3).length

/-- **`v3RegistryBare`** — the full cohort at the rotated block BEFORE the uniform DSL rc-EMIT wrap
(keys = the v2 keys suffixed `R24`; wire strings via `emitVmJson2`; driver `EmitRotationV3.lean`).
The deployed registry is `v3Registry = v3RegistryBare.map withDfaRcPins` below. -/
def v3RegistryBare : List (String × EffectVmDescriptor2) :=
  [ ("transferVmDescriptor2R24", v3OfFrozen EffectVmEmitTransfer.transferVmDescriptor)
  , ("burnVmDescriptor2R24", v3OfFrozen EffectVmEmitBurn.burnVmDescriptor)
  , ("mintVmDescriptor2R24", mintV3BridgeHash)
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
  , ("revokeVmDescriptor2R24", revokeV3)
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
  , ("factoryVmDescriptor2R24", factoryV3Carriers)
  , ("spawnVmDescriptor2R24", spawnV3)
  , ("receiptArchiveVmDescriptor2R24", receiptArchiveV3)
  , ("cellUnsealVmDescriptor2R24", cellUnsealV3)
  , ("emitEventVmDescriptor2R24", v3OfFrozen EffectVmEmitEmitEvent.emitEventVmDescriptor) ]
    -- THE VALUE8 EPOCH (the deployed setField members, was the freeze-ALL `v3OfFrozen`). The
    -- freeze-ALL wrap froze ALL 64 fields completion lanes BEFORE↔AFTER — including the WRITTEN
    -- slot's — so a `FieldElement = [u8;32]` with any nonzero byte outside `28..32` could not
    -- prove: the protocol could not express an honest 32-byte field write. `setFieldV3 slot`
    -- (freeze-EXCEPT) frees exactly the written slot's 8 completion lanes (`fieldsSlotLanes slot`,
    -- the seven historical PLUS the flag-day ninth at `176 + slot`) and
    -- `withSetFieldCompletionPins slot` PUBLISHES them as 8 tail PIs, so the high 224 bits are
    -- BOUND (a lane forged off its published PI is UNSAT — `withSetFieldCompletionPins_rejects_forged_pi`)
    -- rather than frozen. The other seven slots stay fully frozen.
  ++ (List.finRange 8).map fun slot =>
      (s!"setFieldVmDescriptor2-{slot.val}R24",
        withSetFieldCompletionPins slot
          (withSelectorGate EffectVmEmitSetField.SEL_SET_FIELD (setFieldV3 slot)))

/-- **`v3Registry`** — the DEPLOYED full cohort: every `v3RegistryBare` member wrapped OUTERMOST
through `withDfaRcPins` (the dsl rc-EMIT — a `Witnessed{Dfa}` caveat is a PRECONDITION any
cap-authorized turn can carry, so the whole cohort exposes the 4-felt route-commitment carrier as
its LAST 4 member PIs: slots `piCount − 4 .. piCount − 1` per member, riding AFTER every per-effect
extra pin and BEFORE the 16 wide commit PIs `wideAppend` lands on the wide twin). Downstream
registries (`v3RegistryCapOpen`, `v3RegistryWide`, the umem weld) inherit by construction. -/
def v3Registry : List (String × EffectVmDescriptor2) :=
  v3RegistryBare.map (fun (k, d) => (k, withDfaRcPins d))

-- The rc wrap is uniform: every member gains EXACTLY 4 PIs and NO width/table/site change.
#guard (v3Registry.zip v3RegistryBare).all fun ((_, w), (_, b)) =>
  w.piCount == b.piCount + 4 && w.traceWidth == b.traceWidth
    && w.tables.length == b.tables.length && w.hashSites.length == b.hashSites.length
-- The deployed transfer publishes rc at slots 39..42 (piCount 39 → 43); the STEP-3 factory
-- (piCount 56) at 56..59; the custom exposure member (piCount 55 — the faithful carrier's
-- sixteen exposure pins at 39..54) at 55..58; the bridge-mint felt mint-hash member (piCount 40 —
-- the mint-hash pin at 39) at 40..43.
#guard (v3Registry.lookup "transferVmDescriptor2R24").any (·.piCount == 43)
#guard (v3Registry.lookup "factoryVmDescriptor2R24").any (·.piCount == 60)
#guard (v3Registry.lookup "customVmDescriptor2R24").any (·.piCount == 59)
#guard (v3Registry.lookup "mintVmDescriptor2R24").any (·.piCount == 44)

#guard v3Registry.length == 36
-- Every registry entry emits a versioned v2 wire string with the rotated width, the five
-- EPOCH tables, and the four appended PI slots.
-- cheap STRUCTURAL smoke (see EffectVmEmitV2): the emitVmJson2 per-descriptor byte-pins cover
-- serialization exactly; re-serializing all 45 v3Registry entries here was ~redundant elab compute.
#guard v3Registry.all fun (_, d) => !d.name.isEmpty && !d.constraints.isEmpty && d.traceWidth != 0
-- Phase B-GATE: each graduated registry descriptor's width is the rotated base PLUS `7·n_sites`
-- lane columns (n_sites varies by v1 face), so the width is `≥ base` and the surplus is a
-- multiple of 7 (`CHIP_OUT_LANES - 1`) — EXCEPT the custom member, whose surplus additionally
-- carries 8 teeth columns (4 commitment + 4 VK; the faithful custom-carrier flag day).
-- Concrete per-descriptor widths are pinned by the emit goldens + the Rust registry fingerprints.
#guard v3Registry.all fun (k, d) =>
  let teeth := if k == "customVmDescriptor2R24" then 8 else 0
  EFFECT_VM_WIDTH + APPENDIX_SPAN ≤ d.traceWidth
    && (d.traceWidth - (EFFECT_VM_WIDTH + APPENDIX_SPAN) - teeth) % (CHIP_OUT_LANES - 1) == 0
#guard v3Registry.all fun (_, d) => d.tables.length == 5
#guard v3Registry.all fun (_, d) => d.hashSites.length == 0 && d.ranges.length == 0
-- The rotated transfer: the v1 graduation's constraints + 24 welds + 4 pins + 138 chip sites
-- (v15: 63 per block after the key-nonet flag day, + the 12 caveat sites incl. the rc pair).
#guard (v3Of EffectVmEmitTransfer.transferVmDescriptor).constraints.length
        == transferVmDescriptor2.constraints.length + 24 + 4 + 144
#guard (v3Of EffectVmEmitTransfer.transferVmDescriptor).piCount == 39
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
-- The extras ride: attenuate carries ONLY the submask non-amp lookup (+1; the two scalar map-ops were
-- DROPPED — the faithful 8-felt cap-write is forced by the cap-open AFTER-SPINE, not an arity-2 map-op),
-- revokeCapability carries NO extras (its scalar held-read + remove-write pair is DROPPED — the
-- REMOVE-shaped after-spine deploy, `effCapRemoveV3`), setFieldDyn its 2 mem ops.
-- Both rebased onto the ROTATED-limb cap-write base (`v3OfWithCapWrite` over the tick face).
#guard attenuateV3.constraints.length
        == (v3OfCapWrite EffectVmEmitAttenuateA.attenuateVmDescriptorGenuineNoRecomputeTick).constraints.length + 1
#guard revokeCapabilityV3.constraints.length
        == (v3OfCapWrite EffectVmEmitAttenuateA.attenuateVmDescriptorGenuineNoRecomputeTick).constraints.length
#guard (memOpsOf setFieldDynV3).length == 2
#guard (mapOpsOf setFieldDynV3).length == 0
#guard (mapOpsOf attenuateV3).length == 0
#guard (mapOpsOf revokeCapabilityV3).length == 0
-- The cap-family WRITE close (INSERT/REMOVE-shaped after-spine deploy): delegate/grantCap/introduce
-- carry NO map ops (the arity-2 scalar pair is DROPPED — the faithful 8-felt cap-tree INSERT is
-- FORCED by the deployed `effCapInsertV3` wrap, never the lane-0 squeeze); delegateAtten keeps ONLY
-- the submask non-amp lookup (+1); revokeDelegation keeps ONLY the §14.EPOCH bump gate (+1).
#guard delegateV3.constraints.length
        == (v3OfCapWrite EffectVmEmitAttenuateA.attenuateVmDescriptorGenuineNoRecomputeTick).constraints.length
#guard grantCapWriteV3.constraints.length
        == (v3OfCapWrite EffectVmEmitAttenuateA.attenuateVmDescriptorGenuineNoRecomputeTick).constraints.length
#guard introduceWriteV3.constraints.length
        == (v3OfCapWrite EffectVmEmitAttenuateA.attenuateVmDescriptorGenuineNoRecomputeTick).constraints.length
#guard delegateAttenV3.constraints.length
        == (v3OfCapWrite EffectVmEmitAttenuateA.attenuateVmDescriptorGenuineNoRecomputeTick).constraints.length + 1
#guard revokeDelegationWriteV3.constraints.length
        == (v3OfCapWrite EffectVmEmitAttenuateA.attenuateVmDescriptorGenuineNoRecomputeTick).constraints.length + 1
#guard refreshDelegationWriteV3.constraints.length
        == (v3OfCapWrite EffectVmEmitAttenuateA.attenuateVmDescriptorGenuineNoRecomputeTick).constraints.length
#guard (mapOpsOf delegateV3).length == 0
#guard (mapOpsOf grantCapWriteV3).length == 0
#guard (mapOpsOf introduceWriteV3).length == 0
#guard (mapOpsOf delegateAttenV3).length == 0
#guard (mapOpsOf revokeDelegationWriteV3).length == 0
#guard (mapOpsOf refreshDelegationWriteV3).length == 0
-- spawn keeps EXACTLY its 2 cells-tree grow-gate map-ops (limb 0); the 2 cap-tree map-ops (limb 25)
-- are DROPPED (the INSERT-shaped after-spine deploy — the cap handoff rides `effCapInsertV3`).
#guard (mapOpsOf spawnWriteV3).length == 2
-- The rotated Custom carries EXACTLY its one proof-binding op + the sixteen `customPiExposure`
-- PI pins past the rotated passthrough base (no mem/map ops — the recursive-proof binding is
-- Custom's only NEWLY-EXPRESSIBLE leg; the sixteen pins publish commitment8 + canonical VK8).
#guard customV3.constraints.length == (v3Of customV1Face).constraints.length + 1 + 16
#guard (proofBindsOf customV3).length == 1
#guard (memOpsOf customV3).length == 0
#guard (mapOpsOf customV3).length == 0
#guard graduable (rotateV3 customV1Face)

/-! ### The extras' theorems, transported (the §7/§8 legs survive the rotation). -/

/-- The extras' op surface is EXACTLY the original's: the rotated graduation contributes
no mem ops (both sides are concrete lists; the kernel decides this by reduction). -/
theorem memOpsOf_setFieldDynV3 : memOpsOf setFieldDynV3 = memOpsOf setFieldDynVmDescriptor2 :=
  rfl

/-- The rotated attenuate carries NO map ops: the faithful 8-felt in-place UPDATE-AT-KEY is FORCED by
the cap-open AFTER-SPINE (`CapOpenEmit.effCapOpenWriteV3_forces_write8`), not the arity-2 scalar map-op
pair (which left the high felts unbound — the ~31-bit lane-0 squeeze). Only the `submaskLookup`
(`granted ⊑ held`) survives in the base extras, and a lookup is not a map op. -/
theorem mapOpsOf_attenuateV3 :
    mapOpsOf attenuateV3 = [] :=
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

/-- **The rotated cap-crown NON-AMPLIFICATION leg** — on an active attenuate row of a `Satisfied2`
witness of the ROTATED attenuate, the conferred (narrowed) rights are a bitwise SUBMASK of the held
rights (`keep ⊑ held`), forced by the surviving `submaskLookup` against the realizable subset table.

The cap-root WRITE itself (the faithful 8-felt in-place UPDATE-AT-KEY) is NO LONGER forced here by an
arity-2 scalar map-op — that mechanism left the seven high felts of the ~124-bit cap-root unbound (the
lane-0 squeeze). It is now forced downstream by the cap-open AFTER-SPINE
(`CapOpenEmit.effCapOpenWriteV3_forces_write8`, over the committed 8-felt `beforeCapRootCols` /
`afterCapRootCols` groups), which the attenuate CLASS-A refinement trio
(`RotatedKernelRefinementCapFamily.attenuate_descriptorRefines_sat`) consumes. So this leg keeps only
the non-amplification (submask) tooth. -/
theorem attenuateV3_non_amp (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hsub : t.tf (.custom SUBMASK_TID) = subsetTable MASK_BITS)
    (hsat : Satisfied2 hash attenuateV3 minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length)
    (hactive : (envAt t i).loc sel.ATTENUATE_CAPABILITY = 1) :
    ∃ a b : Nat, (envAt t i).loc (prmCol KEEP_MASK) = (a : ℤ)
        ∧ (envAt t i).loc (prmCol HELD_MASK) = (b : ℤ) ∧ a &&& b = a := by
  have hrowc := hsat.rowConstraints i hi
  have hmem : ∀ c ∈ ([.lookup submaskLookup] : List VmConstraint2), c ∈ attenuateV3.constraints :=
    fun c hc => List.mem_append_right _ hc
  have hlook := hrowc (.lookup submaskLookup) (hmem _ (by simp))
  have hlook' : [(envAt t i).loc (prmCol KEEP_MASK), (envAt t i).loc (prmCol HELD_MASK)]
      ∈ t.tf (.custom SUBMASK_TID) := hlook
  rw [hsub] at hlook'
  obtain ⟨a, b, _, _, hab, hx, hy⟩ := (subsetTable_mem_iff MASK_BITS _ _).mp hlook'
  exact ⟨a, b, hx, hy, hab⟩

/-! ### The cap-family WRITE keystones — REBASED onto the INSERT/REMOVE-shaped after-spine deploy.

The former `<slot>V3_forces_write` theorems (delegate / grantCap / introduce / revokeDelegation) forced
the cap-tree write via the arity-2 scalar map-op pair — a mechanism that (a) left the seven high felts
of the ~124-bit cap-root unbound (the lane-0 squeeze) and (b) is SHAPE-UNSAT against the deployed
arity-7 `CanonicalCapTree`: `writesTo` is update-at-key, but a delegate/introduce SPLICES a fresh key
(no shared before/after path) and a revoke tombstones the leaf to the ZERO digest (no leaf-absorb
produces it). Those map-ops are DROPPED. The faithful 8-felt cap-tree writes are now forced downstream
by the deployed INSERT/REMOVE-shaped cap-open wraps
(`CapInsertEmit.effCapInsertV3_forces_write8` / `CapRemoveEmit.effCapRemoveV3_forces_write8`, over the
committed 8-felt `beforeCapRootCols`/`afterCapRootCols` groups), which the CLASS-A refinement trios
(`RotatedKernelRefinementCapFamily.{delegate,grantCap,delegateAtten,introduce,revokeDelegation}_descriptorRefines_sat`)
consume. What survives HERE: delegateAtten's non-amplification submask tooth and revokeDelegation's
§14.EPOCH bump gate. -/

/-- **`delegateAttenV3_non_amp` — the delegateAtten NON-AMPLIFICATION leg.** On an active grant row of a
`Satisfied2 delegateAttenV3` witness, the conferred (narrowed) rights are a bitwise SUBMASK of the held
rights (`keep ⊑ held`), forced by the surviving `submaskLookup` against the realizable subset table. The
cap-tree INSERT itself is forced downstream by the deployed `effCapInsertV3` wrap (see the section
header) — this leg keeps only the non-amplification tooth, exactly as `attenuateV3_non_amp`. -/
theorem delegateAttenV3_non_amp (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hsub : t.tf (.custom SUBMASK_TID) = subsetTable MASK_BITS)
    (hsat : Satisfied2 hash delegateAttenV3 minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length)
    (_hactive : (envAt t i).loc sel.GRANT_CAP = 1) :
    ∃ a b : Nat, (envAt t i).loc (prmCol KEEP_MASK) = (a : ℤ)
        ∧ (envAt t i).loc (prmCol HELD_MASK) = (b : ℤ) ∧ a &&& b = a := by
  have hrowc := hsat.rowConstraints i hi
  have hmem : ∀ c ∈ ([.lookup submaskLookup] : List VmConstraint2),
      c ∈ delegateAttenV3.constraints := fun c hc => List.mem_append_right _ hc
  have hlook := hrowc (.lookup submaskLookup) (hmem _ (by simp))
  have hlook' : [(envAt t i).loc (prmCol KEEP_MASK), (envAt t i).loc (prmCol HELD_MASK)]
      ∈ t.tf (.custom SUBMASK_TID) := hlook
  rw [hsub] at hlook'
  obtain ⟨a, b, _, _, hab, hx, hy⟩ := (subsetTable_mem_iff MASK_BITS _ _).mp hlook'
  exact ⟨a, b, hx, hy, hab⟩

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
      ≡ (envAt t i).loc (beforeEpochCol EFFECT_VM_WIDTH) + 1 [ZMOD 2013265921] := by
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
    (hcanonAfter : 0 ≤ (envAt t i).loc (afterEpochCol EFFECT_VM_WIDTH)
      ∧ (envAt t i).loc (afterEpochCol EFFECT_VM_WIDTH) < 2013265921)
    (hcanonBeforeBump : 0 ≤ (envAt t i).loc (beforeEpochCol EFFECT_VM_WIDTH) + 1
      ∧ (envAt t i).loc (beforeEpochCol EFFECT_VM_WIDTH) + 1 < 2013265921)
    (hwrong : (envAt t i).loc (afterEpochCol EFFECT_VM_WIDTH)
      ≠ (envAt t i).loc (beforeEpochCol EFFECT_VM_WIDTH) + 1) :
    ¬ Satisfied2 hash revokeDelegationWriteV3 minit mfin maddrs t :=
  fun hsat => hwrong (canon_eq_of_modEq hcanonAfter hcanonBeforeBump
    (revokeDelegationWriteV3_forces_epoch_bump hash minit mfin maddrs t hsat i hi hnl hactive))

-- (`refreshDelegationWriteV3_forces_write` — the arity-2 map-op DELEG-write theorem — is DELETED: the
-- scalar `delegReadOpRot`/`delegUpdateWriteOpRot` pair was shape-UNSAT against the deployed
-- native-8-felt witness heaps. The DELEG-tree UPDATE-AT-KEY is now FORCED by the deployed
-- `effCapOpenWriteV3` wrap: `CapOpenEmit.effCapOpenWriteV3_forces_write8`, consumed by
-- `RotatedKernelRefinementCapFamily.refreshDelegation_descriptorRefines_sat`.)

/-- The rotated Custom declares EXACTLY the one proof-binding op (the rotated graduation
contributes none; the extras add exactly `customV3ProofBind`). -/
theorem proofBindsOf_customV3 : proofBindsOf customV3 = [customV3ProofBind] := by
  have hbase : proofBindsOf (v3Of customV1Face) = [] := proofBindsOf_graduateV1 (rotateV3 customV1Face) _
  unfold proofBindsOf at hbase ⊢
  -- `customV3.constraints = ((v3Of …).constraints ++ [proofBind customV3ProofBind]) ++ customPiExposure`;
  -- the sixteen `customPiExposure` pins are all `.base (.piBinding …)`, contributing no proof-binds.
  show (((v3Of customV1Face).constraints ++ [VmConstraint2.proofBind customV3ProofBind])
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
    E.boundTo (customV3ProofBind.commit.map (·.eval (envAt t i).loc))
      (customV3ProofBind.vk.map (·.eval (envAt t i).loc)) := by
  have hm : customV3ProofBind ∈ proofBindsOf customV3 := by
    rw [proofBindsOf_customV3]; exact List.mem_cons_self
  exact proofBind_bound hash E customV3 hsat hm i hi
    (by simpa [customV3ProofBind, customProofBindAt, EmittedExpr.eval] using hactive)

#assert_axioms setFieldDynV3_memLog
#assert_axioms setFieldDynV3_readback_genuine
#assert_axioms attenuateV3_non_amp
#assert_axioms delegateAttenV3_non_amp
#assert_axioms revokeDelegationWriteV3_forces_epoch_bump
#assert_axioms revokeDelegationWriteV3_rejects_wrong_epoch
#assert_axioms epochBumpGate_forces
#assert_axioms proofBindsOf_customV3
#assert_axioms customV3_binds_proof
#assert_axioms noteSpendV3_grow_gate_forces_set_insert
#assert_axioms noteSpendV3_opens_delegation_ancestor

-- NON-VACUITY of the bound block, executable (Horner toy sponge): moving the heap-root limb
-- (offset 27) or the iroot moves the chained commitment the appendix pins.
#guard wireCommitR refSponge ((List.range 31).map (fun i => (300 + i : ℤ))) 7
  != wireCommitR refSponge (((List.range 31).map (fun i => (300 + i : ℤ))).set 27 999) 7
#guard wireCommitR refSponge ((List.range 31).map (fun i => (300 + i : ℤ))) 7
  != wireCommitR refSponge ((List.range 31).map (fun i => (300 + i : ℤ))) 8

/-! ## THE MULTI-WIDTH (`graduableWide`) ROTATION LIFTS — the hardened 15-bit availability
descriptors reach the rotation tower.

Mirrors of `graduable_rotateV3` / `graduable_rotateV3FrozenAuthority` / `v3OfFrozen` /
`rotV3Frozen_sound_v1` at the §10 multi-width graduation (`graduateV1Wide`,
`EffectVmEmitV2.lean`): a rotated `Satisfied2FaithfulWide` witness over a wide-graduable member
(e.g. `EffectVmEmitTransfer.transferVmDescriptorAvail`, whose borrow-weld limbs are 15-BIT range
teeth) lowers to its per-row v1 denotation `satisfiedVm` — which the availability keystone
(`transferAvail_derives_availability`) consumes. ADDITIVE: the single-width `graduable` path and
every existing registry member are untouched; rotation preserves the wide side conditions because
`rotateV3` appends only col-only sites and keeps `ranges` verbatim (the SAME facts
`graduable_rotateV3` uses). -/

/-- The WIDE graduation side conditions LIFT through the rotation (the `graduableWide` mirror of
`graduable_rotateV3`: appendix sites are col-only + chip-rate-fitting; ranges are verbatim). -/
theorem graduableWide_rotateV3 {d : EffectVmDescriptor} (h : graduableWide d = true) :
    graduableWide (rotateV3 d) = true := by
  unfold graduableWide at h ⊢
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
    · rcases List.mem_append.mp hs' with hs'' | hs'' <;> fin_cases hs'' <;> rfl
    · fin_cases hs' <;> rfl

/-- Continuity welds are CONSTRAINTS; `graduableWide` reads only sites/ranges (the wide mirror of
`graduable_rotateV3FrozenAuthority`). -/
theorem graduableWide_rotateV3FrozenAuthority {d : EffectVmDescriptor}
    (h : graduableWide d = true) : graduableWide (rotateV3FrozenAuthority d) = true := by
  have hr := graduableWide_rotateV3 h
  unfold rotateV3FrozenAuthority
  unfold graduableWide at hr ⊢
  simpa using hr

/-- **`v3OfFrozenWide d`** — the WIDE graduated rotated descriptor of a hardened member (the
`graduateV1Wide` analog of `v3OfFrozen`): same rotation + authority-continuity weld, range teeth
lowered per-width (the 15-bit borrow limbs into the 15-bit table). -/
def v3OfFrozenWide (d : EffectVmDescriptor)
    (hAdm : ∀ s ∈ (rotateV3FrozenAuthority d).hashSites,
        ChipArityAdmitted s.inputs.length := by graduate_arity) : EffectVmDescriptor2 :=
  graduateV1Wide (rotateV3FrozenAuthority d) hAdm

/-- **`rotV3FrozenWide_sound_v1`** — a `Satisfied2FaithfulWide` witness of the WIDE frozen
graduation yields the full v1 denotation of the original descriptor on every row (the
`graduableWide` mirror of `rotV3Frozen_sound_v1`). This is the bridge that lets a rotated witness
over the hardened availability descriptor reach `transferAvail_derives_availability`. -/
theorem rotV3FrozenWide_sound_v1 (permOut : List ℤ → List ℤ) (hash : List ℤ → ℤ)
    (d : EffectVmDescriptor)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hgrad : graduableWide d = true)
    (hf : Satisfied2FaithfulWide permOut hash (v3OfFrozenWide d (sitesFit_admitted (graduableWide_spec (graduableWide_rotateV3FrozenAuthority hgrad)).2.1)) minit mfin maddrs t) :
    ∀ i, i < t.rows.length →
      satisfiedVm hash d (envAt t i) (i == 0) (i + 1 == t.rows.length) := by
  intro i hi
  exact rotateV3FrozenAuthority_satisfiedVm_v1 hash d _ _ _
    (satisfied2FaithfulWide_satisfiedVm permOut hash (rotateV3FrozenAuthority d) minit mfin maddrs
      t (graduableWide_rotateV3FrozenAuthority hgrad) hf i hi)

#assert_axioms graduableWide_rotateV3
#assert_axioms graduableWide_rotateV3FrozenAuthority
#assert_axioms rotV3FrozenWide_sound_v1

/-! ### The FEE-PINNED wide rotation lift (the §11.8 fee availability face reaches the tower).

`transferFeeV3` composes `graduateV1 (rotateV3WithFeePin (rotateV3FrozenAuthority ·))`; the
hardened fee face (`EffectVmEmitTransfer.transferFeeVmDescriptorAvail`, 15-bit teeth) needs the
SAME composition at the WIDE graduation. The fee pin is one appended `.piBinding` constraint
(sites/ranges verbatim), so both the graduability lift and the per-row v1 peel are structural. -/

/-- The fee pin is a CONSTRAINT; `graduableWide` reads only sites/ranges (the wide mirror of
`graduable_rotateV3WithNullifierPin`, at the fee pin). -/
theorem graduableWide_rotateV3WithFeePin {base : EffectVmDescriptor}
    (h : graduableWide base = true) : graduableWide (rotateV3WithFeePin base) = true := by
  unfold rotateV3WithFeePin
  unfold graduableWide at h ⊢
  simpa using h

/-- The fee-pinned constraints are the base's plus the one appended pin. -/
theorem rotateV3WithFeePin_constraints (base : EffectVmDescriptor) :
    (rotateV3WithFeePin base).constraints
      = base.constraints ++ [.piBinding .last FEE_COL ROT_FEE_PI] := rfl

/-- The per-row v1 denotation peels through the fee pin (constraints-prefix; sites/ranges
verbatim). -/
theorem rotateV3WithFeePin_satisfiedVm (hash : List ℤ → ℤ) (base : EffectVmDescriptor)
    (env : VmRowEnv) (isFirst isLast : Bool)
    (h : satisfiedVm hash (rotateV3WithFeePin base) env isFirst isLast) :
    satisfiedVm hash base env isFirst isLast := by
  obtain ⟨hc, hsites, hr⟩ := h
  exact ⟨fun c hc' => hc c (by
      rw [rotateV3WithFeePin_constraints]; exact List.mem_append_left _ hc'),
    hsites, hr⟩

/-- **`v3OfFrozenFeeWide d`** — the WIDE graduated FEE-PINNED rotated descriptor of a hardened fee
member: `transferFeeV3`'s composition (freeze → fee pin → graduation) at the multi-width
graduation, so the 15-bit borrow/carry teeth of the §11.8 fee availability weld lower into the
15-bit table. -/
def v3OfFrozenFeeWide (d : EffectVmDescriptor)
    (hAdm : ∀ s ∈ (rotateV3WithFeePin (rotateV3FrozenAuthority d)).hashSites,
        ChipArityAdmitted s.inputs.length := by graduate_arity) : EffectVmDescriptor2 :=
  graduateV1Wide (rotateV3WithFeePin (rotateV3FrozenAuthority d)) hAdm

/-- **`rotV3FrozenFeeWide_sound_v1`** — a `Satisfied2FaithfulWide` witness of the wide fee-pinned
frozen graduation yields the full v1 denotation of the original descriptor on every row (the
fee-pinned mirror of `rotV3FrozenWide_sound_v1`). This is the bridge that lets a rotated witness
over the hardened FEE availability descriptor reach
`EffectVmEmitTransfer.transferFeeAvail_derives_availability_row`. -/
theorem rotV3FrozenFeeWide_sound_v1 (permOut : List ℤ → List ℤ) (hash : List ℤ → ℤ)
    (d : EffectVmDescriptor)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hgrad : graduableWide d = true)
    (hf : Satisfied2FaithfulWide permOut hash (v3OfFrozenFeeWide d (sitesFit_admitted (graduableWide_spec (graduableWide_rotateV3WithFeePin
      (graduableWide_rotateV3FrozenAuthority hgrad))).2.1)) minit mfin maddrs t) :
    ∀ i, i < t.rows.length →
      satisfiedVm hash d (envAt t i) (i == 0) (i + 1 == t.rows.length) := by
  intro i hi
  have hg : graduableWide (rotateV3WithFeePin (rotateV3FrozenAuthority d)) = true :=
    graduableWide_rotateV3WithFeePin (graduableWide_rotateV3FrozenAuthority hgrad)
  exact rotateV3FrozenAuthority_satisfiedVm_v1 hash d _ _ _
    (rotateV3WithFeePin_satisfiedVm hash _ _ _ _
      (satisfied2FaithfulWide_satisfiedVm permOut hash _ minit mfin maddrs t hg hf i hi))

-- The hardened fee face is wide-graduable and its fee-pinned frozen rotation keeps the
-- `transferFeeV3` PI shape (46 + the fee pin = 47).
#guard graduableWide EffectVmEmitTransfer.transferFeeVmDescriptorAvail
#guard graduableWide
  (rotateV3WithFeePin (rotateV3FrozenAuthority EffectVmEmitTransfer.transferFeeVmDescriptorAvail))
#guard (rotateV3WithFeePin (rotateV3FrozenAuthority
  EffectVmEmitTransfer.transferFeeVmDescriptorAvail)).piCount == 40

#assert_axioms graduableWide_rotateV3WithFeePin
#assert_axioms rotateV3WithFeePin_satisfiedVm
#assert_axioms rotV3FrozenFeeWide_sound_v1

end Dregg2.Circuit.Emit.EffectVmEmitRotationV3
