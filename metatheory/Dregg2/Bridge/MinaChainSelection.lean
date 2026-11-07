/-
# Dregg2.Bridge.MinaChainSelection — Ouroboros Samasika CHAIN SELECTION, in Lean.

⚑ **SUBSTRATE, SAID OUT LOUD.** This file authors **NO AIR**. Samasika chain selection is an
**OFF-CIRCUIT DECISION PROCEDURE**: it is what a node runs on two already-valid candidate tips to
pick one, and Mina itself never proves it in a SNARK (the in-circuit half of the density machinery
is `Min_window_density.Checked.update_min_window_density`, which computes a *block's own* density
during block production — a different function from the pairwise `select` this file implements).
So this is pure `Nat`/`Bool` Lean, exactly as `LightClientMina` / `LightClientSolana` are. Nothing
here is a `Builder` gadget and nothing here belongs in Rust. If a future lane wants selection
IN-CIRCUIT (e.g. a recursive proof that a tip is canonical), that object is a Lean-authored
`def`-generator + forcing lemmas — House Law #1 — and it does not exist yet.

## What this closes

`LightClientMina`'s header says, verbatim: "**FORK CHOICE IS NOT CHECKED.** Samasika's chain
selection appears nowhere in this file or anywhere else in the tree." That was true. This file is
the missing piece: a `select` that decides which of two tips is canonical, matched line-by-line
against the canonical implementation, with the structural facts about it PROVED rather than assumed.

## SOURCES — every rule below is cited to a line of a real implementation

Canonical (the OCaml daemon), `~/dev/mina` @ the working checkout:

| object | file:line |
|---|---|
| `select` (the top-level rule) | `src/lib/consensus/proof_of_stake.ml:2971-3078` |
| `is_short_range` | `src/lib/consensus/proof_of_stake.ml:2951-2967` |
| `Min_window_density.update_min_window_density` | `src/lib/consensus/proof_of_stake.ml:1221-1335` |
| `virtual_min_window_density` (inside `select`) | `src/lib/consensus/proof_of_stake.ml:3044-3063` |
| `Slot.in_seed_update_range` | `src/lib/consensus/slot.ml:9-13` |
| `Global_slot.epoch` / `Global_slot.slot` | `src/lib/consensus/global_slot.ml:77-83` |
| `Global_sub_window.of_global_slot` / `.sub_window` | `src/lib/consensus/global_sub_window.ml:10-18` |
| `Constants.create` (`grace_period_end`) | `src/lib/consensus/constants.ml:239-241` |
| `epoch_count` update (`+1` per transition) | `src/lib/consensus/proof_of_stake.ml:1129-1148` |

Second rendering (openmina / `mina-rust`, `crates/core/src/consensus.rs`): `is_short_range_fork:45`,
`relative_min_window_density:77`, `short_range_fork_take:126`, `long_range_fork_take:154`,
`consensus_take:190`. Spec document: `~/dev/mina/docs/specs/consensus/README.md` §5.2, §5.3.2,
§5.4.9, §5.4.12.

**Where the two disagree, this file follows the OCaml** — it is what mainnet runs and what the
in-circuit density update is checked against. The disagreements are not glossed: they are §8, and
they are proved, not asserted.

## CONSTANTS — real values, cited, never invented

All from `~/dev/mina/src/config/mainnet.mlh:15-20` (byte-identical in `devnet.mlh:15-20`):

| constant | value | line |
|---|---|---|
| `k` (depth of finality) | 290 | `mainnet.mlh:15` |
| `delta` | 0 | `mainnet.mlh:16` |
| `slots_per_epoch` | 7140 | `mainnet.mlh:17` |
| `slots_per_sub_window` | 7 | `mainnet.mlh:18` |
| `sub_windows_per_window` | 11 | `mainnet.mlh:19` |
| `grace_period_slots` | 2160 | `mainnet.mlh:20` |
| `slots_per_window` (derived) | 77 = 7·11 | `constants.ml:227` |
| `grace_period_end` (derived) | **2237** = 2160 + 77 | `constants.ml:239` |

⚑ The spec document's constants table (`README.md:96-113`) says `grace_period_end = 1440`, and
openmina hardcodes `const GRACE_PERIOD_END: u32 = 1440` (`consensus.rs:15`, with a `// TODO get
constants from elsewhere`). Both are **stale**: the daemon computes 2237. §8 turns that into a
theorem rather than a remark.

## SCOPE, honestly

Selection assumes the candidate tips are **already valid** — that their blocks verify, that their
VRF leader elections are legitimate, that the densities in them were honestly produced. None of
that is here (a sibling lane has VRF/stake). Samasika's own spec says this in as many words
(`README.md:918-922`): an implementation MUST reject invalid blocks and MUST NOT accept blocks for
future slots, or the sliding window is attackable. `select` is the tie-break AFTER those checks,
not a substitute for them.
-/
import Dregg2.Tactics

set_option autoImplicit false
set_option maxRecDepth 40000

namespace Dregg2.Bridge.MinaChainSelection

/-! ## §1 — Consensus constants. -/

/-- Mina's consensus constants, the subset chain selection reads.
`slotsPerWindow` and `gracePeriodEnd` are DERIVED exactly as `Constants.create` derives them
(`constants.ml:227,239`) so a caller cannot pass an inconsistent pair. -/
structure Constants where
  /-- Depth of finality (`mainnet.mlh:15`). Not read by `select`; carried because the light client
  is stated in terms of it. -/
  k : Nat
  /-- Maximum permissible packet delay in slots (`mainnet.mlh:16`). Not read by `select`. -/
  delta : Nat
  /-- `slots_per_epoch` (`mainnet.mlh:17`). Read by `in_seed_update_range`. -/
  slotsPerEpoch : Nat
  /-- `slots_per_sub_window` (`mainnet.mlh:18`). -/
  slotsPerSubWindow : Nat
  /-- `sub_windows_per_window` (`mainnet.mlh:19`). -/
  subWindowsPerWindow : Nat
  /-- `grace_period_slots` (`mainnet.mlh:20`). -/
  gracePeriodSlots : Nat

/-- `slots_per_window = slots_per_sub_window * sub_windows_per_window` (`constants.ml:227`). -/
def Constants.slotsPerWindow (C : Constants) : Nat := C.slotsPerSubWindow * C.subWindowsPerWindow

/-- `grace_period_end = grace_period_slots + slots_per_window` (`constants.ml:239-241`).
On mainnet this is `2160 + 77 = 2237`, NOT the `1440` in the spec table or in openmina. -/
def Constants.gracePeriodEnd (C : Constants) : Nat := C.gracePeriodSlots + C.slotsPerWindow

/-- The real mainnet / devnet constants. -/
def mainnet : Constants :=
  { k := 290, delta := 0, slotsPerEpoch := 7140, slotsPerSubWindow := 7,
    subWindowsPerWindow := 11, gracePeriodSlots := 2160 }

/-- The derived values are the real ones. -/
theorem mainnet_slotsPerWindow : mainnet.slotsPerWindow = 77 := by decide
theorem mainnet_gracePeriodEnd : mainnet.gracePeriodEnd = 2237 := by decide

/-! ## §2 — `Consensus_state`, with the fields the real one has.

Mirrors `Consensus_state.Poly` (`proof_of_stake.ml:1740-1760`) and the wire shape a node actually
serves. The fields BELOW the `-- not read by select` line are present on purpose: §6's
`select_reads_only_eight_fields` proves they cannot influence the verdict, and among them is
`epochCount` — the field openmina keys `is_short_range_fork` on. -/

/-- A Mina consensus state, as chain selection sees it. Field elements (checkpoints, seeds, keys)
are their NUMERIC value in `[0, p)` — the ordering the OCaml `compare` on
`Snark_params.Tick.Field.t` uses, and the one openmina's `BigInt` (which stores
`field.into_bigint()`) derives. -/
structure ConsensusState where
  /-- `blockchain_length`. -/
  blockchainLength : Nat
  /-- `min_window_density`. -/
  minWindowDensity : Nat
  /-- `sub_window_densities`, `sub_windows_per_window` of them, oldest-relative-index-first. -/
  subWindowDensities : List Nat
  /-- `Blake2b(last_vrf_output)` as 32 bytes. BOTH implementations compare the DIGEST, not the raw
  output (`proof_of_stake.ml:3026-3031`; `consensus.rs:143`), so the digest is what we carry. -/
  lastVrfHash : List Nat
  /-- `curr_global_slot_since_hard_fork.slot_number`. -/
  currGlobalSlot : Nat
  /-- `curr_global_slot_since_hard_fork.slots_per_epoch`. ⚑ Carried ON THE VALUE, and
  `Global_slot.epoch` divides by THIS one (`global_slot.ml:79`), not by the constants' — an
  asymmetry openmina reproduces (`consensus.rs:47`) and this file therefore reproduces too. -/
  slotsPerEpoch : Nat
  /-- `staking_epoch_data.lock_checkpoint`. -/
  stakingLockCheckpoint : Nat
  /-- `next_epoch_data.lock_checkpoint`. -/
  nextLockCheckpoint : Nat
  -- ── everything below is in the real `Consensus_state` and is NOT read by `select` ──
  /-- `epoch_count`. ⚑ Incremented by ONE per epoch transition (`proof_of_stake.ml:1140`), so it
  LAGS `curr_global_slot / slots_per_epoch` permanently after any fully-empty epoch. openmina keys
  its short-range test on this field; the OCaml does not. -/
  epochCount : Nat
  /-- `total_currency`. -/
  totalCurrency : Nat
  /-- `global_slot_since_genesis`. -/
  globalSlotSinceGenesis : Nat
  /-- `staking_epoch_data.seed`. -/
  stakingSeed : Nat
  /-- `staking_epoch_data.start_checkpoint`. -/
  stakingStartCheckpoint : Nat
  /-- `staking_epoch_data.epoch_length`. -/
  stakingEpochLength : Nat
  /-- `staking_epoch_data.ledger.hash`. -/
  stakingLedgerHash : Nat
  /-- `next_epoch_data.seed`. -/
  nextSeed : Nat
  /-- `next_epoch_data.start_checkpoint`. -/
  nextStartCheckpoint : Nat
  /-- `next_epoch_data.epoch_length`. -/
  nextEpochLength : Nat
  /-- `next_epoch_data.ledger.hash`. -/
  nextLedgerHash : Nat
  /-- `has_ancestor_in_same_checkpoint_window`. -/
  hasAncestorInSameCheckpointWindow : Bool
  /-- `block_stake_winner`. -/
  blockStakeWinner : Nat
  /-- `block_creator`. -/
  blockCreator : Nat
  /-- `coinbase_receiver`. -/
  coinbaseReceiver : Nat
  /-- `supercharge_coinbase`. -/
  superchargeCoinbase : Bool
deriving Repr, DecidableEq

/-- Build a state from the eight selection-relevant fields; everything else zero. Used by the
counterexamples and the differential, so a reader can see at a glance that the non-selection
fields play no role. -/
def mkCS (blockchainLength minWindowDensity : Nat) (subWindowDensities lastVrfHash : List Nat)
    (currGlobalSlot slotsPerEpoch stakingLockCheckpoint nextLockCheckpoint : Nat) :
    ConsensusState :=
  { blockchainLength, minWindowDensity, subWindowDensities, lastVrfHash, currGlobalSlot,
    slotsPerEpoch, stakingLockCheckpoint, nextLockCheckpoint,
    epochCount := 0, totalCurrency := 0, globalSlotSinceGenesis := 0, stakingSeed := 0,
    stakingStartCheckpoint := 0, stakingEpochLength := 0, stakingLedgerHash := 0, nextSeed := 0,
    nextStartCheckpoint := 0, nextEpochLength := 0, nextLedgerHash := 0,
    hasAncestorInSameCheckpointWindow := false, blockStakeWinner := 0, blockCreator := 0,
    coinbaseReceiver := 0, superchargeCoinbase := false }

/-! ## §3 — Epoch/slot arithmetic and the SHORT-RANGE FORK CHECK. -/

/-- `Global_slot.epoch` (`global_slot.ml:77-79`) — divides by the VALUE's own `slots_per_epoch`. -/
def currEpoch (c : ConsensusState) : Nat := c.currGlobalSlot / c.slotsPerEpoch

/-- `Global_slot.slot` (`global_slot.ml:81-83`). -/
def currSlot (c : ConsensusState) : Nat := c.currGlobalSlot % c.slotsPerEpoch

/-- `Slot.in_seed_update_range` (`slot.ml:9-13`): the first 2/3 of an epoch, where the VRF seed is
still being updated. Divides the CONSTANTS' `slots_per_epoch` (the OCaml asserts it is a multiple
of 3). -/
def inSeedUpdateRange (C : Constants) (slot : Nat) : Bool :=
  decide (slot < (C.slotsPerEpoch / 3) * 2)

/-- `pred_case` from `is_short_range` (`proof_of_stake.ml:2954-2962`): `c1` is exactly ONE epoch
BEHIND `c2`, `c1`'s NEXT slot is past the seed-update range (so `c1`'s next-epoch lock checkpoint
is finalized), and `c1`'s next-epoch lock checkpoint IS `c2`'s staking-epoch lock checkpoint.

⚑ The `Slot.succ` is load-bearing and is the subtle part: the condition is
`not (in_seed_update_range (succ (curr_slot c1)))`, i.e. `curr_slot c1 ≥ 2/3·slots_per_epoch − 1`,
one slot EARLIER than a reading without the `succ`. openmina drops it (`consensus.rs:50` tests
`s2_epoch_slot >= slots_per_epoch * 2 / 3`), so the two implementations disagree on exactly the
boundary slot. -/
def predCase (C : Constants) (c1 c2 : ConsensusState) : Bool :=
  decide (currEpoch c1 + 1 = currEpoch c2)
    && !inSeedUpdateRange C (currSlot c1 + 1)
    && decide (c1.nextLockCheckpoint = c2.stakingLockCheckpoint)

/-- **`isShortRange`** (`proof_of_stake.ml:2963-2967`). Same epoch ⇒ compare the two states'
STAKING-epoch lock checkpoints; different epochs ⇒ the adjacent-epoch case, tried in BOTH
orientations. Note the same-epoch test is on `curr_epoch` (derived from the global slot), NOT on
`epoch_count`. -/
def isShortRange (C : Constants) (c1 c2 : ConsensusState) : Bool :=
  if currEpoch c1 = currEpoch c2 then
    decide (c1.stakingLockCheckpoint = c2.stakingLockCheckpoint)
  else predCase C c1 c2 || predCase C c2 c1

/-! ## §4 — The sliding-window density: `update_min_window_density` and the VIRTUAL (relative)
minimum window density the long-range rule compares. -/

/-- `Global_sub_window.of_global_slot` (`global_sub_window.ml:10-15`). -/
def globalSubWindow (C : Constants) (slot : Nat) : Nat := slot / C.slotsPerSubWindow

/-- `Global_sub_window.sub_window` (`global_sub_window.ml:17-18`) — the relative index into
`sub_window_densities`. -/
def relativeSubWindow (C : Constants) (gsw : Nat) : Nat := gsw % C.subWindowsPerWindow

/-- Map a list with its index (written out rather than depending on a core name whose argument
order has moved between toolchains). -/
def mapIdxFrom (i : Nat) (f : Nat → Nat → Nat) : List Nat → List Nat
  | [] => []
  | x :: xs => f i x :: mapIdxFrom (i + 1) f xs

/-- The projected ("current") window of `update_min_window_density`
(`proof_of_stake.ml:1286-1304`). If the two slots are in the SAME sub-window nothing changes; if
the windows OVERLAP, only the sub-windows strictly BETWEEN `prev` and `next` (in ring order) are
zeroed; otherwise the whole window is zeroed. -/
def projectedWindow (C : Constants) (prevGlobalSlot nextGlobalSlot : Nat)
    (prevSub : List Nat) : List Nat :=
  let prevGsw := globalSubWindow C prevGlobalSlot
  let nextGsw := globalSubWindow C nextGlobalSlot
  let prevRel := relativeSubWindow C prevGsw
  let nextRel := relativeSubWindow C nextGsw
  let same := prevGsw = nextGsw
  let overlapping := prevGsw + C.subWindowsPerWindow ≥ nextGsw
  mapIdxFrom 0 (fun i d =>
    let gtPrev := i > prevRel
    let ltNext := i < nextRel
    let within := if prevRel < nextRel then gtPrev && ltNext else gtPrev || ltNext
    if same then d else if overlapping && !within then d else 0) prevSub

/-- **`updateMinWindowDensity`** (`proof_of_stake.ml:1221-1335`), the density half. `select` calls
it with `~incr_window:false`, so only the density is needed here; the "next window" half is block
production and is not part of chain selection. -/
def updateMinWindowDensity (C : Constants) (prevGlobalSlot nextGlobalSlot : Nat)
    (prevSub : List Nat) (prevMin : Nat) : Nat :=
  let same := globalSubWindow C prevGlobalSlot = globalSubWindow C nextGlobalSlot
  let cur := (projectedWindow C prevGlobalSlot nextGlobalSlot prevSub).foldl (· + ·) 0
  if same || nextGlobalSlot < C.gracePeriodEnd then prevMin else min cur prevMin

/-- **`virtualMinWindowDensity`** — `select`'s `virtual_min_window_density`
(`proof_of_stake.ml:3048-3059`): the min window density this chain WOULD have if extended, with no
intervening blocks, to `maxSlot` (the later of the two chains' slots). This projection is what
makes the long-range rule usable by a peer that has been offline: without it a stale chain's
monotonically-decreasing `min_window_density` could beat the network's (spec §5.4.12). -/
def virtualMinWindowDensity (C : Constants) (s : ConsensusState) (maxSlot : Nat) : Nat :=
  if s.currGlobalSlot = maxSlot then s.minWindowDensity
  else updateMinWindowDensity C s.currGlobalSlot maxSlot s.subWindowDensities s.minWindowDensity

/-! ## §5 — THE RULE: `select`. -/

/-- Byte-lexicographic strict less-than — OCaml's `String.compare` on two raw Blake2b digests
(`proof_of_stake.ml:3029-3031`), and openmina's `Vec<u8>` `Ord` (`consensus.rs:145`). -/
def lexLt : List Nat → List Nat → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as', b :: bs' => if a < b then true else if b < a then false else lexLt as' bs'

/-- The FINAL tie-break: the candidate's state hash is numerically greater
(`proof_of_stake.ml:3022-3023`). ⚑ This is a comparison of the state hash AS A FIELD ELEMENT — the
derived `compare` on `Snark_params.Tick.Field.t`, which orders by the canonical value in `[0, p)`.
It is NOT a byte-lexicographic compare of the 32-byte little-endian encoding, and it is NOT the
Base58Check string order. openmina agrees: its `StateHash` derefs to a `BigInt` holding
`field.into_bigint()`. -/
def candidateHashBigger (existingHash candidateHash : Nat) : Bool :=
  decide (existingHash < candidateHash)

/-- `candidate_vrf_is_bigger` (`proof_of_stake.ml:3025-3035`): the candidate's VRF digest is
lexicographically greater, ties broken by the state hash. -/
def candidateVrfBigger (e c : ConsensusState) (eh ch : Nat) : Bool :=
  lexLt e.lastVrfHash c.lastVrfHash
    || (decide (e.lastVrfHash = c.lastVrfHash) && candidateHashBigger eh ch)

/-- `blockchain_length_is_longer` (`proof_of_stake.ml:3036-3040`) — THE SHORT-RANGE RULE: longest
chain, ties broken by VRF then by state hash. -/
def blockchainLengthLonger (e c : ConsensusState) (eh ch : Nat) : Bool :=
  decide (e.blockchainLength < c.blockchainLength)
    || (decide (e.blockchainLength = c.blockchainLength) && candidateVrfBigger e c eh ch)

/-- The later of the two chains' global slots — the slot both windows are projected to
(`proof_of_stake.ml:3044-3046`). -/
def maxSlot (e c : ConsensusState) : Nat := max c.currGlobalSlot e.currGlobalSlot

/-- `long_fork_chain_quality_is_better` (`proof_of_stake.ml:3041-3063`) — THE LONG-RANGE RULE:
greater RELATIVE minimum window density, ties broken by the whole short-range chain. -/
def longForkQualityBetter (C : Constants) (e c : ConsensusState) (eh ch : Nat) : Bool :=
  let m := maxSlot e c
  let de := virtualMinWindowDensity C e m
  let dc := virtualMinWindowDensity C c m
  decide (de < dc) || (decide (de = dc) && blockchainLengthLonger e c eh ch)

/-- `select`'s two statuses (`proof_of_stake.ml:2969`). -/
inductive SelectStatus where
  | keep : SelectStatus
  | take : SelectStatus
deriving Repr, DecidableEq

/-- **`select`** (`proof_of_stake.ml:2971-3078`). `Take` means: adopt the CANDIDATE. -/
def select (C : Constants) (e c : ConsensusState) (eh ch : Nat) : SelectStatus :=
  if isShortRange C e c then
    (if blockchainLengthLonger e c eh ch then SelectStatus.take else SelectStatus.keep)
  else
    (if longForkQualityBetter C e c eh ch then SelectStatus.take else SelectStatus.keep)

/-- `beats c e` — "candidate `c` (hash `ch`) is selected over existing `e` (hash `eh`)". The
relation the structural theorems below are about. -/
def beats (C : Constants) (c e : ConsensusState) (ch eh : Nat) : Prop :=
  select C e c eh ch = SelectStatus.take

instance (C : Constants) (c e : ConsensusState) (ch eh : Nat) :
    Decidable (beats C c e ch eh) := by unfold beats; infer_instance

/-! ## §6 — WHAT THE RULE IS. Determinism, irreflexivity, asymmetry, and where ties can occur. -/

section Lex

/-- `lexLt` is irreflexive. -/
theorem lexLt_irrefl : ∀ x : List Nat, lexLt x x = false := by
  intro x; induction x with
  | nil => rfl
  | cons a as ih => simp [lexLt, ih]

/-- A strict `lexLt` rules out equality. -/
theorem lexLt_ne : ∀ x y : List Nat, lexLt x y = true → x ≠ y := by
  intro x y h he; subst he; rw [lexLt_irrefl] at h; exact Bool.noConfusion h

/-- `lexLt` is asymmetric. -/
theorem lexLt_asymm : ∀ x y : List Nat, lexLt x y = true → lexLt y x = false := by
  intro x; induction x with
  | nil => intro y _; cases y with
    | nil => rfl
    | cons _ _ => rfl
  | cons a as ih =>
    intro y h; cases y with
    | nil => simp [lexLt] at h
    | cons b bs =>
      simp only [lexLt] at h ⊢
      by_cases hab : a < b
      · simp only [hab, if_true] at h
        have : ¬ b < a := by omega
        simp [this, hab]
      · simp only [hab, if_false] at h
        by_cases hba : b < a
        · simp [hba] at h
        · simp only [hba, if_false] at h
          simp [hab, hba, ih bs h]

/-- `lexLt` is transitive. -/
theorem lexLt_trans : ∀ x y z : List Nat, lexLt x y = true → lexLt y z = true → lexLt x z = true := by
  intro x; induction x with
  | nil =>
    intro y z _ hyz; cases z with
    | nil => cases y with
      | nil => exact absurd hyz (by simp [lexLt])
      | cons _ _ => exact absurd hyz (by simp [lexLt])
    | cons _ _ => rfl
  | cons a as ih =>
    intro y z hxy hyz
    cases y with
    | nil => simp [lexLt] at hxy
    | cons b bs =>
      cases z with
      | nil => simp [lexLt] at hyz
      | cons c cs =>
        simp only [lexLt] at hxy hyz ⊢
        by_cases hab : a < b
        · simp only [hab, if_true] at hxy
          by_cases hbc : b < c
          · have : a < c := by omega
            simp [this]
          · simp only [hbc, if_false] at hyz
            by_cases hcb : c < b
            · simp [hcb] at hyz
            · have hbc' : b = c := by omega
              subst hbc'; simp [hab]
        · simp only [hab, if_false] at hxy
          by_cases hba : b < a
          · simp [hba] at hxy
          · have hab' : a = b := by omega
            subst hab'
            rw [if_neg (Nat.lt_irrefl a)] at hxy
            by_cases hac : a < c
            · simp [hac]
            · simp only [hac, if_false] at hyz ⊢
              by_cases hca : c < a
              · simp [hca] at hyz
              · simp only [hca, if_false] at hyz ⊢
                exact ih bs cs hxy hyz

/-- If neither is strictly less, they are equal. -/
theorem lexLt_total : ∀ x y : List Nat, lexLt x y = false → lexLt y x = false → x = y := by
  intro x; induction x with
  | nil => intro y h _; cases y with
    | nil => rfl
    | cons _ _ => simp [lexLt] at h
  | cons a as ih =>
    intro y h h'; cases y with
    | nil => simp [lexLt] at h'
    | cons b bs =>
      simp only [lexLt] at h h'
      by_cases hab : a < b
      · simp [hab] at h
      · simp only [hab, if_false] at h
        by_cases hba : b < a
        · simp [hba] at h'
        · simp only [hba, if_false] at h h'
          have hab' : a = b := by omega
          subst hab'
          rw [if_neg (Nat.lt_irrefl a)] at h'
          exact congrArg _ (ih bs h h')

end Lex

/-- **`isShortRange` is SYMMETRIC.** Needed for everything below: `select existing candidate` and
`select candidate existing` must take the SAME branch, or the rule could contradict itself simply
by being asked in the other order. -/
theorem isShortRange_symm (C : Constants) (a b : ConsensusState) :
    isShortRange C a b = isShortRange C b a := by
  unfold isShortRange
  by_cases h : currEpoch a = currEpoch b
  · rw [if_pos h, if_pos h.symm]
    exact decide_eq_decide.mpr ⟨Eq.symm, Eq.symm⟩
  · rw [if_neg h, if_neg (fun hh => h hh.symm), Bool.or_comm]

/-- `isShortRange` is REFLEXIVE — a chain never long-range-forks itself. -/
theorem isShortRange_refl (C : Constants) (a : ConsensusState) : isShortRange C a a = true := by
  unfold isShortRange; simp

/-- `maxSlot` is symmetric, so the two chains are projected to the SAME slot in either order. -/
theorem maxSlot_symm (e c : ConsensusState) : maxSlot e c = maxSlot c e := by
  unfold maxSlot; omega

/-- The SELECTION KEY: the state rebuilt from the eight fields `select` reads, everything else
zeroed. -/
def selKey (s : ConsensusState) : ConsensusState :=
  mkCS s.blockchainLength s.minWindowDensity s.subWindowDensities s.lastVrfHash s.currGlobalSlot
    s.slotsPerEpoch s.stakingLockCheckpoint s.nextLockCheckpoint

/-- **DETERMINISM, the version with content (I): `select` FACTORS THROUGH the eight-field key.**

⚑ This is `rfl` — and that is the whole point. It typechecks definitionally exactly BECAUSE no
other field is ever projected: replace all seventeen remaining fields by zeros and the verdict is
the same term. If `select` read `epochCount` (as openmina's does), `rfl` would fail. -/
theorem select_factors_through_selKey (C : Constants) (e c : ConsensusState) (eh ch : Nat) :
    select C e c eh ch = select C (selKey e) (selKey c) eh ch := rfl

/-- **DETERMINISM, the version with content (II): `select` reads exactly EIGHT fields.**

`select` is a `def`, so "the same pair always selects the same chain" is definitional. The
non-trivial statement — the one a light client actually needs — is that the verdict is a function
of the eight fields named here and of NOTHING ELSE the state carries. In particular it does not
depend on `epochCount` (which openmina keys its short-range test on), nor on `totalCurrency`,
seeds, start checkpoints, epoch lengths, the block producer, or the supercharge flag. A verifier
that reconstructs only these eight fields reproduces the daemon's verdict exactly. -/
theorem select_reads_only_eight_fields (C : Constants) (e c e' c' : ConsensusState) (eh ch : Nat)
    (he1 : e.blockchainLength = e'.blockchainLength)
    (he2 : e.minWindowDensity = e'.minWindowDensity)
    (he3 : e.subWindowDensities = e'.subWindowDensities)
    (he4 : e.lastVrfHash = e'.lastVrfHash)
    (he5 : e.currGlobalSlot = e'.currGlobalSlot)
    (he6 : e.slotsPerEpoch = e'.slotsPerEpoch)
    (he7 : e.stakingLockCheckpoint = e'.stakingLockCheckpoint)
    (he8 : e.nextLockCheckpoint = e'.nextLockCheckpoint)
    (hc1 : c.blockchainLength = c'.blockchainLength)
    (hc2 : c.minWindowDensity = c'.minWindowDensity)
    (hc3 : c.subWindowDensities = c'.subWindowDensities)
    (hc4 : c.lastVrfHash = c'.lastVrfHash)
    (hc5 : c.currGlobalSlot = c'.currGlobalSlot)
    (hc6 : c.slotsPerEpoch = c'.slotsPerEpoch)
    (hc7 : c.stakingLockCheckpoint = c'.stakingLockCheckpoint)
    (hc8 : c.nextLockCheckpoint = c'.nextLockCheckpoint) :
    select C e c eh ch = select C e' c' eh ch := by
  rw [select_factors_through_selKey C e c, select_factors_through_selKey C e' c']
  have ke : selKey e = selKey e' := by
    simp only [selKey, mkCS, he1, he2, he3, he4, he5, he6, he7, he8]
  have kc : selKey c = selKey c' := by
    simp only [selKey, mkCS, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8]
  rw [ke, kc]

/-- The tie-break chain is irreflexive: a chain never beats itself on length/VRF/hash. -/
theorem blockchainLengthLonger_irrefl (s : ConsensusState) (h : Nat) :
    blockchainLengthLonger s s h h = false := by
  simp [blockchainLengthLonger, candidateVrfBigger, candidateHashBigger, lexLt_irrefl]

/-- **IRREFLEXIVITY.** A chain is never selected over itself — so a light client fed the same tip
twice does not flap. (`is_short_range` is reflexive, so this lands in the short branch.) -/
theorem select_irrefl (C : Constants) (s : ConsensusState) (h : Nat) :
    select C s s h h = SelectStatus.keep := by
  unfold select
  rw [if_pos (by simpa using isShortRange_refl C s), blockchainLengthLonger_irrefl]
  rfl

/-- The tie-break chain is asymmetric. -/
theorem blockchainLengthLonger_asymm (e c : ConsensusState) (eh ch : Nat)
    (h : blockchainLengthLonger e c eh ch = true) : blockchainLengthLonger c e ch eh = false := by
  by_contra hcon
  have h2 : blockchainLengthLonger c e ch eh = true := by
    cases hx : blockchainLengthLonger c e ch eh
    · exact absurd hx hcon
    · rfl
  simp only [blockchainLengthLonger, candidateVrfBigger, candidateHashBigger, Bool.or_eq_true,
    Bool.and_eq_true, decide_eq_true_eq] at h h2
  rcases h with l1 | ⟨q1, v1⟩ <;> rcases h2 with l2 | ⟨q2, v2⟩
  · omega
  · omega
  · omega
  · rcases v1 with w1 | ⟨u1, s1⟩ <;> rcases v2 with w2 | ⟨u2, s2⟩
    · rw [lexLt_asymm _ _ w1] at w2; exact Bool.noConfusion w2
    · rw [u2, lexLt_irrefl] at w1; exact Bool.noConfusion w1
    · rw [u1, lexLt_irrefl] at w2; exact Bool.noConfusion w2
    · omega

/-- **ASYMMETRY — NO TWO-CYCLE.** `select` never takes in BOTH directions. This is precisely the
invariant the OCaml only QUICKCHECKS ("selection invariant: candidate selections are not
commutative", `proof_of_stake.ml:4617-4630`); here it is proved for all inputs. A light client that
can prefer `A` over `B` and `B` over `A` is not a light client. -/
theorem select_asymm (C : Constants) (e c : ConsensusState) (eh ch : Nat)
    (h : select C e c eh ch = SelectStatus.take) :
    select C c e ch eh = SelectStatus.keep := by
  unfold select at h ⊢
  rw [← isShortRange_symm C e c]
  by_cases hs : isShortRange C e c = true
  · rw [if_pos hs] at h ⊢
    by_cases hb : blockchainLengthLonger e c eh ch = true
    · rw [if_neg (by simp [blockchainLengthLonger_asymm e c eh ch hb])]
    · rw [if_neg (by simpa using hb)] at h; exact absurd h (by simp)
  · rw [if_neg hs] at h ⊢
    by_cases hq : longForkQualityBetter C e c eh ch = true
    · refine if_neg ?_
      simp only [longForkQualityBetter, maxSlot_symm c e, Bool.or_eq_true, Bool.and_eq_true,
        decide_eq_true_eq] at hq ⊢
      intro hcon
      rcases hq with h1 | ⟨h1, h2⟩
      · rcases hcon with h3 | ⟨h3, _⟩ <;> omega
      · rcases hcon with h3 | ⟨_, h4⟩
        · omega
        · rw [blockchainLengthLonger_asymm e c eh ch h2] at h4; exact Bool.noConfusion h4
    · rw [if_neg (by simpa using hq)] at h; exact absurd h (by simp)

/-- **WHERE TIES LIVE.** If neither chain is selected over the other, then their lengths, their VRF
digests AND their state hashes are all equal — in BOTH branches, since a density tie falls through
to exactly the same chain. So `select` never "declines to decide" between two genuinely different
tips: a `Keep`/`Keep` pair is a pair a light client cannot distinguish by any input the rule reads.
Together with `select_asymm` this is the trichotomy: for any pair, exactly one of
{take, take-the-other, all-keys-equal}. -/
theorem select_ties_only_on_equal_keys (C : Constants) (e c : ConsensusState) (eh ch : Nat)
    (h1 : select C e c eh ch = SelectStatus.keep)
    (h2 : select C c e ch eh = SelectStatus.keep) :
    e.blockchainLength = c.blockchainLength ∧ e.lastVrfHash = c.lastVrfHash ∧ eh = ch := by
  have key : ∀ (x y : ConsensusState) (xh yh : Nat),
      blockchainLengthLonger x y xh yh = false → blockchainLengthLonger y x yh xh = false →
      x.blockchainLength = y.blockchainLength ∧ x.lastVrfHash = y.lastVrfHash ∧ xh = yh := by
    intro x y xh yh hx hy
    simp only [blockchainLengthLonger, candidateVrfBigger, candidateHashBigger, Bool.or_eq_false_iff,
      Bool.and_eq_false_iff, decide_eq_false_iff_not, Bool.not_eq_true'] at hx hy
    obtain ⟨hx1, hx2⟩ := hx
    obtain ⟨hy1, hy2⟩ := hy
    have hlen : x.blockchainLength = y.blockchainLength := by omega
    have hx2' := hx2.resolve_left (by simp [hlen])
    have hy2' := hy2.resolve_left (by simp [hlen.symm])
    obtain ⟨hxv, hxh⟩ := hx2'
    obtain ⟨hyv, hyh⟩ := hy2'
    have hvrf : x.lastVrfHash = y.lastVrfHash := lexLt_total _ _ hxv hyv
    have hxh' := hxh.resolve_left (by simp [hvrf])
    have hyh' := hyh.resolve_left (by simp [hvrf.symm])
    exact ⟨hlen, hvrf, by omega⟩
  unfold select at h1 h2
  rw [← isShortRange_symm C e c] at h2
  by_cases hs : isShortRange C e c = true
  · rw [if_pos hs] at h1 h2
    have hb1 : blockchainLengthLonger e c eh ch = false := by
      by_cases hb : blockchainLengthLonger e c eh ch = true
      · rw [if_pos hb] at h1; exact absurd h1 (by simp)
      · simpa using hb
    have hb2 : blockchainLengthLonger c e ch eh = false := by
      by_cases hb : blockchainLengthLonger c e ch eh = true
      · rw [if_pos hb] at h2; exact absurd h2 (by simp)
      · simpa using hb
    exact key e c eh ch hb1 hb2
  · rw [if_neg hs] at h1 h2
    have hq1 : longForkQualityBetter C e c eh ch = false := by
      by_cases hq : longForkQualityBetter C e c eh ch = true
      · rw [if_pos hq] at h1; exact absurd h1 (by simp)
      · simpa using hq
    have hq2 : longForkQualityBetter C c e ch eh = false := by
      by_cases hq : longForkQualityBetter C c e ch eh = true
      · rw [if_pos hq] at h2; exact absurd h2 (by simp)
      · simpa using hq
    simp only [longForkQualityBetter, maxSlot_symm c e, Bool.or_eq_false_iff,
      Bool.and_eq_false_iff, decide_eq_false_iff_not] at hq1 hq2
    obtain ⟨d1, t1⟩ := hq1
    obtain ⟨d2, t2⟩ := hq2
    have hd : virtualMinWindowDensity C e (maxSlot e c) = virtualMinWindowDensity C c (maxSlot e c) := by
      omega
    exact key e c eh ch (by simpa using t1.resolve_left (by simp [hd]))
      (by simpa using t2.resolve_left (by simp [hd.symm]))

/-- The short-range tie-break chain is TRANSITIVE (it is a lexicographic order on
`(blockchain_length, Blake2b(vrf), state_hash)`). -/
theorem blockchainLengthLonger_trans (a b c : ConsensusState) (ha hb hc : Nat)
    (h1 : blockchainLengthLonger a b ha hb = true)
    (h2 : blockchainLengthLonger b c hb hc = true) :
    blockchainLengthLonger a c ha hc = true := by
  simp only [blockchainLengthLonger, candidateVrfBigger, candidateHashBigger, Bool.or_eq_true,
    Bool.and_eq_true, decide_eq_true_eq] at h1 h2 ⊢
  rcases h1 with l1 | ⟨e1, v1⟩
  · rcases h2 with l2 | ⟨e2, _⟩
    · exact Or.inl (by omega)
    · exact Or.inl (by omega)
  · rcases h2 with l2 | ⟨e2, v2⟩
    · exact Or.inl (by omega)
    · refine Or.inr ⟨by omega, ?_⟩
      rcases v1 with w1 | ⟨q1, s1⟩
      · rcases v2 with w2 | ⟨q2, _⟩
        · exact Or.inl (lexLt_trans _ _ _ w1 w2)
        · exact Or.inl (q2 ▸ w1)
      · rcases v2 with w2 | ⟨q2, s2⟩
        · exact Or.inl (q1 ▸ w2)
        · exact Or.inr ⟨q1.trans q2, by omega⟩

/-- **TRANSITIVITY, WHERE IT HOLDS.** Restricted to a set of tips that are pairwise SHORT-RANGE,
`beats` is a strict total order (longest chain, then VRF, then state hash) and is transitive. This
is the regime Samasika is designed for — inside one epoch behind a shared lock checkpoint — and it
is the regime the OCaml's own quickcheck for transitivity generates. §7 shows it is the ONLY
regime. -/
theorem beats_trans_short_range (C : Constants) (a b c : ConsensusState) (ha hb hc : Nat)
    (sab : isShortRange C a b = true) (sbc : isShortRange C b c = true)
    (sac : isShortRange C a c = true)
    (h1 : beats C b a hb ha) (h2 : beats C c b hc hb) : beats C c a hc ha := by
  unfold beats select at h1 h2 ⊢
  rw [if_pos sab] at h1
  rw [if_pos sbc] at h2
  rw [if_pos sac]
  have hb1 : blockchainLengthLonger a b ha hb = true := by
    by_cases x : blockchainLengthLonger a b ha hb = true
    · exact x
    · rw [if_neg (by simpa using x)] at h1; exact absurd h1 (by simp)
  have hb2 : blockchainLengthLonger b c hb hc = true := by
    by_cases x : blockchainLengthLonger b c hb hc = true
    · exact x
    · rw [if_neg (by simpa using x)] at h2; exact absurd h2 (by simp)
  rw [if_pos (blockchainLengthLonger_trans a b c ha hb hc hb1 hb2)]

/-! ## §7 — ⚑ WHAT THE RULE IS **NOT**: `select` IS NOT A TOTAL ORDER. IT HAS 3-CYCLES.

This is the genuinely interesting structural fact about Samasika, and misreporting it would be
worse than not proving it. `select` is **irreflexive, asymmetric and total-up-to-key-equality**
(§6) — a *tournament*. It is **NOT transitive**, and not merely by an edge case: there are triples
of consensus states `A, B, C` with `B` selected over `A`, `C` over `B`, and `A` over `C`.

TWO independent mechanisms produce it, and BOTH are exhibited below as `decide`-checked witnesses:

  1. **MIXED REGIME.** `is_short_range` is not transitive (it is not even an equivalence across
     epochs), so different PAIRS are judged by different rules — `A ~ B` and `B ~ C` short-range
     while `A ~ C` is long-range. Realistic: `A` and `B` sit in the same epoch behind the same
     staking checkpoint, but only `B`'s next-epoch checkpoint got locked to `C`'s.

  2. **LONG REGIME ALONE.** Even when all three pairs are long-range, the "relative minimum window
     density" of a chain is NOT AN INTRINSIC SCALAR — it is a function of the PAIR, through
     `max_slot`. A chain's density is one number when it is the leading chain and a much smaller
     number when it is projected forward to a rival's later slot. So the comparison key itself
     changes per comparison, and a cycle costs nothing.

CONSEQUENCE FOR A LIGHT CLIENT, stated plainly: **`select` is a pairwise decision, not a "best
chain" function.** Folding it over a set of candidates is order-dependent, and a peer feeding
candidates in an adversarial order can walk a node around a cycle indefinitely. Any use of this
rule must therefore fix the comparison set and the order — which is exactly what the anchored
segment in `LightClientMina` gives (see §9). -/

/-- `A`: epoch 1 (slot 7139 of 7140), density 50, length 10. -/
def cycA : ConsensusState := mkCS 10 50 [6,5,5,5,5,5,5,6,6,6,6] [] 14279 7140 555 111
/-- `B`: same epoch, same staking lock checkpoint as `A`, but its NEXT-epoch checkpoint is `C`'s.
Length 20. -/
def cycB : ConsensusState := mkCS 20 50 [6,5,5,5,5,5,5,6,6,6,6] [] 14279 7140 555 222
/-- `C`: epoch 2 slot 0 — one slot after `A`/`B`. Density 40, length 30. -/
def cycC : ConsensusState := mkCS 30 40 [4,4,4,4,4,4,4,4,4,4,4] [] 14280 7140 222 333

/-- The regime of the mixed-regime witness: `A~B` and `B~C` SHORT-range, `A~C` LONG-range. -/
theorem cycle_mixed_regime :
    isShortRange mainnet cycA cycB = true
    ∧ isShortRange mainnet cycB cycC = true
    ∧ isShortRange mainnet cycA cycC = false := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- ⚑ **A 3-CYCLE IN SAMASIKA CHAIN SELECTION (mixed regime).** `B` is selected over `A`, `C` over
`B`, and `A` over `C`. A node holding `A` and offered `B`, `C`, `A`, … in that order switches every
time, forever. Every state here is well-formed: 11 sub-window densities, real mainnet constants,
consecutive slots. -/
theorem select_has_a_3_cycle_mixed :
    beats mainnet cycB cycA 2 1 ∧ beats mainnet cycC cycB 3 2 ∧ beats mainnet cycA cycC 1 3 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- The density asymmetry driving the mixed witness: projected to slot 14280, `A` keeps its
density 50 (the sub-window advanced by exactly one, so `update_min_window_density` zeroes nothing —
`proof_of_stake.ml:1294-1301`), while `C`, already AT 14280, is simply its own 40. -/
theorem cycle_mixed_densities :
    virtualMinWindowDensity mainnet cycA 14280 = 50
    ∧ virtualMinWindowDensity mainnet cycC 14280 = 40 := by
  refine ⟨?_, ?_⟩ <;> decide

/-- `A'`: slot 7212, density 10. -/
def lcycA : ConsensusState := mkCS 0 10 [0,0,0,0,0,0,0,0,0,0,7] [] 7212 7140 1044 0
/-- `B'`: slot 7200, density 50. -/
def lcycB : ConsensusState := mkCS 0 50 [7,7,7,7,7,0,0,0,0,0,0] [] 7200 7140 1010 0
/-- `C'`: slot 7200, density 70. Distinct staking lock checkpoints make ALL THREE pairs
long-range. -/
def lcycC : ConsensusState := mkCS 0 70 [0,0,0,0,0,0,0,0,0,0,7] [] 7200 7140 1015 0

/-- All three pairs are LONG-range. -/
theorem cycle_long_regime :
    isShortRange mainnet lcycA lcycB = false
    ∧ isShortRange mainnet lcycB lcycC = false
    ∧ isShortRange mainnet lcycA lcycC = false := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- ⚑ **A 3-CYCLE WITH EVERY PAIR LONG-RANGE.** Nothing about the short/long partition is needed:
the long-range rule alone is intransitive, because `relative_min_window_density` is a function of
the PAIR. Here `C'` beats `B'` at 70-vs-50 (both at slot 7200, no projection), and `A'` beats `C'`
at 10-vs-7 (because projecting `C'` forward to 7212 collapses it to 7), while `B'` beats `A'` at
35-vs-10 (`B'` projected to 7212 keeps 35). -/
theorem select_has_a_3_cycle_long_range_only :
    beats mainnet lcycB lcycA 2 1 ∧ beats mainnet lcycC lcycB 3 2 ∧ beats mainnet lcycA lcycC 1 3 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- The pair-dependence, isolated: `C'`'s relative density is **70** against a rival at its own
slot and **7** against a rival 12 slots ahead. There is no single number "`C'`'s density". -/
theorem relative_density_is_pair_dependent :
    virtualMinWindowDensity mainnet lcycC 7200 = 70
    ∧ virtualMinWindowDensity mainnet lcycC 7212 = 7 := by
  refine ⟨?_, ?_⟩ <;> decide

/-- **THE HEADLINE, as a refutation.** `beats` is NOT transitive, for the OCaml `select` at real
mainnet constants. Stated as the negation of the universally quantified transitivity so that no
reader can take §6's restricted theorem for the general one. -/
theorem beats_not_transitive :
    ¬ (∀ (C : Constants) (a b c : ConsensusState) (ha hb hc : Nat),
        beats C b a hb ha → beats C c b hc hb → beats C c a hc ha) := by
  intro h
  have hcyc := h mainnet lcycA lcycB lcycC 1 2 3
    select_has_a_3_cycle_long_range_only.1 select_has_a_3_cycle_long_range_only.2.1
  have hno : select mainnet lcycA lcycC 1 3 = SelectStatus.keep :=
    select_asymm mainnet lcycC lcycA 3 1 select_has_a_3_cycle_long_range_only.2.2
  unfold beats at hcyc
  rw [hno] at hcyc
  exact SelectStatus.noConfusion hcyc

/-! ## §8 — ⚑ THE SECOND RENDERING DISAGREES. openmina's chain selection is not the daemon's.

`mina-rust/crates/core/src/consensus.rs` transcribes the SPEC DOCUMENT's §5.4.12 pseudocode rather
than the daemon's `update_min_window_density`, and the spec document's §5.4.12 is itself
inconsistent with its own §5.4.9. Three separate defects compound:

  1. **The shift count is measured in SLOTS, not SUB-WINDOWS.** §5.4.9 says "if `next` is `k`
     SUB-WINDOWS ahead we must shift `k − 1` times"; §5.4.12's code writes
     `max_slot - B1.curr_global_slot - 1`, a SLOT difference, and `consensus.rs:88` copies it. With
     `slots_per_sub_window = 7`, a one-sub-window advance becomes a six-shift.
  2. **One extra zero.** `consensus.rs:101` is `for _ in 0..=shift_count` — `shift_count + 1`
     iterations — where the spec's own pseudocode is `while shift_count > 0`.
  3. **The wrong grace-period end.** `consensus.rs:15` hardcodes `GRACE_PERIOD_END = 1440` with a
     `// TODO get constants from elsewhere`; the daemon computes `2160 + 77 = 2237`.

And in the short-range check, `consensus.rs:49` keys on `epoch_count` where the daemon keys on
`curr_global_slot / slots_per_epoch`, and `consensus.rs:50` drops the daemon's `Slot.succ`.

`relMinWindowDensityOpenmina` below is that rendering, so the disagreement is a THEOREM. -/

/-- Zero `n` sub-windows by ring-shifting from index `i` (`consensus.rs:99-104`). -/
def ringZero (C : Constants) : Nat → Nat → List Nat → List Nat
  | 0, _, w => w
  | n + 1, i, w =>
      let i' := (i + 1) % C.subWindowsPerWindow
      ringZero C n i' (w.set i' 0)

/-- **openmina's `relative_min_window_density`** (`consensus.rs:77-112`) — the object openmina's
`long_range_fork_take` actually compares. `gpEnd` is its hardcoded grace-period end. -/
def relMinWindowDensityOpenmina (C : Constants) (gpEnd : Nat) (b1 b2 : ConsensusState) : Nat :=
  let m := max b1.currGlobalSlot b2.currGlobalSlot
  if m < gpEnd then b1.minWindowDensity
  else
    let shiftCount := min (m - (b1.currGlobalSlot + 1)) C.subWindowsPerWindow
    let start := relativeSubWindow C (globalSubWindow C b1.currGlobalSlot)
    let w := ringZero C (shiftCount + 1) start b1.subWindowDensities
    min b1.minWindowDensity (w.foldl (· + ·) 0)

/-- The spec document's §5.4.12 pseudocode literally (`shift_count` iterations, not
`shift_count + 1`) — a THIRD number, so that "the spec says X" cannot be used to defend either
implementation. -/
def relMinWindowDensitySpecDoc (C : Constants) (gpEnd : Nat) (b1 b2 : ConsensusState) : Nat :=
  let m := max b1.currGlobalSlot b2.currGlobalSlot
  if m < gpEnd then b1.minWindowDensity
  else
    let shiftCount := min (m - (b1.currGlobalSlot + 1)) C.subWindowsPerWindow
    let start := relativeSubWindow C (globalSubWindow C b1.currGlobalSlot)
    let w := ringZero C shiftCount start b1.subWindowDensities
    min b1.minWindowDensity (w.foldl (· + ·) 0)

/-- A chain at slot 10000 with a full window. -/
def divA : ConsensusState := mkCS 0 50 [6,5,5,5,5,5,5,6,6,6,6] [] 10000 7140 1 0
/-- The same chain one sub-window later (slot 10007). -/
def divB : ConsensusState := mkCS 0 40 [4,4,4,4,4,4,4,4,4,4,4] [] 10007 7140 2 0

/-- ⚑ **THE THREE RENDERINGS GIVE THREE DIFFERENT ANSWERS** to the same question — the relative
minimum window density of `divA` measured against `divB`, one sub-window ahead. The daemon says
**50** (a one-sub-window advance zeroes NOTHING: `prev_rel = 9`, `next_rel = 10`, and the "within
range" set `{i : 9 < i < 10}` is empty). openmina says **23**. The spec document's own pseudocode
says **28**. -/
theorem three_renderings_three_answers :
    virtualMinWindowDensity mainnet divA 10007 = 50
    ∧ relMinWindowDensityOpenmina mainnet 1440 divA divB = 23
    ∧ relMinWindowDensitySpecDoc mainnet 1440 divA divB = 28 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- The hardcoded grace-period end is load-bearing on its own: at slot 2100 the daemon is still
INSIDE the grace period (`2100 < 2237`) and returns the previous minimum unchanged, while openmina
believes the grace period ended at 1440 and projects. -/
def graceA : ConsensusState := mkCS 0 50 [6,5,5,5,5,5,5,6,6,6,6] [] 2000 7140 1 0
/-- Its rival, 100 slots later. -/
def graceB : ConsensusState := mkCS 0 40 [4,4,4,4,4,4,4,4,4,4,4] [] 2100 7140 2 0

/-- ⚑ **THE GRACE-PERIOD CONSTANT ALONE FLIPS THE NUMBER.** -/
theorem grace_period_end_diverges :
    virtualMinWindowDensity mainnet graceA 2100 = 50
    ∧ relMinWindowDensityOpenmina mainnet 1440 graceA graceB = 0
    ∧ mainnet.gracePeriodEnd = 2237 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- openmina's short-range check, as written (`consensus.rs:45-72`): keyed on `epoch_count`, and
without the daemon's `Slot.succ` before `in_seed_update_range`. -/
def isShortRangeOpenmina (C : Constants) (c1 c2 : ConsensusState) : Bool :=
  let check := fun (s1 s2 : ConsensusState) =>
    decide (s1.epochCount = s2.epochCount + 1)
      && decide (currSlot s2 ≥ C.slotsPerEpoch * 2 / 3)
      && decide (s1.stakingLockCheckpoint = s2.nextLockCheckpoint)
  if c1.epochCount = c2.epochCount then
    decide (c1.stakingLockCheckpoint = c2.stakingLockCheckpoint)
  else check c1 c2 || check c2 c1

/-- A chain whose `epoch_count` LAGS its `curr_epoch` — which happens on the real chain after any
fully-empty epoch, because `epoch_count` is incremented by ONE per transition regardless of how
many epochs were skipped (`proof_of_stake.ml:1130-1140`). Here `curr_epoch = 2`,
`epoch_count = 1`. -/
def lagA : ConsensusState :=
  { mkCS 0 0 [] [] 14280 7140 777 0 with epochCount := 1 }
/-- Its rival, in `curr_epoch` 1 (global slot 14279 = the last slot of epoch 1), sharing no
staking checkpoint but with its NEXT-epoch lock checkpoint equal to `lagA`'s staking one. -/
def lagB : ConsensusState :=
  { mkCS 0 0 [] [] 14279 7140 888 777 with epochCount := 1 }

/-- ⚑ **THE SHORT-RANGE CHECK ITSELF DIVERGES.** The daemon (keyed on `curr_epoch`: 2 vs 1) finds
the adjacent-epoch case and calls this a SHORT-range fork; openmina (keyed on `epoch_count`: 1 vs
1) falls into its same-epoch branch, compares STAKING checkpoints (777 vs 888), and calls it LONG.
Different branch ⇒ a different rule ⇒ potentially a different chain. -/
theorem short_range_check_diverges :
    isShortRange mainnet lagA lagB = true ∧ isShortRangeOpenmina mainnet lagA lagB = false := by
  refine ⟨?_, ?_⟩ <;> decide

/-- **openmina's `consensus_take`** (`consensus.rs:190-201`), assembled from its own
`short_range_fork_take` (`:126`) and `long_range_fork_take` (`:154`). The tie-break chain below the
density is the same lexicographic (length, VRF, state hash) as the daemon's, so `select` and
`selectOpenmina` differ ONLY through `isShortRange` and the density — which is exactly what makes
the differential in `MinaChainSelectionDifferential` diagnostic rather than merely red. -/
def selectOpenmina (C : Constants) (gpEnd : Nat) (e c : ConsensusState) (eh ch : Nat) :
    SelectStatus :=
  if isShortRangeOpenmina C e c then
    (if blockchainLengthLonger e c eh ch then SelectStatus.take else SelectStatus.keep)
  else
    let de := relMinWindowDensityOpenmina C gpEnd e c
    let dc := relMinWindowDensityOpenmina C gpEnd c e
    if de < dc then SelectStatus.take
    else if dc < de then SelectStatus.keep
    else (if blockchainLengthLonger e c eh ch then SelectStatus.take else SelectStatus.keep)

/-- A state whose `epoch_count` is 2 and whose `curr_epoch` is also 2, staking checkpoint 111. -/
def keyA : ConsensusState := { mkCS 0 0 [] [] 14280 7140 111 0 with epochCount := 2 }
/-- Its rival one epoch back in both senses, whose NEXT-epoch checkpoint is `keyA`'s staking one
but whose STAKING checkpoint is different. -/
def keyB : ConsensusState := { mkCS 0 0 [] [] 14279 7140 888 111 with epochCount := 1 }

/-- ⚑ **`select_factors_through_selKey` IS NOT VACUOUS: openmina's rule does NOT factor.** Zero out
the seventeen non-selection fields and the daemon's verdict is unchanged (that theorem is `rfl`);
do the same to openmina's short-range test and it FLIPS, because it reads a NINTH field —
`epoch_count`. So "reads exactly eight fields" is a real property of the daemon's rule that the
second implementation does not have. -/
theorem openmina_does_not_factor_through_selKey :
    isShortRangeOpenmina mainnet keyA keyB = true
    ∧ isShortRangeOpenmina mainnet (selKey keyA) (selKey keyB) = false
    ∧ isShortRange mainnet keyA keyB = isShortRange mainnet (selKey keyA) (selKey keyB) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- The `Slot.succ` off-by-one, isolated: at epoch slot 4759 the daemon's
`not (in_seed_update_range (4759 + 1))` holds (4760 is the first slot past the range) while
openmina's `4759 ≥ 4760` does not. -/
theorem succ_off_by_one :
    inSeedUpdateRange mainnet (4759 + 1) = false
    ∧ decide ((4759 : Nat) ≥ mainnet.slotsPerEpoch * 2 / 3) = false := by
  refine ⟨?_, ?_⟩ <;> decide

/-! ## §9 — THE LIGHT-CLIENT SEAM.

`LightClientMina.minaVerify` decides an ANCHORED SEGMENT: linked, Pickles-proved, `k` deep from a
governance-pinned weak-subjectivity anchor. Its own header names the hole — "a `k`-deep linked
proved segment from a DIFFERENT anchor is not refused by anything here" — and
`LightClientMinaGate`'s ordered remainder names fork choice as item 4.

**What the gate can decide once `select` exists that it could not before**: given TWO accepted
updates `u₁, u₂` (each linked, proved and `k`-deep, possibly under different anchors), it can now
rank their tips and refuse the loser. That is the function below. It is stated at CURRENT
resolution, and the resolution has three named limits:

  * `select` is a TOURNAMENT, not an order (§7). `minaBetterTip` is therefore a comparison of TWO
    named tips, never a fold over a set — folding is order-dependent and cyclable. A light client
    that must choose among many candidates has to fix the comparison set first; the anchored
    segment is what fixes it.
  * The inputs `select` reads are NOT all available from the public GraphQL surface the deployed
    `bridge/src/mina_observer.rs` uses. Measured 2026-07-29 against
    `api.minascan.io/node/devnet`: `blockHeight`, `epoch`, `slot`, `minWindowDensity`,
    `lastVrfOutput` and both `lockCheckpoint`s ARE served, and **`subWindowDensities` is not a
    field of the GraphQL `ConsensusState` at all**. So the LONG-RANGE branch cannot be evaluated
    from GraphQL; it needs the binprot protocol state. The short-range branch can.
  * Selection assumes both tips are already VALID. Here that assumption is discharged by
    `LightClientMina.MinaValidAt` for each side — which is exactly why this belongs at the light
    client and not in front of it.
-/

/-- **`minaBetterTip`** — the fork-choice decision over two candidate tips. `true` means the
CANDIDATE tip wins and the existing one must be dropped. This is `select` with the light client's
naming; it is the object a gate would export. -/
def minaBetterTip (C : Constants) (existing candidate : ConsensusState)
    (existingHash candidateHash : Nat) : Bool :=
  select C existing candidate existingHash candidateHash == SelectStatus.take

/-- **THE LIGHT-CLIENT PROPERTY THAT WAS MISSING.** Two `k`-deep proved segments under different
anchors are no longer indistinguishable: `minaBetterTip` decides between them, it decides the same
way whichever side is presented first (`select_asymm`), and it never prefers a tip to itself
(`select_irrefl`). -/
theorem minaBetterTip_decides (C : Constants) (a b : ConsensusState) (ha hb : Nat) :
    (minaBetterTip C a b ha hb = true → minaBetterTip C b a hb ha = false)
    ∧ minaBetterTip C a a ha ha = false := by
  constructor
  · intro h
    simp only [minaBetterTip, beq_iff_eq] at h ⊢
    rw [select_asymm C a b ha hb h]; simp
  · simp [minaBetterTip, select_irrefl C a ha]

/-- ⚑ **AND THE HONEST LIMIT, AS A THEOREM.** `minaBetterTip` cannot be folded over a candidate
set: the very same states that cycle in §7 make "the best of `{A, B, C}`" depend on the order they
arrive in. This is why the seam is a PAIRWISE comparison against a fixed anchored segment and not
a `List.foldl`. -/
theorem minaBetterTip_is_not_foldable :
    minaBetterTip mainnet lcycA lcycB 1 2 = true
    ∧ minaBetterTip mainnet lcycB lcycC 2 3 = true
    ∧ minaBetterTip mainnet lcycC lcycA 3 1 = true := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-! ## §10 — axiom hygiene. -/

#assert_axioms mainnet_slotsPerWindow
#assert_axioms mainnet_gracePeriodEnd
#assert_axioms lexLt_irrefl
#assert_axioms lexLt_ne
#assert_axioms lexLt_asymm
#assert_axioms lexLt_trans
#assert_axioms lexLt_total
#assert_axioms isShortRange_symm
#assert_axioms isShortRange_refl
#assert_axioms maxSlot_symm
#assert_axioms select_factors_through_selKey
#assert_axioms select_reads_only_eight_fields
#assert_axioms blockchainLengthLonger_irrefl
#assert_axioms select_irrefl
#assert_axioms blockchainLengthLonger_asymm
#assert_axioms select_asymm
#assert_axioms select_ties_only_on_equal_keys
#assert_axioms blockchainLengthLonger_trans
#assert_axioms beats_trans_short_range
#assert_axioms cycle_mixed_regime
#assert_axioms select_has_a_3_cycle_mixed
#assert_axioms cycle_mixed_densities
#assert_axioms cycle_long_regime
#assert_axioms select_has_a_3_cycle_long_range_only
#assert_axioms relative_density_is_pair_dependent
#assert_axioms beats_not_transitive
#assert_axioms three_renderings_three_answers
#assert_axioms grace_period_end_diverges
#assert_axioms openmina_does_not_factor_through_selKey
#assert_axioms short_range_check_diverges
#assert_axioms succ_off_by_one
#assert_axioms minaBetterTip_decides
#assert_axioms minaBetterTip_is_not_foldable

#print axioms select_asymm
#print axioms beats_not_transitive
#print axioms three_renderings_three_answers

end Dregg2.Bridge.MinaChainSelection
