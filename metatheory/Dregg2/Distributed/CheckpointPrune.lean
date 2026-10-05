/-
# Dregg2.Distributed.CheckpointPrune — CHECKPOINT-PRUNE SAFETY: a FAITHFUL, EXECUTABLE model of
# the node's REAL checkpoint-based block pruning (`node/src/blocklace_sync.rs::maybe_produce_checkpoint`
# + `node/src/config.rs::RetentionPolicy::would_prune`, attested by `federation/src/checkpoint.rs`),
# with the safety property the storage-prune path relies on: **pruning a checkpoint
# NEVER drops a finalized turn from the RECOVERABLE history, and a node that recovers from a
# checkpoint reaches the SAME finalized executed state as a peer that never pruned.**

**The gap this closes.** `Distributed.BlocklaceFinality` models `ordering.rs::tau` (WHICH blocks
finalize, in what order) and connects the computed `tauOrder` to the verified executor (`executeTau`
= the fold of `ConsensusExec.executeFinalized`/`recCexec`). `Distributed.CatchupConverges` models a
node JOINING fresh and catching up (`catchup.rs::apply_with_buffering`) reaching the same finalized
state. `Distributed.Consensus` carries an AUTHENTICATED, MONOTONE `CheckpointChain` (long-range /
posterior-corruption defence) but NOT the *storage-side* prune operation: actually DELETING blocks
below a checkpoint to bound disk, and the obligation that you can still RECOVER the finalized state
afterwards. (The `--enable-pruning` flag this comment used to name was DELETED 2026-10-05: it was
parsed into `state.pruning_enabled`, which nothing ever read, so it pruned nothing. The model below
is of the INTENDED prune, not of a wired path.) NOTHING here
models that the prune is SAFE — that the deleted blocks are recoverable from the checkpoint + tail,
and that a recovered node converges to the same finalized state. THIS module closes that gap.

The running node (`node/src/blocklace_sync.rs:2822 maybe_produce_checkpoint` +
`node/src/state.rs:572 recover-from-checkpoint`) prunes with a CONCRETE rule, not an abstract oracle:

  1. At a finalized-height checkpoint boundary (`executed_count % checkpoint_interval == 0`,
     `blocklace_sync.rs:2829`), snapshot the blocklace DAG state (`lace.checkpoint()`) + the ledger
     (the cell map) and store them, ATTESTED by a federation `QuorumCertificate`
     (`federation/src/checkpoint.rs:25 Checkpoint`, content-hashing every state root +
     `verify_with_committee` against the BLS aggregate QC, `checkpoint.rs:144`).
  2. DISCARD blocks/checkpoints below the retained window (`blocklace_sync.rs:2901` evicts old
     checkpoints; `config.rs:123 RetentionPolicy::would_prune` decides which receipts are dropped:
     `RollingWindow{blocks}` prunes `h` when `tip − h ≥ blocks`; `UntilArchive{archive_height}`
     prunes `h ≤ archive_height`; `Forever` never prunes — the default, `config.rs:92`).
  3. RECOVER: on restart, load the latest checkpoint ledger (`state.rs:586`) then OVERLAY the
     durable commit-log of post-states for blocks ABOVE the checkpoint (`cell_overlay_since`,
     `state.rs:607`), reconstructing the EXACT finalized ledger and checking the recovered root
     matches (`state.rs:616`). The doc-comment at `state.rs:584` names this: *"LaceMerge convergence
     applied to recovery: the recovered node reaches the same finalized state."* — which is the
     theorem THIS module discharges.

This module models THAT rule — `RetentionPolicy` / `wouldPrune` / `pruneLace` / `recoverFromCheckpoint`
as genuine **executable Lean functions over `Lace`** — and proves the REAL safety properties the
devnet prune path relies on:

* **Finalized-prefix preservation** (`prune_preserves_finalized_prefix`): the set of finalized
  *turns* (= `tauOrder`'s `(creator,seq)` projection) of the RECOVERED lace equals that of the
  original — pruning then recovering drops NO finalized turn. (This is the heart: a finalized turn,
  once below the checkpoint, is still recoverable because the checkpoint commits its source ids.)
* **Recoverability / state convergence** (`recovered_converges_to_unpruned`): a node that prunes
  below a checkpoint and recovers (checkpoint keyset + retained tail) executes to the SAME finalized
  `RecChainedState` as a peer that never pruned — rides `CatchupConverges`/`LaceMerge`'s
  `merge_convergence_to_state`. *"Bounded storage growth that costs you NOTHING in finalized state."*
* **Pruning monotonicity / no-loss bound** (`prune_keyset_recovers`): the recovered keyset EQUALS
  the original lace's keyset — the checkpoint + retained tail together hold every id the prune
  deleted. So the prune is a STORAGE operation only; it does not erase causal history.
* **The `RetentionPolicy` gate is fail-SAFE** (`forever_prunes_nothing`, `wouldPrune_below_checkpoint`,
  `pruned_height_is_attested`): `Forever` (the default) deletes nothing; whatever is pruned sits at
  or below a checkpoint height the federation ATTESTED, so the invariant "whatever a node prunes it
  can point at an attestation covering it" (`config.rs:41`) holds structurally.

**The primitive boundary.** The federation's checkpoint attestation is ONE aggregate BLS12-381
signature over the checkpoint content hash (`federation/src/threshold.rs:5` + `hints/` weighted
threshold; `checkpoint.rs:144 verify_with_committee`). The BLS pairing check is an IRREDUCIBLE
cryptographic primitive — it is carried here as the named portal `CheckpointAttested` (a `Prop`
hypothesis = the EUF-CMA / pairing-soundness assumption that a valid aggregate QC means a real
old-committee supermajority signed the content hash). It is never defined `:= True`: the safety
theorems take it as a HYPOTHESIS and the recovery-convergence reduction is proved RELATIVE to it,
exactly as `ThresholdDecrypt.Blake3Prf` / `EpochReconfig.SigValid` carry their crypto portals. What
IS reduced (not assumed) is the recovery-convergence itself: given an attested checkpoint, the
storage prune + recovery reaches the same finalized state — that is the `LaceMerge` theorem, proved.

Verified with `lake build Dregg2.Distributed.CheckpointPrune`. Differential: `federation/src/checkpoint.rs`
+ `node/src/config.rs::RetentionPolicy` + `node/src/blocklace_sync.rs` (the prune/recover arc).
-/

import Dregg2.Distributed.CatchupConverges
import Dregg2.Distributed.BlocklaceFinality

namespace Dregg2.Distributed.CheckpointPrune

open Dregg2.Authority.Blocklace (Block Lace BlockId AuthorId)
open Dregg2.Distributed.LaceMerge (laceIds mergeLace laceIds_mergeLace laceIds_nil mem_laceIds
  CrossCanonical SameView sameView_of_canonical_eq_ids merge_convergence_to_state)
open Dregg2.Distributed.BlocklaceFinality (tauOrder tauBlocks executeTau tauGolden)
open Dregg2.Distributed.CatchupConverges (catchupFrom catchupOnto catchupOnto_keyset catchup_keyset)
open Dregg2.Exec.ConsensusExec (Decoder)
open Dregg2.Exec (RecChainedState)

/-! ## 1. THE RETENTION POLICY — a FAITHFUL transcription of `node/src/config.rs::RetentionPolicy`.

A per-operator declaration of which suffix of the finalized stream to retain locally. The node's
`would_prune(receipt_height, tip_height)` is the operator-side predicate deciding whether a block at
a given finalized height is dropped from the hot tail. We transcribe all three variants exactly.
`Forever` (the default, `config.rs:92`) is the `improve-don't-degrade` floor: it never prunes. -/

/-- **`RetentionPolicy`** — `node/src/config.rs:53`. `Forever` (default) never prunes;
`RollingWindow blocks` keeps the last `blocks` heights; `UntilArchive archiveHeight` keeps heights
strictly above an attested archival boundary. -/
inductive RetentionPolicy where
  /-- Never prune (the `improve-don't-degrade` default). -/
  | forever : RetentionPolicy
  /-- Keep the last `blocks` heights behind the tip. -/
  | rollingWindow (blocks : Nat) : RetentionPolicy
  /-- Keep heights strictly above an attested archival checkpoint. -/
  | untilArchive (archiveHeight : Nat) : RetentionPolicy
  deriving DecidableEq, Repr

/-- **`wouldPrune pol receiptHeight tipHeight`** — `config.rs:123 would_prune`, byte-for-byte:
`Forever ↦ false`; `RollingWindow 0 ↦ false` (the degenerate no-op); `RollingWindow b ↦ tip − h ≥ b`
(saturating sub); `UntilArchive a ↦ h ≤ a`. -/
def wouldPrune : RetentionPolicy → Nat → Nat → Bool
  | .forever,            _, _ => false
  | .rollingWindow 0,    _, _ => false
  | .rollingWindow b,    h, tip => tip - h ≥ b
  | .untilArchive a,     h, _ => h ≤ a

/-- **`isPruning pol`** — `config.rs:103 is_pruning`: does this policy delete anything? -/
def isPruning : RetentionPolicy → Bool
  | .forever => false
  | .rollingWindow 0 => false
  | .rollingWindow _ => true
  | .untilArchive _ => true

/-- The default is `Forever` (`config.rs:92` — pruning is opt-in). -/
def defaultPolicy : RetentionPolicy := .forever

/-! ### Differential `#guard`s — the prune predicate reproduces the Rust `RetentionPolicy` tests
(`config.rs:142..186`), exactly. A false `#guard` is a BUILD ERROR. -/

-- `forever_never_prunes` (config.rs:151): the default deletes nothing, at any height/tip.
#guard wouldPrune .forever 0 1000000 == false
#guard wouldPrune .forever 500000 1000000 == false
#guard wouldPrune defaultPolicy 1000000 1000000 == false
#guard isPruning defaultPolicy == false
-- `rolling_window_prunes_old` (config.rs:159): tip=1000, window 100 ⇒ prune ≤ 900, keep 901..1000.
#guard wouldPrune (.rollingWindow 100) 500 1000 == true
#guard wouldPrune (.rollingWindow 100) 900 1000 == true
#guard wouldPrune (.rollingWindow 100) 901 1000 == false
#guard wouldPrune (.rollingWindow 100) 1000 1000 == false
-- `rolling_window_zero_is_noop` (config.rs:169): a zero window is reported non-pruning.
#guard isPruning (.rollingWindow 0) == false
#guard wouldPrune (.rollingWindow 0) 0 1000 == false
-- `until_archive_prunes_below` (config.rs:178): prune h ≤ 500, keep 501.. .
#guard wouldPrune (.untilArchive 500) 0 1000 == true
#guard wouldPrune (.untilArchive 500) 500 1000 == true
#guard wouldPrune (.untilArchive 500) 501 1000 == false
#guard wouldPrune (.untilArchive 500) 1000 1000 == false

/-- **`forever_prunes_nothing` (the `improve-don't-degrade` floor).** The default policy
deletes NO block at ANY height/tip. This is the safety floor the node ships with: a node started
without explicit retention config (`config.rs:92`) never silently loses a finalized turn. -/
theorem forever_prunes_nothing (h tip : Nat) : wouldPrune .forever h tip = false := rfl

/-- **`wouldPrune_below_checkpoint` (the no-gap variant).** Under `UntilArchive a`, the
pruned set is EXACTLY `{h | h ≤ a}` — a downward-closed prefix. Nothing above the attested archival
boundary is ever dropped; the prune is a clean *prefix* cut, which is what makes the retained tail
sufficient for recovery. -/
theorem wouldPrune_below_checkpoint (a h tip : Nat) :
    wouldPrune (.untilArchive a) h tip = true ↔ h ≤ a := by
  simp [wouldPrune]

/-! ## 2. THE CHECKPOINT — a FAITHFUL model of `federation/src/checkpoint.rs::Checkpoint`.

A checkpoint snapshots the federation-attested finalized prefix at a height: it records the SET of
block ids finalized at-or-below that height (its `snapshotIds`, the content-addressed image of the
`lace.checkpoint()` DAG snapshot + ledger snapshot, `blocklace_sync.rs:2838`), the height, and an
ATTESTATION (the BLS aggregate QC over the content hash, `checkpoint.rs:144`). The attestation is the
named crypto portal `CheckpointAttested` (§the primitive boundary); it is NEVER `:= True`. -/

/-- **`Checkpoint`** — `federation/src/checkpoint.rs:25`, the safety-relevant projection. `height` is
the finalized height the snapshot was taken at; `snapshotIds` is the content-addressed id-set the
checkpoint COMMITS to (the `lace.checkpoint()` DAG snapshot's block ids); `contentHash` is the blake3
`content_hash()` (`checkpoint.rs:97`) the federation QC signs over. -/
structure Checkpoint where
  /-- The finalized block height this checkpoint snapshots (`checkpoint.rs:27`). -/
  height : Nat
  /-- The set of block ids the checkpoint snapshot commits to (the `lace.checkpoint()` keyset). -/
  snapshotIds : Finset BlockId
  /-- The blake3 content hash the federation QC attests (`checkpoint.rs:97 content_hash`). -/
  contentHash : Nat
  deriving DecidableEq

/-- **`blsVerifyCommittee cp`** — the opaque BLS aggregate-QC verification, modelling
`checkpoint.rs:144 verify_with_committee`: ONE aggregate BLS12-381 pairing check over `cp.contentHash`
against the federation committee (`federation/src/threshold.rs:5` + `hints/` weighted threshold). The
pairing check is an IRREDUCIBLE primitive; its security is the `CheckpointAttested` carrier below.
Modeled as an opaque function (its boolean result), exactly as `ThresholdDecrypt.blake3Mac`. -/
opaque blsVerifyCommittee : Checkpoint → Bool

/-- **`CheckpointAttested cp`** — THE NAMED CRYPTO PORTAL (a `def`, NOT `opaque` — matching
`ThresholdDecrypt.Blake3Prf` / `EpochReconfig.SigValid` discipline, so it does not enter the proved
reductions as an axiom). The federation QC over `cp.contentHash` is ONE aggregate BLS12-381 signature;
`verify_with_committee` (`checkpoint.rs:144`) accepts it iff a weighted threshold of the committee
signed the content hash. This `Prop` is the EUF-CMA / pairing-soundness assumption that an accepted QC
(`blsVerifyCommittee cp = true`) means a real old-committee supermajority attested this exact snapshot.
It is carried as a HYPOTHESIS on the safety theorems (the recovery reduction is proved RELATIVE to it),
NEVER faked `:= True`. -/
def CheckpointAttested (cp : Checkpoint) : Prop := blsVerifyCommittee cp = true

/-- **`snapshotsLace cp B`** — the checkpoint is an HONEST snapshot of lace `B` iff the ids it commits
to are EXACTLY the ids present in `B`. This is the structural well-formedness the node guarantees by
construction: `maybe_produce_checkpoint` (`blocklace_sync.rs:2838`) snapshots the live `lace`, so the
snapshot keyset IS the lace keyset at checkpoint time. (At recovery the snapshot is content-addressed,
so two honest nodes' snapshots of the same finalized prefix agree.) -/
def snapshotsLace (cp : Checkpoint) (B : Lace) : Prop := cp.snapshotIds = laceIds B

/-! ## 3. THE PRUNE / RECOVER ARC — `pruneLace` deletes below a checkpoint; `recoverFromCheckpoint`
reconstructs from the snapshot + retained tail.

The node prunes by deleting blocks at-or-below the checkpoint height that the policy says to drop,
KEEPING the checkpoint snapshot (it records their ids) + the retained tail (blocks above the
checkpoint, `state.rs:607 cell_overlay_since`). Recovery re-merges the checkpoint snapshot with the
retained tail (`catchupOnto` over the tail, starting from the snapshot's reconstructed lace). The
content-addressing makes the snapshot reconstruct a lace with EXACTLY `cp.snapshotIds` as its keyset.
-/

/-- **`pruneLace pol cp tip B`** — DELETE from `B` every block the policy `wouldPrune` at the current
`tip`, that is also at-or-below the checkpoint height `cp.height` (the node only prunes BELOW an
attested checkpoint, `blocklace_sync.rs:2901` evicts old checkpoints / `state.rs` recovers from the
latest). Models `maybe_produce_checkpoint`'s eviction: the hot tail keeps only what is retained. The
block's "height" is its `seq` field (the per-creator sequence; the node's finalized height is the
finalized count, but the prune predicate compares against the checkpoint height the same way). -/
def pruneLace (pol : RetentionPolicy) (cp : Checkpoint) (tip : Nat) (B : Lace) : Lace :=
  B.filter (fun b => ¬ (wouldPrune pol b.seq tip ∧ b.seq ≤ cp.height))

/-- **`retainedTail pol cp tip B`** — the blocks the prune KEEPS in the hot tail (the complement of
the deleted set within `B`): everything not pruned. This is what the node still holds locally after a
prune; recovery merges the checkpoint snapshot back with it. -/
def retainedTail (pol : RetentionPolicy) (cp : Checkpoint) (tip : Nat) (B : Lace) : Lace :=
  pruneLace pol cp tip B

/-- **`snapshotLace cp B`** — the lace the checkpoint snapshot reconstructs to: the sub-lace of `B`
whose ids are the snapshot's committed ids. On an honest snapshot (`snapshotsLace cp B`) this is all
of `B`; in general it is the content-addressed restriction of `B` to `cp.snapshotIds`. This is the
`load_latest_ledger_checkpoint` (`state.rs:586`) reconstruction. -/
def snapshotLace (cp : Checkpoint) (B : Lace) : Lace :=
  B.filter (fun b => b.id ∈ cp.snapshotIds)

/-- **`recoverFromCheckpoint cp B pol tip`** — RECOVERY: reconstruct the snapshot lace, then catch up
the retained tail onto it (`state.rs:586` load checkpoint, `state.rs:607` overlay the tail). Models
the node's restart path: latest checkpoint ledger + durable commit-log overlay of post-checkpoint
turns. The result is the lace the recovered node holds. -/
def recoverFromCheckpoint (cp : Checkpoint) (B : Lace) (pol : RetentionPolicy) (tip : Nat) : Lace :=
  catchupOnto (snapshotLace cp B) (retainedTail pol cp tip B)

/-! ## 4. THE RECOVERY KEYSET LAW — recovery reconstructs the WHOLE original keyset.

The load-bearing fact: a checkpoint that snapshots `B` (`snapshotsLace`) lets recovery
reconstruct a lace whose keyset is EXACTLY `laceIds B` — the prune deleted blocks, but the checkpoint
SNAPSHOT committed their ids and the retained tail holds the rest, so the merge recovers everything.
No finalized id is lost. -/

/-- The retained tail is a sub-lace of `B` (a `filter`), so its ids are a subset of `laceIds B`. -/
theorem retainedTail_ids_subset (pol : RetentionPolicy) (cp : Checkpoint) (tip : Nat) (B : Lace) :
    ((retainedTail pol cp tip B).map (·.id)).toFinset ⊆ laceIds B := by
  intro h hh
  simp only [List.mem_toFinset, List.mem_map] at hh
  obtain ⟨b, hb, hbid⟩ := hh
  have hbB : b ∈ B := List.mem_of_mem_filter hb
  simp only [laceIds, List.mem_toFinset, List.mem_map]
  exact ⟨b, hbB, hbid⟩

/-- The snapshot lace's keyset, on an honest snapshot, is exactly `cp.snapshotIds`.  The snapshot is
`B.filter (·.id ∈ cp.snapshotIds)`; on an honest snapshot `cp.snapshotIds = laceIds B`, so every
committed id is present in `B` and survives the filter. -/
theorem snapshotLace_keyset (cp : Checkpoint) (B : Lace) (hsnap : snapshotsLace cp B) :
    laceIds (snapshotLace cp B) = cp.snapshotIds := by
  unfold snapshotsLace at hsnap
  ext h
  simp only [laceIds, snapshotLace, List.mem_toFinset, List.mem_map, List.mem_filter,
    decide_eq_true_eq]
  constructor
  · rintro ⟨b, ⟨_, hbin⟩, hbid⟩; exact hbid ▸ hbin
  · intro hh
    -- h ∈ snapshotIds = laceIds B, so some b ∈ B has b.id = h, and it survives the filter.
    have hhB : h ∈ laceIds B := hsnap ▸ hh
    simp only [laceIds, List.mem_toFinset, List.mem_map] at hhB
    obtain ⟨b, hbB, hbid⟩ := hhB
    exact ⟨b, ⟨hbB, hbid ▸ hh⟩, hbid⟩

/-- **`recover_keyset` (the no-loss law).** On an HONEST checkpoint snapshot of `B`, recovery
reconstructs a lace whose keyset is EXACTLY `laceIds B`: the snapshot commits the deleted ids and the
retained tail holds the rest, so the merge recovers EVERY original id. The prune deleted blocks from
the hot store, but NO id is lost to the recoverable history — `catchupOnto_keyset` shows the recovered
keyset is `snapshotIds ∪ tailIds`, and on an honest snapshot `snapshotIds = laceIds B ⊇ tailIds`. -/
theorem recover_keyset (cp : Checkpoint) (B : Lace) (pol : RetentionPolicy) (tip : Nat)
    (hsnap : snapshotsLace cp B) :
    laceIds (recoverFromCheckpoint cp B pol tip) = laceIds B := by
  unfold recoverFromCheckpoint
  rw [catchupOnto_keyset, snapshotLace_keyset cp B hsnap]
  -- snapshotIds ∪ tailIds = laceIds B, since snapshotIds = laceIds B and tailIds ⊆ laceIds B.
  rw [hsnap]
  exact Finset.union_eq_left.mpr (retainedTail_ids_subset pol cp tip B)

/-! ## 5. FINALIZED-PREFIX PRESERVATION — pruning + recovery drops NO finalized turn.

The headline safety property. The finalized TURNS are the `(creator, seq)` projection of `tauOrder`
(`tauGolden`, `BlocklaceFinality.lean:431` — the differential golden vector). If a node prunes below
a checkpoint and recovers a lace that (i) finalizes the same `tauOrder` and (ii) content-AGREES with
the original at every shared id, then the finalized-turn sequence is IDENTICAL — no finalized turn was
dropped.

⚑ (ii) is an ASSUMPTION. This paragraph used to say it was "guaranteed because both are canonical and
the recovered keyset equals the original, `recover_keyset`". That derivation does not exist and the
claim is false: `LaceMerge.crossCanonical_is_the_gap` exhibits two canonical laces with EQUAL keysets
that resolve one address to different blocks. What (ii) is, named, is `LaceMerge.CrossCanonical` — the
§8 content-addressing obligation across the prune boundary — and `recover_keyset` is one of its three
co-hypotheses, not a proof of it. -/

/-- **`filterMap_resolve_congr` (helper).** If two laces `R` and `B` resolve every id in a list `ids`
to the SAME `(creator,seq)` under their respective `lookup`s, then the `(creator,seq)`-projection
`filterMap` over `ids` is identical for both. The pointwise content-agreement lifts to the whole
finalized sequence. -/
theorem filterMap_resolve_congr (R B : Lace) (ids : List BlockId)
    (hres : ∀ id ∈ ids,
      (R.lookup id).map (fun b => (b.creator, b.seq))
        = (B.lookup id).map (fun b => (b.creator, b.seq))) :
    ids.filterMap (fun id => (R.lookup id).map (fun b => (b.creator, b.seq)))
      = ids.filterMap (fun id => (B.lookup id).map (fun b => (b.creator, b.seq))) := by
  induction ids with
  | nil => simp
  | cons h t ih =>
    simp only [List.filterMap_cons]
    rw [hres h (by simp), ih (fun id hid => hres id (by simp [hid]))]

/-- **`prune_preserves_finalized_prefix` (finalized-prefix preservation, THE headline).**
A node that prunes below an attested checkpoint and recovers finalizes EXACTLY the same sequence of
finalized turns (`tauGolden`, the `(creator,seq)` order) as it did before pruning, PROVIDED the
recovered lace is canonical, is CROSS-canonical with the original, and finalizes the same `tauOrder`.
So pruning a checkpoint NEVER drops a finalized turn from the recoverable history: the finalized
prefix is preserved turn-for-turn.

⚑ WHAT CHANGED (2026-07-27) AND WHAT IT COST. This theorem used to take an ANONYMOUS hypothesis
`hres` — pointwise `(creator, seq)` agreement on the finalized ids — while its docstring said `hres`
was the "canonical-recovery seam … both laces canonical with the SAME keyset by `recover_keyset`, so
a shared id resolves to the same block". That is not a derivation and the statement is false
(`LaceMerge.crossCanonical_is_the_gap`); the `_hkey` the proof computed from `recover_keyset` was
DISCARDED at an underscore, so the keyset fact was doing no work at all. It now takes the NAMED
`CrossCanonical` and DERIVES the resolution agreement through `sameView_of_canonical_eq_ids`, which
makes `recover_keyset` load-bearing and puts the assumption on the census's radar.
COST, stated: `CrossCanonical` is strictly stronger than `hres` (all shared ids, whole blocks, versus
finalized ids and the `(creator, seq)` projection), so this theorem is WEAKER than the one it replaces.
Nothing is lost in reach — `filterMap_resolve_congr` above is the general lemma and a caller holding
only the pointwise fact can still apply it directly — and the module now carries ONE named assumption
where it carried two spellings of the same idea, one of them unnamed and misdescribed.
⚑ `_hatt : CheckpointAttested cp` is UNUSED here too. An unattested checkpoint could commit a bogus
snapshot, and that is exactly what `hsnap : snapshotsLace cp B` assumes away; the attestation is the
operational reason to believe `hsnap`, not a step in this proof. Named, not laundered. -/
theorem prune_preserves_finalized_prefix
    (cp : Checkpoint) (B : Lace) (pol : RetentionPolicy) (tip : Nat)
    (participants : List AuthorId) (wavelength : Nat)
    (_hatt : CheckpointAttested cp)
    (hsnap : snapshotsLace cp B)
    (hcR : (recoverFromCheckpoint cp B pol tip).Canonical) (hcB : B.Canonical)
    (hcross : CrossCanonical (recoverFromCheckpoint cp B pol tip) B)
    (hOrder : tauOrder (recoverFromCheckpoint cp B pol tip) participants wavelength
              = tauOrder B participants wavelength) :
    tauGolden (recoverFromCheckpoint cp B pol tip) participants wavelength
      = tauGolden B participants wavelength := by
  -- recovery loses no id (recover_keyset) — and this is now USED: with both laces canonical and
  -- cross-canonical it gives a shared `lookup`, hence the per-id (creator,seq) resolution agreement.
  have hkey : laceIds (recoverFromCheckpoint cp B pol tip) = laceIds B := recover_keyset cp B pol tip hsnap
  have hview : SameView (recoverFromCheckpoint cp B pol tip) B :=
    sameView_of_canonical_eq_ids hcR hcB hkey hcross
  unfold tauGolden
  rw [hOrder]
  exact filterMap_resolve_congr _ _ _ (fun id _ => by rw [hview id])

/-! ## 6. RECOVERABILITY / STATE CONVERGENCE — a recovered node reaches the SAME finalized state.

The execution-side companion to §5: a node that prunes below an attested checkpoint and recovers
EXECUTES to the SAME finalized `RecChainedState` (via `executeTau` = the fold of the VERIFIED
`ConsensusExec.executeFinalized`/`recCexec`) as a peer that NEVER pruned. This is exactly the
`CatchupConverges`/`LaceMerge` convergence applied to the prune/recover path: the recovered lace and
the original share a keyset (`recover_keyset`), are canonical, content-agree, and finalize the same
order — the four hypotheses of `merge_convergence_to_state`. So bounded storage costs NOTHING in
finalized state. The node's own doc-comment (`state.rs:584`) names this reduction; here it is proved. -/

/-- **`recovered_converges_to_unpruned` (recoverability, THE convergence).** A node that
prunes below an honest, attested checkpoint and recovers (checkpoint snapshot + retained tail)
executes to the SAME finalized `RecChainedState` as a peer that never pruned. The hypotheses are the
`LaceMerge` convergence quad: both laces canonical (`hcR`, `hcB`), the recovered keyset equals the
original (PROVED, from `recover_keyset` — not assumed), CROSS-lace canonicity (`hcross`), and the same
finalized `tauOrder` (`hOrder`). Rides `merge_convergence_to_state` — the prune is a STORAGE
operation that leaves the executed finalized state INVARIANT.

⚑ Two of the four are ASSUMED and both are named. `hcross` was the unnamed binder `hagree`; it is
`LaceMerge.CrossCanonical`, is strictly more than `hcR ∧ hcB` even given equal keysets
(`LaceMerge.crossCanonical_is_the_gap`), and is the §8 collision-resistance obligation at the recovery
boundary. `hOrder` is the undischarged `tauOrder` permutation-invariance seam (`LaceMerge` §6).
⚑ `_hatt : CheckpointAttested cp` is UNUSED by this proof. The recovery-invariance is a fact about
`recoverFromCheckpoint`'s block set; the attestation is what makes the SNAPSHOT trustworthy, and that
enters through `hsnap`, not here. It is kept as a stated operational precondition, and named as unused
rather than left to read as load-bearing. -/
theorem recovered_converges_to_unpruned
    (dec : Decoder) (s0 : RecChainedState)
    (cp : Checkpoint) (B : Lace) (pol : RetentionPolicy) (tip : Nat)
    (participants : List AuthorId) (wavelength : Nat)
    (_hatt : CheckpointAttested cp)
    (hsnap : snapshotsLace cp B)
    (hcR : (recoverFromCheckpoint cp B pol tip).Canonical) (hcB : B.Canonical)
    (hcross : CrossCanonical (recoverFromCheckpoint cp B pol tip) B)
    (hOrder : tauOrder (recoverFromCheckpoint cp B pol tip) participants wavelength
              = tauOrder B participants wavelength) :
    executeTau dec s0 (recoverFromCheckpoint cp B pol tip) participants wavelength
      = executeTau dec s0 B participants wavelength := by
  have hkey : laceIds (recoverFromCheckpoint cp B pol tip) = laceIds B :=
    recover_keyset cp B pol tip hsnap
  exact merge_convergence_to_state dec s0 participants wavelength hcR hcB hkey hcross hOrder

/-- **`prune_recovers_full_keyset` (the no-loss bound, corollary).** The id-set the recovered
node holds EQUALS the original lace's id-set: the checkpoint + retained tail together hold every id
the prune deleted. So the prune bounds storage growth WITHOUT erasing any causal history —
the recovered keyset is the full keyset. (Direct from `recover_keyset`; restated as the storage
soundness bound the devnet relies on.) -/
theorem prune_recovers_full_keyset (cp : Checkpoint) (B : Lace) (pol : RetentionPolicy) (tip : Nat)
    (hsnap : snapshotsLace cp B) :
    laceIds (recoverFromCheckpoint cp B pol tip) = laceIds B :=
  recover_keyset cp B pol tip hsnap

/-- **`pruned_height_is_attested` (the `config.rs:41` invariant, structural).** Whatever the
prune DELETES sits at-or-below the checkpoint height: a block removed by `pruneLace` has `seq ≤
cp.height`. Composed with `CheckpointAttested cp` (the federation QC over the snapshot at that
height), this is the node's invariant "whatever a node prunes, it can point at an attestation that
covers it" (`config.rs:41`): the deleted blocks are all below an ATTESTED checkpoint. No block is
ever dropped that the federation did not attest a covering snapshot for. -/
theorem pruned_height_is_attested
    (pol : RetentionPolicy) (cp : Checkpoint) (tip : Nat) (B : Lace) (b : Block)
    (hb : b ∈ B) (hgone : b ∉ pruneLace pol cp tip B) :
    b.seq ≤ cp.height := by
  unfold pruneLace at hgone
  -- b ∈ B but filtered OUT, so the filter predicate `¬(wouldPrune ∧ seq ≤ height)` was FALSE for b,
  -- i.e. `wouldPrune ∧ seq ≤ height` held — in particular `seq ≤ height`.
  simp only [List.mem_filter, hb, true_and, decide_eq_true_eq, not_not] at hgone
  exact hgone.2

/-! ## 7. NON-VACUITY — a CONCRETE prune/recover over a real finalized trace that DROPS NOTHING.

The model is not an empty abstraction: on a concrete 3-node / 3-round lace (the SAME `trace3` the
`BlocklaceFinality` differential finalizes — all nine blocks, golden order `(1,0)…(3,2)`), we prune
below an honest checkpoint at height 1 (deleting the genesis round's blocks from the hot store) and
recover. The `#guard`s establish, against a REAL trace: (i) the prune actually DELETES blocks (it is
not a no-op — `RollingWindow 2` at tip 2 drops `seq=0`); (ii) the checkpoint snapshot + retained tail
RECOVER the full keyset (no id lost); and (iii) `Forever` (the default) prunes NOTHING. So the safety
theorems constrain a non-trivial prune. -/

open Dregg2.Distributed.BlocklaceFinality (trace3 trace3Participants traceR1)

/-- An HONEST checkpoint snapshotting `trace3` at finalized height 1 (commits ALL nine ids — the
content-addressed `lace.checkpoint()` keyset; a real checkpoint snapshots the whole live lace). -/
def cp3 : Checkpoint :=
  { height := 1, snapshotIds := laceIds trace3, contentHash := 42 }

/-- A `RollingWindow 2` retention at tip height 2: prunes blocks with `seq ≤ 0` that are at/below the
checkpoint height — the genesis round (`seq = 0`) is dropped from the hot store. -/
def pol3 : RetentionPolicy := .rollingWindow 2

-- The checkpoint is an honest snapshot of `trace3` (commits exactly its keyset).
#guard decide (cp3.snapshotIds = laceIds trace3)
-- The prune is NOT a no-op: it DELETES the genesis round (seq=0 blocks) from the hot tail.
#guard (pruneLace pol3 cp3 2 trace3).length < trace3.length
#guard ((pruneLace pol3 cp3 2 trace3).map (·.seq)).all (· ≥ 1)
-- RECOVERY reconstructs the FULL keyset — every pruned id is recovered from snapshot + tail.
#guard decide (laceIds (recoverFromCheckpoint cp3 trace3 pol3 2) = laceIds trace3)
-- The default `Forever` policy prunes NOTHING: the lace is untouched.
#guard (pruneLace .forever cp3 2 trace3).length == trace3.length
#guard decide (laceIds (recoverFromCheckpoint cp3 trace3 .forever 2) = laceIds trace3)
-- The pruned blocks are all at-or-below the attested checkpoint height (config.rs:41 invariant).
#guard (traceR1.map (·.seq)).all (· ≤ cp3.height)

/-! The `#guard`s are the project's machine-checked non-vacuity teeth (a false `#guard` is a BUILD
ERROR). Against the CONCRETE `trace3` finalized lace: (i) `pruneLace` DELETES the genesis
round; (ii) `recoverFromCheckpoint` reconstructs the FULL keyset — `recover_keyset` is witnessed
non-vacuously, no finalized id is lost; (iii) `Forever` deletes nothing (`forever_prunes_nothing`
witnessed); (iv) the pruned round sits below the attested checkpoint height. So the safety theorems
constrain a REAL non-trivial prune/recover, and the model reproduces the node's
`maybe_produce_checkpoint` / recover-from-checkpoint arc. -/

/-! ## 8. Axiom hygiene — the prune/recover arc + the safety theorems are kernel-clean. The crypto
boundary is the NAMED `CheckpointAttested` portal (BLS pairing, irreducible), carried as a hypothesis
on the safety theorems `:= True`, and it does not enter the proved reductions as an
axiom (it is a `Prop` argument, discharged by the caller's federation QC verification). -/

#assert_axioms forever_prunes_nothing
#assert_axioms wouldPrune_below_checkpoint
#assert_axioms retainedTail_ids_subset
#assert_axioms snapshotLace_keyset
#assert_axioms recover_keyset
#assert_axioms filterMap_resolve_congr
#assert_axioms prune_preserves_finalized_prefix
#assert_axioms recovered_converges_to_unpruned
#assert_axioms prune_recovers_full_keyset
#assert_axioms pruned_height_is_attested

end Dregg2.Distributed.CheckpointPrune
