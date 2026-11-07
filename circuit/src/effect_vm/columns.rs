//! Column layout constants for the Effect VM AIR trace.
//!
//! Defines `EFFECT_VM_WIDTH`, the per-effect-class column block bases,
//! and four sub-modules that name each column by purpose:
//! - `sel` — one boolean column per effect type (NUM_EFFECTS = 29).
//! - `state` — 14 columns describing cell state at row enter/exit.
//! - `param` — 8 effect-typed parameter columns.
//! - `aux_off` — NUM_AUX auxiliary witness columns.

/// Total trace width.
/// Layout: 54 selector columns (30 live + 24 retired-pinned-zero) + 14 state_before
/// + 8 params + 14 state_after + 96 aux = 186.
///
/// The aux block decomposes as:
///   `aux[8..10]` = state commitment intermediates;
///   `aux[11]` = cumulative custom-effect count (sum-check, Stage 1);
///   `aux[12..20]` = old_reserved bit-decomposition for sealing honesty (Stage 2),
///   plus mode_flag bit at `aux[20]`;
///   `aux[21..22]` = retired ResizeQueue sign/mag slots (always zero since the
///   queue family dissolved; compacted in the descriptor-regeneration lane);
///   `aux[23..28]` = sovereign-witness key-commit + sequence;
///   `aux[28..36]` = federation-id + owner-cell-id binding (γ.2 #131/#132);
///   `aux[36..96]` = W9-RANGECHECK 30+30 bit decomposition of new_balance_lo/hi,
///   enforced UNCONDITIONALLY on every row via booleanity + recomposition —
///   a wrapped debit `old - amount` mod p lands outside [0, 2^30) and cannot be
///   bit-decomposed, so the STARK rejects it IN-circuit.
///
/// NB: aux[2..5] are reserved on row 0 for delta_mag / delta_sign /
/// effects_hash_4[0..1] boundary writes. Per-effect witnesses must avoid
/// those slots on row 0; aux[6..7] are exclusive per-row selector-gated.
pub const EFFECT_VM_WIDTH: usize = AUX_BASE + NUM_AUX; // 90 + 98 = 188

/// Number of effect types (selector COLUMNS).
///
/// VERB-LOCKSTEP: 30 effects are LIVE (29 + the dedicated supply [`sel::MINT`],
/// SUPPLY-MODEL.md Stage 2b, which repurposed one retired index); the 24
/// factory-dissolved effects (escrow ×6, obligation ×3, bridge lock/finalize/
/// cancel ×3, queue ×6, caps-in-slots) no longer exist as `Effect` variants —
/// their selector
/// COLUMNS remain in the layout (the frozen verified descriptors emitted by
/// `Dregg2/Circuit/Emit/*` pin absolute column indices against the 186-wide
/// trace).
///
/// ⚑ **CORRECTION, 2026-07-30.** This note used to claim "the AIR pins every
/// retired selector to ZERO on every row, so no valid trace can carry a doomed
/// effect (the refusal is in-circuit)". **That was false.** MEASURED across all
/// 117 emitted members of `rotation-v3-staged-registry.tsv` +
/// `rotation-wide-registry-staged.tsv`: the 24 retired selector columns are
/// referenced by **zero** constraints — no pin-to-zero, no gate, no lookup. A
/// trace CAN carry a non-zero retired selector. What makes that harmless is not
/// a refusal but INERTNESS: no constraint reads those columns, so their value
/// cannot reach any published slot or any state transition. The measurement is
/// the gate `circuit/tests/unforced_pi_pin_census.rs::
/// retired_selector_columns_are_referenced_by_nothing`, which goes red the day
/// one of them becomes load-bearing — a prose claim could not.
///
/// The column COMPACTION (54 → 30 selectors) is a pure size win and needs the
/// producer relayout: `Transition { hi, lo }` is offset-encoded through the
/// FIXED state bases (`EFFECTVM_STATE_{BEFORE,AFTER}_BASE = NUM_EFFECTS`, …),
/// so deleting selector columns moves every state and appendix column in every
/// member and every producer that fills them. It is the descriptor-regeneration
/// lane's, not a doc's.
pub const NUM_EFFECTS: usize = 54;

/// Selector column indices.
///
/// VERB-LOCKSTEP: the 29 live effects keep their historical column indices
/// (the frozen verified descriptors pin absolute columns); the 24 retired
/// indices are listed in [`sel::RETIRED_SELECTORS`].
///
/// ⚑ They are NOT pinned to zero by anything — see the correction on
/// [`NUM_EFFECTS`]. They are unreferenced, hence inert, and that is measured.
pub mod sel {
    pub const NOOP: usize = 0;
    pub const TRANSFER: usize = 1;
    pub const SET_FIELD: usize = 2;
    pub const GRANT_CAP: usize = 3;
    pub const NOTE_SPEND: usize = 4;
    pub const NOTE_CREATE: usize = 5;
    /// Custom cell program dispatch: state flows normally, but domain-specific
    /// constraints are proven externally. The Effect VM binds to the external
    /// proof via `custom_proof_commitment` in the params.
    pub const CUSTOM: usize = 8;
    /// MakeSovereign: transition cell mode_flag from 0 to 1.
    pub const MAKE_SOVEREIGN: usize = 12;
    /// CreateCellFromFactory: record factory VK hash + provenance.
    pub const CREATE_CELL_FROM_FACTORY: usize = 13;
    /// RevokeCapability: remove a capability slot from the c-list Merkle root.
    /// Mirrors GRANT_CAP but binds the slot's hash instead of a new cap_entry.
    pub const REVOKE_CAPABILITY: usize = 24;
    /// EmitEvent: stateless side-effect; commits an event hash to effects_hash
    /// but does not modify any state column (balance, fields, cap_root all
    /// pass through unchanged; nonce increments like any non-NoOp effect).
    pub const EMIT_EVENT: usize = 25;
    /// SetPermissions: update the cell's permission table. The VM doesn't
    /// model permissions in its state columns (they live in the cell's
    /// off-trace manifest), so the AIR enforces state-passthrough and binds
    /// a hash of the new permissions into effects_hash.
    pub const SET_PERMISSIONS: usize = 26;
    /// SetVerificationKey: update the cell's circuit/predicate VK. Like
    /// SET_PERMISSIONS, the VK lives outside the VM trace, so the AIR
    /// enforces full state passthrough and the new VK hash is bound into
    /// effects_hash.
    pub const SET_VERIFICATION_KEY: usize = 27;
    /// RefreshDelegation: bump the cell's delegation epoch. No VM state
    /// columns track the epoch directly, so this is a passthrough variant
    /// (the epoch lives off-trace); the selector alone records the intent.
    pub const REFRESH_DELEGATION: usize = 29;
    /// RevokeDelegation: invalidate a child cell's delegation snapshot.
    /// State passthrough; child_hash binds the target into effects_hash.
    pub const REVOKE_DELEGATION: usize = 30;
    /// CreateCell: actor records the creation of a new cell. The actor's own
    /// state doesn't change (CreateCell rejects non-zero initial balance via
    /// executor check). Passthrough; create_hash binds (pk, token_id, balance).
    pub const CREATE_CELL: usize = 31;
    /// SpawnWithDelegation: actor spawns a child with a delegation snapshot.
    /// Actor's state passthrough; spawn_hash binds (child_pk, child_token_id,
    /// max_staleness) into effects_hash.
    pub const SPAWN_WITH_DELEGATION: usize = 32;
    /// ExerciseViaCapability: invoke a cap from the actor's c-list. The
    /// inner_effects act on the TARGET cell, not the actor; from the actor's
    /// perspective this is a passthrough that records (cap_slot,
    /// hash(inner_effects)).
    pub const EXERCISE_VIA_CAPABILITY: usize = 34;
    /// Introduce: 3-party introduction; introducer's state doesn't change.
    pub const INTRODUCE: usize = 35;
    /// PipelinedSend: dispatch a future action against an EventualRef. The
    /// dispatching cell's state doesn't change (the dispatch is deferred);
    /// passthrough with hash(target ‖ action_hash).
    pub const PIPELINED_SEND: usize = 36;
    /// Mint: the DEDICATED cap-gated SUPPLY-CREATION verb (SUPPLY-MODEL.md
    /// Stage 2b). Balance credit at `param1` (mirror BridgeMint's body), but on
    /// its OWN selector column so a supply-mint proves + self-verifies under a
    /// dedicated selector rather than riding `BRIDGE_MINT`'s slot. Repurposes
    /// the dissolved `ExportSturdyRef` retired index (14) — the IR-2 live path
    /// never pinned that column against any other descriptor, so giving Mint
    /// this index shifts no absolute column. The Lean twin is
    /// `EffectVmEmit.sel.MINT` (= 14); the rotated descriptor is
    /// `supplyMintVmDescriptor2R24` (`EffectVmEmitRotationV3.supplyMintV3`).
    pub const MINT: usize = 14;
    /// GrainTurn: the single-tick multi-field grain turn (initiative 10) — one executor turn on
    /// the grain worker cell as one row (slots 3..=7 written, `turn.fee` debited, ONE nonce tick).
    /// Repurposes the FIRST retired index (6), the [`MINT`] precedent: no live descriptor ever
    /// referenced column 6 (`unforced_pi_pin_census.rs::retired_selector_columns_are_referenced_by_nothing`
    /// measured it), so giving it a meaning shifts no absolute column. Lean twin
    /// `EffectVmEmitGrainTurn.SEL_GRAIN_TURN = 6`; the rotated member is
    /// `grainTurnVmDescriptor2R24`.
    pub const GRAIN_TURN: usize = 6;
    /// BridgeMint: actor mints tokens carried by a portable proof from
    /// another federation. Balance credit (mirror NoteSpend). The SHIELD verb —
    /// the one bridge variant that survives the lockstep.
    pub const BRIDGE_MINT: usize = 40;
    /// Burn: explicit, non-conservation balance reduction. Distinct from
    /// `TRANSFER` with `direction == 1` (no destination credit) and from
    /// `NOTE_CREATE` (no commitment hidden in the row). The AIR pins
    /// `was_burn_flag == 1` and binds the target via params[0].
    pub const BURN: usize = 46;
    /// CellDestroy: permanently retire a cell. Lifecycle lives off-trace
    /// but the AIR binds both `target_hash` (params[0]) and
    /// `death_certificate_hash` (params[1]) into effects_hash, distinct
    /// from any SetPermissions alias.
    pub const CELL_DESTROY: usize = 47;
    /// AttenuateCapability: narrow an existing c-list slot's commitment.
    /// Distinct from REVOKE_CAPABILITY: revoke folds a `slot_hash` into
    /// cap_root in a single step; attenuate folds a 2-of-2 leaf
    /// `hash_2_to_1(cap_slot_hash, narrower_commitment)` into cap_root.
    pub const ATTENUATE_CAPABILITY: usize = 48;
    /// CellSeal: transition a cell lifecycle to `Sealed`. State passthrough;
    /// `target_hash` (params[0]) and `reason_hash` (params[1]) bind the
    /// cell and rationale into effects_hash (domain tag 49).
    pub const CELL_SEAL: usize = 49;
    /// CellUnseal: reverse a cell seal (`Sealed` → `Live`). State passthrough;
    /// `target_hash` (params[0]) binds the cell (domain tag 50). One param
    /// vs. CellSeal's two makes the two variants algebraically distinct.
    pub const CELL_UNSEAL: usize = 50;
    /// ReceiptArchive: summarize the cell's receipt-chain prefix. State
    /// passthrough; `target_hash` (params[0]), `archive_end_height`
    /// (params[1]), and `terminal_receipt_hash` (params[2]) all fold into
    /// effects_hash (domain tag 51).
    pub const RECEIPT_ARCHIVE: usize = 51;
    /// Refusal: evidence-of-absence. State passthrough; `target_hash`
    /// (params[0]) and `reason_hash` (params[1]) bind the refusing cell and
    /// commitment+reason discriminant into effects_hash (domain tag 52).
    pub const REFUSAL: usize = 52;
    /// IncrementNonce: explicit runtime nonce bump. State passthrough except
    /// for the global nonce tick; selector alone binds intent.
    pub const INCREMENT_NONCE: usize = 53;

    /// The 24 RETIRED selector columns (VERB-LOCKSTEP). Their effects no
    /// longer exist as `Effect` variants — escrow ×6 (37, 39, 42..46 less
    /// the survivors), obligation ×3 (6, 7, 9), field-seal pair ×3 (10, 11,
    /// 28), caps-in-slots/CapTP ×4 (14..18), queue ×6 (18..24), bridge
    /// lock/finalize/cancel ×3 (33, 38, 41).
    ///
    /// ⚑ **CORRECTED 2026-07-30.** This doc used to say "the AIR pins each of
    /// these columns to ZERO on every row, so a trace claiming a doomed effect
    /// is UNSATISFIABLE — the kernel's refusal is structural in-circuit". It is
    /// not: MEASURED over all 117 emitted members, these 24 columns are
    /// referenced by **zero** constraints, so nothing pins them and nothing
    /// refuses a non-zero one. They are safe because they are INERT — no gate,
    /// lookup, mem/map op, hash site, range tooth or PI pin reads them, so a
    /// non-zero value there reaches nothing. `retired_selector_columns_are_
    /// referenced_by_nothing` in `circuit/tests/unforced_pi_pin_census.rs` is
    /// that measurement, and it uses THIS list as its input — the constant is
    /// load-bearing for the gate rather than decorative.
    ///
    /// The columns are kept until the Lean-emitter relayout lane regenerates
    /// the frozen descriptors against a compacted 30-selector layout.
    ///
    /// Index ↔ retired effect (index 14, the dissolved `ExportSturdyRef`, was
    /// REPURPOSED for the dedicated supply [`MINT`] selector, SUPPLY-MODEL.md
    /// Stage 2b — it is no longer pinned to zero; index 6, the dissolved
    /// `CreateObligation`, was REPURPOSED for [`GRAIN_TURN`], initiative 10):
    ///   7  FulfillObligation   9  SlashObligation
    ///   10 Seal                  11 Unseal
    ///   15 EnlivenRef            16 DropRef             17 ValidateHandoff
    ///   18 AllocateQueue         19 EnqueueMessage      20 DequeueMessage
    ///   21 ResizeQueue           22 AtomicQueueTx       23 PipelineStep
    ///   28 CreateSealPair        33 BridgeCancel        37 CreateEscrow
    ///   38 BridgeLock            39 CreateCommittedEscrow
    ///   41 BridgeFinalize        42 ReleaseEscrow       43 RefundEscrow
    ///   44 ReleaseCommittedEscrow 45 RefundCommittedEscrow
    pub const RETIRED_SELECTORS: [usize; 23] = [
        7, 9, 10, 11, 15, 16, 17, 18, 19, 20, 21, 22, 23, 28, 33, 37, 38, 39, 41, 42, 43, 44, 45,
    ];
}

/// State column offsets (relative to state start).
pub mod state {
    pub const BALANCE_LO: usize = 0;
    pub const BALANCE_HI: usize = 1;
    pub const NONCE: usize = 2;
    pub const FIELD_BASE: usize = 3; // fields[0..8] at offsets 3..11
    pub const CAP_ROOT: usize = 11;
    pub const STATE_COMMIT: usize = 12;
    pub const RESERVED: usize = 13;
    pub const SIZE: usize = 14;

    /// **How many developer field lanes the deployed EffectVM state block carries.**
    ///
    /// DERIVED from the block layout (`CAP_ROOT − FIELD_BASE`), never re-typed as a
    /// literal `8`: the field octet is exactly the span between the last scalar before
    /// it and the cap-root limb, so a layout move cannot leave this number behind.
    ///
    /// It is NOT `dregg_cell::state::STATE_SLOTS` (16), and the gap is real, not a
    /// stale widening left half-done. A cell holds 16 indexed slots; the EffectVM row
    /// carries the first EIGHT of them as columns, and `fields[8..STATE_SLOTS]` folds
    /// into the authority residue (`record_digest` — see `cell_state.rs`'s
    /// `record_digest` doc and `cell/src/commitment.rs`'s `st.fields[8..STATE_SLOTS]`
    /// loop) rather than into a state-block column. The Lean that AUTHORS the AIR types
    /// the bound as `Fin 8`
    /// (`metatheory/Dregg2/Circuit/Emit/EffectVmEmitSetField.lean::setFieldVmDescriptor`,
    /// `gOtherFieldsAll`'s `List.range 8`, `RowEncodesSF`'s `∀ i : Fin 8`), and the
    /// Lean-emitted layout manifest publishes the same octet width
    /// (`layout_generated::CUSTOM_APP_FIELD_OCTET_LEN`). Both are pinned against this
    /// constant by `circuit/tests/setfield_air_lane_bound_pin.rs`.
    ///
    /// So this is a REAL CEILING on what the deployed AIR can attest, not a literal to
    /// raise. Raising it without moving the Lean is a wrong proof, not a wider one.
    pub const NUM_FIELDS: usize = CAP_ROOT - FIELD_BASE;
}

/// Absolute column indices for state_before.
pub const STATE_BEFORE_BASE: usize = NUM_EFFECTS; // selector count after IncrementNonce
/// Absolute column indices for state_after.
pub const STATE_AFTER_BASE: usize = STATE_BEFORE_BASE + state::SIZE + NUM_PARAMS; // 54 + 14 + 8 = 76
/// Effect parameter base column.
pub const PARAM_BASE: usize = STATE_BEFORE_BASE + state::SIZE; // 54 + 14 = 68
/// Number of parameter columns.
pub const NUM_PARAMS: usize = 8;
/// Auxiliary witness base column.
pub const AUX_BASE: usize = STATE_AFTER_BASE + state::SIZE; // 76 + 14 = 90
/// Number of auxiliary columns.
/// Stage 1: 12 (8 effect-aux + 3 state intermediates + 1 custom-count acc).
/// Stage 2: 23 (+ 8 reserved bits + 1 mode flag + 2 retired ResizeQueue slots).
/// Sovereign-witness teeth: 28 (+ 4 WITNESS_KEY_COMMIT + 1 WITNESS_SEQUENCE).
/// γ.2 federation+owner binding (#131/#132): 36 (+ 4 FEDERATION_ID + 4 OWNER_CELL_ID).
/// W9-RANGECHECK: 96 (+ 30 NEW_BAL_LO_BIT + 30 NEW_BAL_HI_BIT).
/// P0-2 record-digest: 97 (+ 1 STATE_RECORD_DIGEST — the authority-residue limb
/// absorbed as the fourth state-commit root input, replacing the literal ZERO).
/// Light-client conservation: 98 (+ 1 ASSET_CLASS — the row-0 aux column pinned
/// to PI[v3::ASSET_CLASS], binding the per-cell asset class into the proof).
pub const NUM_AUX: usize = 98;

/// Bit-width of each balance limb's v1-face boolean decomposition.
///
/// ⚑ **THE UNDERFLOW ARGUMENT THAT USED TO BE WRITTEN HERE WAS FALSE, AND THE MECHANISM IT
/// CREDITED IS NOT IN THE DEPLOYED CIRCUIT.** Both halves of that are worth stating, because
/// either one alone would have left the next reader with a working lemma.
///
/// It read: *"A debit whose modular subtraction underflowed (`old - amount` ≡ p - k) would land
/// at a field element ≥ 2^30 that has no 30-bit boolean decomposition — the recomposition
/// constraint then fails, so the STARK rejects the wrap in-circuit."*
///
/// **1. It is false on 12.5% of its own band.** `p = 2013265921 ≈ 2^30.907`, so `p - k < 2^30`
/// exactly when `k > p - 2^30 = 939524097`. For every `k ∈ [939524098, 2^30)` the underflowed
/// element IS below `2^30`, DOES have a 30-bit decomposition, and a 30-bit range obligation
/// ACCEPTS it. Since both limbs are `< 2^30`, the difference `k = amount_limb - old_limb` ranges
/// over all of `[0, 2^30)`, so the admitted band is `134217726` values reached by an ordinary
/// over-debit — not a corner. Proved both directions, `#assert_axioms`-clean, at
/// `Dregg2.Circuit.RangeFieldContainment.underflow_admitted_at_30_iff` (and at this constant, as
/// `deployed_underflow_admitted_iff`). 29 is the last wrap-free width (`wrap_free_iff_le_29`);
/// at 29 the band is EMPTY (`no_underflow_admitted_at_29`), which is why narrowing would have
/// closed it rather than merely shrunk it.
///
/// **2. The 60 boolean columns this constant sizes are DEAD on every deployed member.** They are
/// `AUX_BASE + NEW_BAL_LO_BIT_BASE` = absolute column 126 and `+ NEW_BAL_HI_BIT_BASE` = 156, and
/// every wide-registry member's E1 kill-set deletes the run `(101, 186)` — see
/// `e1_compact_generated::E1_COMPACT_TABLE`. `helpers::fill_balance_limb_bits` still writes them
/// and `trace_rotated::compact_e1_columns` then drops them. So the recomposition constraint the
/// old comment leaned on is not merely too weak; it is not there.
///
/// # What actually stops an over-debit
///
/// A **15-bit schoolbook borrow chain with a no-final-borrow gate**, in the availability weld —
/// not a range proof on the post-state limb. On the deployed transfer member
/// (`transferVmDescriptor2R24`, row 1 of `descriptors/rotation-wide-registry-staged.tsv`) the
/// gates are, with `c54` = pre-balance lo, `c68` = amount, `c69` = direction, `c76` = post lo:
///
/// ```text
///   [36] c54 = c94 + 2^15·c95        [37] c76 = c96 + 2^15·c97
///   [38] c68 = c98 + 2^15·c99        ← the AMOUNT is decomposed and range-checked too
///   [39] c100²= c100                 [40] c101² = c101          (borrow bits boolean)
///   [41] c69·(c94 − c98 + 2^15·c100 − c96) = 0
///   [42] c69·(c95 − c99 − c100 + 2^15·c101 − c97) = 0
///   [43] c69·c101 = 0                ← THE NO-FINAL-BORROW GATE ⟹ amount ≤ pre-balance
/// ```
///
/// with all six limbs `c94..c99` range-checked to 15 bits by lookups 184–189 against table 84
/// (`range_w15`). The final borrow being pinned to zero makes `post = pre − amount` exact over ℤ,
/// so no wrapped value is representable in the first place — the containment does not depend on
/// the width of the post-state range at all. Burn carries the same chain UNGATED (debit-only);
/// `transferFee` carries ten such lookups for the fee leg. Exactly five deployed members declare
/// table 84, and they are exactly the five that debit a balance: rows 1, 2, 43, 45, 46. Every
/// other member either pins `c76 = c54` (balance untouched) or is a credit (`mint`,
/// `supplyMint`: `c76 = c54 + amount`, carry-chained at `[44]..[48]`).
///
/// The Lean side of that gate is `RotatedKernelRefinementMintBurnAvail` / `KernelConfigSoundness‑
/// Avail` over the `RfixAvail` registry, whose debiting tags discharge availability.
///
/// So: **the conclusion "the deployed circuit rejects the wrap" survives; the stated reason for
/// it did not.** The 30-bit obligation that IS live on the deployed member is a `table 2` lookup
/// on `c76`/`c77` (constraints 182/183) bounding the limb — useful, but it is not what refuses an
/// over-debit, and on its own it would admit the band above.
///
/// ⚠ Do not re-derive an underflow argument from this constant. If a NEW balance-debiting member
/// is added, it needs the borrow chain; a 30-bit range on its post-state limb will not do the
/// job, and `underflow_admitted_at_30_iff` is the counterexample generator.
pub const BAL_LIMB_BITS: usize = 30;

/// Auxiliary column offsets for state commitment tree intermediates.
pub mod aux_off {
    /// Intermediate 1: hash_4_to_1(balance_lo, balance_hi, nonce, field[0])
    pub const STATE_INTER1: usize = 8;
    /// Intermediate 2: hash_4_to_1(field[1], field[2], field[3], field[4])
    pub const STATE_INTER2: usize = 9;
    /// Intermediate 3: hash_4_to_1(field[5], field[6], field[7], cap_root)
    pub const STATE_INTER3: usize = 10;
    /// Stage 1: cumulative count of `s_custom == 1` rows up to and including
    /// this row.
    ///
    /// ⚠ **NOT PINNED TO ANYTHING, MEASURED 2026-08-06.** This said
    /// "Boundary-pinned at last row to `PI[CUSTOM_EFFECT_COUNT]` (sum-check, per
    /// `DESIGN-max-custom-effects.md` §6 step 3)". The column is DECLARED here and
    /// FILLED by the trace generator, and that is all: **no constraint anywhere
    /// references it** (three tree-wide hits — this const, one comment, the fill),
    /// the v1 hand-AIR `eval_constraints` that was to host the sum-check is
    /// retired, and the registries carried zero `pi_binding`s at that index. The PI
    /// slot it was said to be pinned to no longer exists — deleted 2026-08-07,
    /// `docs/PI-DISPOSITION.md` §6. THIS COLUMN IS THE REMAINING HALF OF THE SAME
    /// DEBT: a filled column no constraint reads is prover-chosen padding, and
    /// removing it moves the trace GEOMETRY (a second, separable flag day), which is
    /// why the seven-slot PI compaction did not take it.
    pub const CUSTOM_COUNT_ACC: usize = 11;
    /// Stage 2 (sealing honesty): bit-decomposition of `old_reserved`.
    /// `old_reserved == Σ_{i=0..7} bi * 2^i + mode * 256`, with each bi
    /// and mode boolean. Combined with a Lagrange-basis selection on
    /// `field_idx`, this yields an algebraically bound `bit_at_idx` that
    /// the SetField constraint can check against — closing the
    /// AUDIT[stage2-setfield-sealed-witness] hole.
    pub const RESERVED_BIT_0: usize = 12;
    pub const RESERVED_BIT_1: usize = 13;
    pub const RESERVED_BIT_2: usize = 14;
    pub const RESERVED_BIT_3: usize = 15;
    pub const RESERVED_BIT_4: usize = 16;
    pub const RESERVED_BIT_5: usize = 17;
    pub const RESERVED_BIT_6: usize = 18;
    pub const RESERVED_BIT_7: usize = 19;
    pub const RESERVED_MODE: usize = 20;

    // ---- Sovereign-witness AIR teeth (SOVEREIGN-WITNESS-AIR-DESIGN.md) ----
    /// 4-felt Poseidon2 hash of the sovereign witness's owning pubkey,
    /// row-0-pinned to PI[SOVEREIGN_WITNESS_KEY_COMMIT_BASE..+4].
    /// Zero sentinel on every row for non-sovereign proofs. The boundary
    /// constraint binds row 0; later rows are free (the gate is at row 0
    /// only — the witness identity is a property of the turn, not of
    /// individual effects).
    pub const WITNESS_KEY_COMMIT_0: usize = 23;
    pub const WITNESS_KEY_COMMIT_1: usize = 24;
    pub const WITNESS_KEY_COMMIT_2: usize = 25;
    pub const WITNESS_KEY_COMMIT_3: usize = 26;
    /// Per-cell monotonic sequence counter, row-0-pinned to
    /// PI[SOVEREIGN_WITNESS_SEQUENCE]. Zero sentinel for non-sovereign proofs.
    pub const WITNESS_SEQUENCE: usize = 27;

    // ---- γ.2 follow-up (#131/#132): per-cell federation + owner binding ----
    /// 4-felt Poseidon2 compression of the 32-byte federation id this proof
    /// was minted under. Row-0-pinned to PI[FEDERATION_ID_BASE..+4]. Every
    /// row carries the same value (it is a property of the turn's federation,
    /// not of individual effects); the boundary constraint binds row 0.
    /// A proof minted under federation A cannot satisfy the row-0 binding
    /// when checked against federation B's reconstructed PI.
    pub const FEDERATION_ID_0: usize = 28;
    pub const FEDERATION_ID_1: usize = 29;
    pub const FEDERATION_ID_2: usize = 30;
    pub const FEDERATION_ID_3: usize = 31;
    /// 4-felt Poseidon2 compression of the 32-byte owner cell id whose state
    /// transition this proof attests. Row-0-pinned to PI[OWNER_CELL_ID_BASE..+4].
    /// Binds the proof to a specific owner cell so a proof for owner cell X
    /// cannot be substituted for owner cell Y.
    pub const OWNER_CELL_ID_0: usize = 32;
    pub const OWNER_CELL_ID_1: usize = 33;
    pub const OWNER_CELL_ID_2: usize = 34;
    pub const OWNER_CELL_ID_3: usize = 35;

    // ---- W9-RANGECHECK: in-circuit balance-limb range / underflow proof ----
    /// Base offset (within AUX) of the 30 boolean columns decomposing
    /// `state_after.balance_lo` — absolute column `AUX_BASE + 36` = 126.
    ///
    /// ⚑ **DEAD ON EVERY DEPLOYED MEMBER, AND THE CLAIM THAT USED TO BE HERE WAS FALSE ANYWAY.**
    /// This said the two constraints "prove `balance_lo ∈ [0, 2^30)` IN-circuit and, because a
    /// wrapped (underflowed) debit lands ≥ 2^30, reject the wrap directly". A wrapped debit does
    /// NOT always land ≥ 2^30: `p - k < 2^30` for every `k > 939524097`, so a 30-bit
    /// decomposition accepts an underflow of any such magnitude
    /// (`RangeFieldContainment.underflow_admitted_at_30_iff`). And the columns are deleted from
    /// every wide member by the E1 kill-set run `(101, 186)`
    /// (`e1_compact_generated::E1_COMPACT_TABLE`), so no deployed constraint reads them.
    ///
    /// What actually refuses an over-debit is the 15-bit borrow chain with a no-final-borrow
    /// gate; see the note on [`super::BAL_LIMB_BITS`] for the deployed gate list.
    pub const NEW_BAL_LO_BIT_BASE: usize = 36;
    /// Base offset of the 30 boolean columns decomposing `state_after.balance_hi` — absolute
    /// column 156. Same two constraints as the lo limb, and equally dead (same kill-set run).
    pub const NEW_BAL_HI_BIT_BASE: usize = 36 + super::BAL_LIMB_BITS; // 66

    /// The `record_digest` witness column (audit P0-2): the single Poseidon2 felt
    /// folding ALL authority-bearing cell state the welded state limbs do NOT carry
    /// (permissions / VK / lifecycle / deathCert / delegate / delegation / program /
    /// mode / visibility / side-table roots / `fields[8..]`). The Group-4 state-commit
    /// constraint absorbs it as the FOURTH input of the root hash
    /// (`state_commit == hash_4_to_1(inter1, inter2, inter3, record_digest)`),
    /// replacing the old literal `ZERO` so the commitment binds the FULL cell state.
    /// A residue-free cell witnesses `empty_record_digest()` (`ZERO`) — the no-op
    /// fold, byte-identical to the legacy form. Mirrors the Lean `recStateCommit`'s
    /// `RH` rest-hash limb / `cellCommitS`'s `systemRootsDigest` absorbed limb.
    pub const STATE_RECORD_DIGEST: usize = 96;

    /// Light-client conservation: the per-cell ASSET CLASS (the folded committed
    /// `token_id`), written into row 0 and row-0-pinned to `PI[v3::ASSET_CLASS]`
    /// by a boundary constraint. The proof thereby COMMITS to its asset class so
    /// the per-asset cross-cell conservation gate can partition each proof's
    /// NET_DELTA by the PI-bound class — enforcing per-asset Σδ=0 WITHOUT a
    /// ledger. Zero sentinel = the native / computron asset. Like
    /// FEDERATION_ID/OWNER_CELL_ID, the binding is at row 0 only (the asset class
    /// is a property of the cell, not of individual effect rows).
    pub const ASSET_CLASS: usize = 97;
}

/// THE ROTATED STATE BLOCK (THE ROTATION, STAGED — `.docs-history-noclaude/UNIVERSAL-MAP-ROTATION.md`
/// §2.1/§2.4/§2.6, cutover = `.docs-history-noclaude/ROTATION-CUTOVER.md`).
///
/// NOTHING on the live wire path reads these: the live layout above (186-wide,
/// 14-slot state block) stays byte-identical until the one VK flag-day. These
/// constants mirror the LEAN-EMITTED staged layout — the Lean twin is
/// `metatheory/Dregg2/Circuit/Emit/EffectVmEmitRotation.lean`, whose
/// `rotationLayoutManifest` is byte-pinned both there (`#guard`) and here
/// (`rotation_layout_matches_lean` in `effect_vm_descriptors.rs` rebuilds the
/// manifest from THESE constants and compares against the committed
/// `circuit/descriptors/rotation-layout-v3-staged.json`). Rust never invents a
/// layout fact (law #1 of the rotation spec).
///
/// The block is the rotated `recStateCommit` payload, ABSORPTION-ORDERED
/// (`RotatedLimbs.toList`): cells root · the 16 named registers · the map
/// roots adjacent and uniform (cap, nullifier, heap) · lifecycle · epoch ·
/// committed height · the receipt-index MMR root literally LAST · then the
/// commitment carrier. The commitment is the 4-ary CHAINED chip absorption
/// (8 permutation sites; Lean `wireCommit`, keystone `wireCommit_binds`).
/// NOTE the obsolete 186-wide fan-out is deliberately NOT widened to carry
/// this block (the post-LogUp main table is far thinner — `EPOCH-DESIGN.md`);
/// the staged probe trace is the block + chain carriers alone, and the
/// flag-day descriptor regen decides the final main-table packing.
pub mod rotation {
    /// The cells-root limb column.
    pub const CELLS_ROOT: usize = 0;
    /// Register `i` at `REG_BASE + i`, `i < NUM_REGISTERS`.
    pub const REG_BASE: usize = 1;
    /// The rotated register-file width (8 → 16; `RotationLayout.NUM_REGISTERS`).
    pub const NUM_REGISTERS: usize = 16;
    /// The cap-map root limb column.
    pub const CAP_ROOT: usize = 17;
    /// The nullifier-map root limb column.
    pub const NULLIFIER_ROOT: usize = 18;
    /// The heap-map root limb column (§2.4 — the rotation's `heap_root` limb).
    pub const HEAP_ROOT: usize = 19;
    /// The lifecycle scalar limb column.
    pub const LIFECYCLE: usize = 20;
    /// The epoch scalar limb column.
    pub const EPOCH: usize = 21;
    /// The committed-height scalar limb column (§2.6 — the PI-v3 limb).
    pub const COMMITTED_HEIGHT: usize = 22;
    /// The receipt-index MMR root carrier (`iroot = mroot log`), absorbed LAST.
    pub const IROOT: usize = 23;
    /// The rotated state commitment carrier (the chained absorption's digest).
    pub const STATE_COMMIT: usize = 24;
    /// The rotated state block width: 23 limbs + iroot + state_commit.
    pub const BLOCK_SIZE: usize = 25;
    /// The chained-absorption intermediate-digest carriers (one per non-final site).
    pub const CHAIN_BASE: usize = 25;
    /// Number of chain carriers (9 sites — 7 arity-4 + 2 arity-2 (the deployed chip
    /// pins arity ∈ {2,4}; the arity-2 tail keeps the iroot LITERALLY LAST) — with
    /// the final digest on `STATE_COMMIT`).
    pub const NUM_CHAIN: usize = 8;
    /// The staged probe trace width: the rotated block + the chain carriers.
    pub const PROBE_WIDTH: usize = 33;
    /// The chip absorption arity of the chained realization's body sites.
    pub const CHAIN_ARITY: usize = 4;

    /// THE WIDENED CAVEAT OPERAND (staged — the second rotation wire-shape
    /// pre-gate, `.docs-history-noclaude/ROTATION-CUTOVER.md` §3). The live `SlotCaveatEntry`
    /// operand is `slot_index: u8` — slot-only; the rotated operand is
    /// `(domain_tag, key)` on the universal-memory `UDomain` wire codes
    /// (registers 0 · heap 1 — `turn/src/umem.rs`), key widened `u8 → felt`
    /// so capability attenuation reaches HEAP KEYS. Lean twin:
    /// `Dregg2/Circuit/Emit/EffectVmEmitRotationCaveat.lean` (the no-aliasing
    /// keystone `caveat_operand_no_aliasing`: a slot operand and a heap
    /// operand can NEVER collide — domain separation as a theorem); the
    /// byte-pin twin test is `rotation_caveat_layout_matches_lean`
    /// (`effect_vm_descriptors.rs`). Columns are for the staged R=24 probe
    /// (the CONFIRMED register count): the rotation R=24 part occupies
    /// `0..43` (`rotation_layout_for(24)`), the caveat manifest block and
    /// its chain follow.
    pub mod caveat {
        /// The staged probe's register count (CONFIRMED R=24, ember 2026-06-12).
        pub const R: usize = 24;
        /// The caveat manifest block base (= `rotation_layout_for(24).probe_width`).
        pub const BASE: usize = 43;
        /// The caveat count column.
        pub const COUNT_COL: usize = 43;
        /// Entry `i`'s base column: `ENTRY_BASE + i * ENTRY_SIZE`.
        pub const ENTRY_BASE: usize = 44;
        /// Felts per entry: `[type_tag, domain_tag, key, p0, p1, p2, p3]`.
        pub const ENTRY_SIZE: usize = 7;
        /// Maximum caveat entries (unchanged from the live manifest).
        pub const MAX_CAVEATS: usize = 4;
        /// The manifest block width: 1 count + 4 × 7 = 29 felts.
        pub const MANIFEST_SIZE: usize = 29;
        /// The caveat chain carriers (9 — sites 0..8 of the 10-site chain).
        pub const CHAIN_BASE: usize = 72;
        /// Number of caveat chain carriers.
        pub const NUM_CHAIN: usize = 9;
        /// The caveat-commitment carrier (the chain's final digest).
        pub const CAVEAT_COMMIT: usize = 81;
        /// The caveat probe trace width: 43 + 29 + 9 + 1.
        pub const PROBE_WIDTH: usize = 82;
        /// The registers (slot) domain wire code (`UDomain::Registers`).
        pub const DOMAIN_REGISTERS: u32 = 0;
        /// The heap domain wire code (`UDomain::Heap`).
        pub const DOMAIN_HEAP: u32 = 1;
        /// PI slots: published state commit · committed height · caveat commit.
        pub const PUB_COMMIT: usize = 0;
        pub const PUB_HEIGHT: usize = 1;
        pub const PUB_CAVEAT: usize = 2;
    }
}

/// Effect parameter meanings per effect type.
///
/// Transfer:
///   param0 = amount
///   param1 = direction (0=incoming, 1=outgoing)
///
/// SetField:
///   param0 = field_index (0..7)
///   param1 = new_value
///
/// GrantCapability:
///   param0 = capability_entry (recipient-install rows: opaque entry digest;
///            witnessed granter-side delegation rows: the granted CapLeaf's
///            7-field Poseidon2 digest, pinned in-circuit)
///   param1 = direction (0 = recipient install / legacy, 1 = granter-side
///            Phase-B2 delegation row carrying the non-amp gate witness)
///   param2 = held slot_hash (delegation rows only: the granter c-list slot
///            the membership-open authenticates)
///
/// NoteSpend:
///   param0 = nullifier
///   param1 = value_lo
///   param2 = value_hi
///
/// NoteCreate:
///   param0 = commitment
///   param1 = value_lo
///   param2 = value_hi
///
/// Custom (CellProgram dispatch):
///   param0..param3 = custom_program_vk_hash limbs 0..4 (limbs 4..8 ride the
///                    exact VK-teeth columns in `trace_rotated`)
///   param4..param7 = custom_proof_commitment limbs 0..4 (of the 8-felt proof-bind
///                    commitment — flag-day rotation; limbs 4..8 ride the rotated
///                    member's commit-teeth columns, `trace_rotated::CUSTOM_COMMIT_TEETH_BASE`,
///                    and the full 8 felts are bound through the PI layer)
pub mod param {
    pub const AMOUNT: usize = 0;
    pub const DIRECTION: usize = 1;
    pub const FIELD_INDEX: usize = 0;
    pub const NEW_VALUE: usize = 1;
    pub const CAP_ENTRY: usize = 0;
    /// GrantCapability row role: 0 = recipient install (legacy fold), 1 =
    /// granter-side Phase-B2 delegation row (membership-open + non-amp gates).
    /// Legacy traces never write params[1] on grant rows, so the zero default
    /// keeps every pre-B2 grant row on the install semantics unchanged.
    pub const GRANT_DIRECTION: usize = 1;
    /// Delegation rows only: the held (granter c-list) slot_hash the
    /// membership-open authenticates; pinned in-circuit to the witness.
    pub const GRANT_HELD_SLOT_HASH: usize = 2;
    pub const NULLIFIER: usize = 0;
    pub const NOTE_VALUE_LO: usize = 1;
    pub const NOTE_VALUE_HI: usize = 2;
    /// BridgeMint/Mint rows: the mint identity at `param0`. For BridgeMint this
    /// is the FELT-DOMAIN `note_spend_mint_hash_felt` (the Poseidon2 identity
    /// over the six felts the executor's note-spend STARK verify binds —
    /// `dsl::note_spending::bridge_mint_hash_felt`), published at rotated
    /// PI 46 by the mint-hash pin (Lean `mintV3BridgeHash`). Supply-mint rows
    /// carry the (target, slot) byte-domain fold here (no pin).
    pub const MINT_HASH: usize = 0;
    pub const NOTE_COMMITMENT: usize = 0;
    // CreateCellFromFactory params.
    pub const FACTORY_VK_HASH: usize = 0;
    pub const CHILD_VK_DERIVED: usize = 1;
    // Custom cell program dispatch params.
    /// Low four limbs of the 8-felt VK hash identifying the custom program.
    /// The high four are trace-carried at `trace_rotated::CUSTOM_VK_TEETH_BASE`.
    pub const CUSTOM_VK_HASH_BASE: usize = 0;
    /// Custom proof commitment limbs 0..4 (the param union carries only the low
    /// half of the 8-felt rotated commitment; limbs 4..8 ride the commit-teeth
    /// columns past the member host width — see `trace_rotated::CUSTOM_COMMIT_TEETH_BASE`).
    pub const CUSTOM_PROOF_COMMIT_BASE: usize = 4;
    // Burn params (near-miss aliasing closure, #100 follow-up).
    /// Hash of the target cell whose balance is reduced.
    pub const BURN_TARGET: usize = 0;
    /// Burn amount (low 30 bits). Constraints subtract from balance_lo.
    pub const BURN_AMOUNT_LO: usize = 1;
    /// Disclosure flag — constrained to 1 on any Burn row so that a
    /// verifier replaying the trace cannot confuse this with a
    /// Transfer-direction-1 row.
    pub const BURN_WAS_BURN_FLAG: usize = 2;
    // CellDestroy params (near-miss aliasing closure).
    /// Hash of the cell being destroyed.
    pub const CELL_DESTROY_TARGET: usize = 0;
    /// `DeathCertificate::certificate_hash()` truncated into a BabyBear.
    pub const CELL_DESTROY_CERT_HASH: usize = 1;
    // AttenuateCapability params (near-miss aliasing closure).
    /// Hash of the c-list slot being narrowed.
    pub const ATTN_CAP_SLOT_HASH: usize = 0;
    /// Commitment to the new (narrower) permissions / facet / expiry.
    pub const ATTN_NARROWER_COMMITMENT: usize = 1;
    // CellSeal params (AIR-impl lane #119, selector 49).
    /// Hash of the cell being sealed.
    pub const CELL_SEAL_TARGET: usize = 0;
    /// BLAKE3 of the sealing reason (cleartext off-chain).
    pub const CELL_SEAL_REASON_HASH: usize = 1;

    // CellUnseal params (AIR-impl lane #119, selector 50).
    /// Hash of the cell being unsealed.
    pub const CELL_UNSEAL_TARGET: usize = 0;

    // ReceiptArchive params (AIR-impl lane #119, selector 51).
    /// Hash of the cell being archived.
    pub const RECEIPT_ARCHIVE_TARGET: usize = 0;
    /// `archive_end_height` as BabyBear (low-30-bit truncation of the u64).
    pub const RECEIPT_ARCHIVE_END_HEIGHT: usize = 1;
    /// BLAKE3 of the terminal receipt at `archive_end_height`.
    pub const RECEIPT_ARCHIVE_TERMINAL_HASH: usize = 2;

    // Refusal params (AIR-impl lane #119, selector 52).
    /// Hash of the cell issuing the refusal.
    pub const REFUSAL_TARGET: usize = 0;
    /// Reason-encoded binding: `discriminant ^ trunc(offered_action_commitment)`.
    pub const REFUSAL_REASON_HASH: usize = 1;
}
