//! # `effect_vm_descriptors` — the Lean-emitted EffectVM descriptor REGISTRY.
//!
//! This is the foundation for the EffectVM circuit cutover: a registry of every
//! verified-by-construction `EffectVmDescriptor` that Lean's `emitVmJson` renders,
//! embedded here as committed JSON and keyed by the running prover's per-effect
//! **selector index** (`effect_vm::columns::sel`). The descriptor interpreter
//! (`lean_descriptor_air::parse_vm_descriptor` + `EffectVmDescriptorAir`) ingests
//! the selected JSON to drive the verified circuit for that effect.
//!
//! ## Provenance (the descriptor is a Lean-emitted cache)
//!
//! Each `*.json` under `circuit/descriptors/` is the output of the Lean
//! executable `Dregg2/Circuit/Emit/EmitAllJson.lean` (run via
//! `lake env lean --run`), which imports every `EffectVmEmit<Effect>.lean` module
//! and prints `<def>\t<name>\t<emitVmJson desc>`. The JSON is NOT hand-written —
//! Lean is the source of truth and the checked-in JSON is a CACHE of its emission.
//!
//! The actual Lean↔JSON drift gate is GENERATE-FRESH: `scripts/check-descriptor-drift.sh`
//! re-runs the Lean emitters and diffs the result against the checked-in artifacts.
//! That is the only check that can catch a re-emit changing a gate, because it
//! re-derives from Lean. The `*_FP` SHA-256 constants are cache-freshness pins the
//! emit script (re)writes alongside the JSON — `sha256(bytes) == FP` proves only
//! that a file matches the hash committed next to it (self-consistency), NOT that
//! the bytes still equal the current Lean emission. The tests below verify the real
//! property — that each descriptor PARSES through `parse_vm_descriptor` into the
//! structure the prover consumes — not the FP tautology.
//!
//! ## Coverage (HONEST)
//!
//! 26 UNIQUE descriptors are registered (VERB-LOCKSTEP: the 22 descriptors of
//! the factory-dissolved families — escrow/obligation-adjacent legs, the queue
//! family, seal/unseal/seal-pair, the swiss/sturdyref/handoff family, bridge
//! lock/finalize/cancel — died with their `Effect` variants; their semantics
//! are the factory-cell story). The `attenuateA` cap-root-move object is
//! SHARED by attenuate / delegate (ATTENUATE_CAPABILITY=48, GRANT_CAP=3);
//! `revokeDelegation-v2` / `introduce-v2` carry their OWN frozen-frame +
//! nonce-TICK descriptors, and the cap-table semantics are bound OFF-row via
//! each module's universe-A connector.
//!
//!   * `SELECTOR_DESCRIPTORS`: 25 of the 29 LIVE EffectVM selectors carry a
//!     descriptor (the 4 others — NOOP, SET_FIELD, CUSTOM, CELL_UNSEAL — have no
//!     emit module yet; REVOKE_CAPABILITY (24) GRADUATED via the cap-crown v1
//!     face `dregg-effectvm-revokecapability-v1`). Two selectors (3/48 cap moves)
//!     point at the shared `attenuateA` JSON.
//!
//!   * `NAME_ONLY_DESCRIPTORS`: 1 verified descriptor (`mint`) whose effect has
//!     NO dedicated Rust selector (supply mint, distinct from BRIDGE_MINT).
//!     (The RECORD-LAYER STAGE 2 `record` descriptor is registered in
//!     `ALL_DESCRIPTORS` directly — it is the transfer descriptor's `fields_root`-
//!     binding variant, selected by name on a map-write row, not a new selector.)
//!
//! ## PARTIAL / IR-BLOCKED descriptors (registered honestly)
//!
//! Several descriptors are the **economic-leg only** projection of an effect whose
//! full semantics touch an off-trace surface the per-row EffectVM IR can't yet
//! re-derive (the Lean module headers flag this as "IR-BLOCKED" / "the per-row IR
//! STOPS here"). They are registered because the leg they DO emit is verified, and
//! the registry is honest about the gap. Known-partial: the cap-root-move family
//! (`attenuateA` — `cap_root` is a scalar digest of the cap-table FUNCTION the IR
//! can't unfold) and the passthrough-with-hash effects (`setPermissionsA`/`setVK`/
//! `refreshDelegation`/`emitEvent` — state passthrough + an `effects_hash` binding
//! whose preimage lives off-trace). The transfer/burn/mint/note descriptors are
//! FULL economic-state descriptors (balance limb move + frame freeze + GROUP-4
//! commit).
//!
//! ## DO NOT hand-edit
//!
//! The const block and the tables below are generated from the Lean emit. To
//! refresh, run the ONE command:
//!
//!   scripts/emit-descriptors.sh
//!
//! It runs every Lean emitter, rewrites `circuit/descriptors/*.json`, and re-pins
//! the `*_FP` cache-freshness SHA-256 constants — idempotent (a no-op on a clean
//! tree). The CI gate `scripts/check-descriptor-drift.sh` (the `descriptor-drift`
//! job) is the real Lean↔JSON guard: it regenerates from Lean and diffs. See
//! `docs/DESCRIPTOR-EMIT.md`.

// ==== include_str! consts + sha256 cache-freshness pins (auto-generated; do not hand-edit) ====
pub const DREGG_EFFECTVM_ATTENUATEA_V1_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-attenuateA-v1.json");
pub const DREGG_EFFECTVM_ATTENUATEA_V1_FP: &str =
    "db3b6c5df585720ca7fe303dc56812e7ab9b9a134826044d8aabe301f6eeda16";
pub const DREGG_EFFECTVM_BRIDGEMINT_V1_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-bridgemint-v1.json");
pub const DREGG_EFFECTVM_BRIDGEMINT_V1_FP: &str =
    "bf7f5533d351799339eab210f1a804bd7123bdca0349559f9da9bed8420498a1";
pub const DREGG_EFFECTVM_BURN_V1_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-burn-v1.json");
pub const DREGG_EFFECTVM_BURN_V1_FP: &str =
    "124bd595c512392fb413ebac9ec785c5b3206a2946651949d1a24accac55f25b";
// GRADUATED (cap-crown): RevokeCapability (sel 24) v1 FACE — the cap-root MOVE + frame freeze (the
// SAME row shape as the attenuate template, only the AIR name differs). The in-circuit sorted-tree
// slot DELETION is the v2 leg (`DREGG_EFFECTVM_REVOKE_CAP_IR2_*`). Lean source
// `EffectVmEmitRevokeCapability.revokeCapabilityVmDescriptor`.
pub const DREGG_EFFECTVM_REVOKECAPABILITY_V1_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-revokecapability-v1.json");
pub const DREGG_EFFECTVM_REVOKECAPABILITY_V1_FP: &str =
    "fc27393cbc02187c1f1840f924e32a62b4f3bf3f3c13997b17b74cac1fe65ad7";
// GRADUATED (nonce-tick reconcile, v2): frozen-balance + ticked-nonce effect; the Lean descriptor
// now ticks the runtime nonce (`gNonce`) AND carries the full last-row balance PI binding
// (`boundaryLastPins`), so the descriptor decides IDENTICALLY to the hand-AIR on the real witness
// (honest accept + forged-balance/forged-state-commit reject). Body STRUCTURALLY IDENTICAL to the
// validated `createsealpair-v2` (only the `name` differs). Name bumped `-v1`→`-v2`; FP updated.
pub const DREGG_EFFECTVM_CELLDESTROY_V2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-celldestroy-v2.json");
pub const DREGG_EFFECTVM_CELLDESTROY_V2_FP: &str =
    "6bf15bdea99cddec841af06b2741a62e1b9bff8b73f306f7868217cffc08b000";
pub const DREGG_EFFECTVM_CELLSEAL_V2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-cellseal-v2.json");
pub const DREGG_EFFECTVM_CELLSEAL_V2_FP: &str =
    "cba230cee6467ad92ab25ac5dbe50bbcb770443ac63fa8510f945cf4551cdb3a";
// GRADUATED (lifecycle Sealed→Live, v2): the runtime row is the SAME frozen-frame + nonce-tick
// passthrough as cellSeal (the trace arm ticks the nonce, freezes the economic block; the single
// CELL_UNSEAL_TARGET param binds the cell). The lifecycle flip is the off-row face, verified in
// `EffectVmEmitCellUnseal` (`cellUnsealA_full_sound`). Body structurally identical to cellseal-v2
// with `selectorGates 50`.
pub const DREGG_EFFECTVM_CELLUNSEAL_V2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-cellunseal-v2.json");
pub const DREGG_EFFECTVM_CELLUNSEAL_V2_FP: &str =
    "0aded40b70867fd0d8550cc3741a707f478321dbb28af0925b4fa0df12c62fae";
// GRADUATED (lifecycle/birth reconcile, v2): the WIRE descriptor is now the RUNTIME ACTOR row
// (frozen-frame + nonce-tick + last-row PI pins, body structurally identical to the validated
// `revokeDelegation-v2` template). The pre-v2 JSON pinned the BORN-EMPTY CHILD cell, which the
// runtime row (the acting cell's Stage-3 passthrough) cannot satisfy; the child face stays verified
// in the Lean module (`EffectVmEmitCreateCell`, off-row via `createCellA_full_sound`).
pub const DREGG_EFFECTVM_CREATECELL_V2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-createcell-v2.json");
pub const DREGG_EFFECTVM_CREATECELL_V2_FP: &str =
    "006544514895cd405958e4cd8259893fb4955b4b8b38dd0b8b7f76c2bbb5af6c";
// GRADUATED (lifecycle/birth reconcile, v2): same actor-row reconcile as createcell-v2; the minted
// cell's born-empty face stays in `EffectVmEmitCreateCellFromFactory`.
pub const DREGG_EFFECTVM_CREATECELLFROMFACTORY_V2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-createcellfromfactory-v2.json");
pub const DREGG_EFFECTVM_CREATECELLFROMFACTORY_V2_FP: &str =
    "182ca22173a861e231e4d213a0a8f460465b4a163442b63251eecacf4d18699b";
// emitEvent GRADUATED into the cutover (passthrough+tick reconcile): the Lean emit module
// `EffectVmEmitEmitEvent` now ticks the runtime nonce (`gNonce`), freezes the economic block (NOT the
// commit), and carries the selector-binding gate (`selectorGates 25`). The prior JSON froze the nonce +
// the commit (made the honest TICKED trace UNSAT). Name unchanged (`-v1`); body + fingerprint updated.
pub const DREGG_EFFECTVM_EMITEVENT_V1_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-emitEvent-v1.json");
pub const DREGG_EFFECTVM_EMITEVENT_V1_FP: &str =
    "10d766540f7757265b99fcdaa8f432c2c63a8d1ee7ab97fddcc053b9559d6e51";
// GRADUATED (nonce-tick + last-row PI pins, v2): the Lean emit module was reconciled onto the runtime
// Stage-3 passthrough batch (whole economic block frozen, nonce ticks via `gNonce`) AND grew the
// `boundaryLastPins` last-row balance PI binding. Body STRUCTURALLY IDENTICAL to the validated
// `createsealpair-v2`; the JSON had not been re-emitted. Name `-v1`→`-v2`; FP updated.
pub const DREGG_EFFECTVM_EXERCISEA_HOLDLAYER_V2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-exerciseA-holdlayer-v2.json");
pub const DREGG_EFFECTVM_EXERCISEA_HOLDLAYER_V2_FP: &str =
    "d45371406cef1078be685eb13219e1aa2baaeeeccc22a57e176e92fa147964a6";
// GRADUATED (nonce-tick + last-row PI pins, v2): the explicit nonce-only effect. The Lean module was
// reconciled to the runtime TICK (`new_state.nonce += 1`) via `gNonce` and grew `boundaryLastPins`,
// dropping the prior param-bound nonce gate; body STRUCTURALLY IDENTICAL to `createsealpair-v2`. The
// committed JSON was the stale param-bound v1. Name `-v1`→`-v2`; FP updated.
pub const DREGG_EFFECTVM_INCREMENTNONCE_V2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-incrementNonce-v2.json");
pub const DREGG_EFFECTVM_INCREMENTNONCE_V2_FP: &str =
    "b04b751145cdbb67a4797cc087502d1e4d3977517f356cbfee550a716a604a40";
// GRADUATED (sovereign mode-bit reconcile, v2): the WIRE descriptor is the RUNTIME row — frame
// freeze + `reserved += 256` (the packed mode_flag bit the hand-AIR enforces) + nonce tick + last-row
// PI pins. The pre-v2 JSON pinned the executor's REBIND-TO-ZERO face (readable record dropped behind
// `stateCommitment`), which the runtime row cannot satisfy; that face stays verified in
// `EffectVmEmitMakeSovereign`. WHICH sovereignty semantics is canonical (rebind-zero vs mode-bit)
// remains an open protocol decision — the cutover models what the runtime proves today.
pub const DREGG_EFFECTVM_MAKESOVEREIGN_V2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-makesovereign-v2.json");
pub const DREGG_EFFECTVM_MAKESOVEREIGN_V2_FP: &str =
    "07b3118fa14a0334dbc8635b8cca3ceeebd1b3a3d837350dc6b460b23316ead4";
pub const DREGG_EFFECTVM_MINT_V1_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-mint-v1.json");
pub const DREGG_EFFECTVM_MINT_V1_FP: &str =
    "5dae1969757703ad4c36a67cff3b933bfb723f9c480c48d0d6f4a844fb28c957";
pub const DREGG_EFFECTVM_NOTECREATE_V1_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-notecreate-v1.json");
pub const DREGG_EFFECTVM_NOTECREATE_V1_FP: &str =
    "b978d4d274b22b324d625bf6dd9e8592448a58295bc977c16b7d179f7cd62995";
pub const DREGG_EFFECTVM_NOTESPEND_V1_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-notespend-v1.json");
pub const DREGG_EFFECTVM_NOTESPEND_V1_FP: &str =
    "ccf18056f2002042677d15b785e372ef5db73ba039f1b534a96592331352725e";
// GRADUATED (nonce-tick + last-row PI pins, v2): see exercise note. Body STRUCTURALLY IDENTICAL to
// `createsealpair-v2`. Name `-v1`→`-v2`; FP updated.
pub const DREGG_EFFECTVM_PIPELINEDSENDA_V2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-pipelinedSendA-v2.json");
pub const DREGG_EFFECTVM_PIPELINEDSENDA_V2_FP: &str =
    "a9d384910d828824e5a0012862f81dee637adb036f730be560ba3a9567fa49d4";
// GRADUATED (lifecycle-SET reconcile, v2): the WIRE descriptor is the RUNTIME row — pure
// frozen-frame + nonce-tick (the hand-AIR freezes field[1] and ticks the nonce; the archive
// lifecycle write lives off-row via effects_hash). The pre-v2 JSON SET field[1] := 1 and froze the
// nonce (the executor face), UNSAT on the runtime trace; that face stays verified in
// `EffectVmEmitReceiptArchive`.
pub const DREGG_EFFECTVM_RECEIPTARCHIVEA_V2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-receiptArchiveA-v2.json");
pub const DREGG_EFFECTVM_RECEIPTARCHIVEA_V2_FP: &str =
    "51de76f7f03355c80b94d511cebe96913bf168b651af1fb061fce5013350fcbc";
// GRADUATED (nonce-tick + last-row PI pins, v2): refreshDelegation already ticked the runtime nonce
// (`gNonce`) but the committed JSON carried only `boundaryFirstPins` (anti-ghost WEAK: the forged
// last-row balance tooth did not bite). The Lean module grew `boundaryLastPins` + the 2 balance ranges.
// Name `-v1`→`-v2`; FP updated.
pub const DREGG_EFFECTVM_REFRESHDELEGATION_V2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-refreshDelegation-v2.json");
pub const DREGG_EFFECTVM_REFRESHDELEGATION_V2_FP: &str =
    "18a3b33be53905459397f131cd5561a116b1e6ef708522cc0e65dd203eb5acdf";
// GRADUATED (nonce-tick + last-row PI pins, v2): revokeDelegation was PRE-v2 pointed at the
// `attenuateA` cap-root-MOVE descriptor, which the runtime hand-AIR does NOT enforce on a revoke row
// (it FREEZES `cap_root`); it "passed" only by fixture accident (cap_root = param2 = 0). The v2 Lean
// module emits the runtime frozen-frame + nonce-TICK directly; the cap-table edge removal is bound
// OFF-row via the universe-A connector. Body STRUCTURALLY IDENTICAL to `createsealpair-v2`.
pub const DREGG_EFFECTVM_REVOKEDELEGATION_V2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-revokeDelegation-v2.json");
pub const DREGG_EFFECTVM_REVOKEDELEGATION_V2_FP: &str =
    "80d71983fc39074811cec5d02d8f34e76847d50d7b0374fa0177946628818a71";
// GRADUATED (nonce-tick + last-row PI pins, v2): introduce, same reconcile as revokeDelegation (was
// PRE-v2 pointed at `attenuateA`). The cap-table grant is bound OFF-row via the universe-A connector.
pub const DREGG_EFFECTVM_INTRODUCE_V2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-introduce-v2.json");
pub const DREGG_EFFECTVM_INTRODUCE_V2_FP: &str =
    "892649cf9c246f652014acb6b8bcf5666639a73f824334f293d5da21c8fd6b6a";
// GRADUATED (nonce-tick reconcile, v2): see celldestroy/cellseal note. Body STRUCTURALLY IDENTICAL
// to `createsealpair-v2`. Name bumped `-v1`→`-v2`; FP updated.
pub const DREGG_EFFECTVM_REFUSAL_V2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-refusal-v2.json");
pub const DREGG_EFFECTVM_REFUSAL_V2_FP: &str =
    "96cd1b817c7c2d7da7a2e4291dd2b609400f17fb7ce350a21f7da95f27463e51";
// GRADUATED (nonce-tick + last-row PI pins, v2): see exercise note. Body STRUCTURALLY IDENTICAL to
// `createsealpair-v2`. Name `-v1`→`-v2`; FP updated.
pub const DREGG_EFFECTVM_SETPERMISSIONSA_V2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-setPermissionsA-v2.json");
pub const DREGG_EFFECTVM_SETPERMISSIONSA_V2_FP: &str =
    "a58d7e656d4bcbd06f7c101b0a4ac187c82263731e06d6cd0e2002b3710d280f";
pub const DREGG_EFFECTVM_SETVK_V2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-setVK-v2.json");
pub const DREGG_EFFECTVM_SETVK_V2_FP: &str =
    "c4adc1fb71cf65d21cc60e484b5eb0a1db655c72ef83e75c4fd77f8b65bdbff9";
// GRADUATED (lifecycle/birth reconcile, v3): the WIRE descriptor is the RUNTIME ACTOR (parent) row
// (frozen-frame + nonce-tick). The pre-v3 `v2quint-childcell` JSON pinned the born-empty + cap-handoff
// CHILD cell, which the runtime row cannot satisfy; the child face stays verified in
// `EffectVmEmitSpawn` (off-row via `spawnA_full_sound`).
pub const DREGG_EFFECTVM_SPAWNA_V3_ACTORROW_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-spawnA-v3-actorrow.json");
pub const DREGG_EFFECTVM_SPAWNA_V3_ACTORROW_FP: &str =
    "0b8d63be017a3e7df00f0a9d3f8b43eb6640a3178e40422ffc84b3315851691d";
pub const DREGG_EFFECTVM_TRANSFER_V1_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-transfer-v1.json");
pub const DREGG_EFFECTVM_TRANSFER_V1_FP: &str =
    "7b5a24a1f8fccf4e157f93acfa84307772c7b1650cc6febb048d8adc9d538ae4";
// RECORD-LAYER STAGE 2 (`_RECORD-LAYER-UPGRADE.md` §B.5/§E Stage 2): the transfer descriptor with
// GROUP-4 site 3's previously-spare 4th input ({"t":"zero"}) replaced by the `fields_root` carrier
// cell (col 89 = state_after.FIELDS_ROOT = the RESERVED slot), absorbing the user-field-map root into
// `state_commit`. Width-neutral (186); constraints/ranges/sites 0..2 byte-identical to transfer.
// Verified by construction in `Dregg2.Circuit.Emit.EffectVmEmitRecordRoot` (anti-ghost:
// `recordDescriptor_commit_binds_fieldsRoot`).
pub const DREGG_EFFECTVM_RECORD_V1_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-record-v1.json");
// Re-emitted: the committed JSON had gone STALE behind the Lean source (the transfer selector-binding
// gate landed in `EffectVmEmitTransfer`, and `recordVmDescriptor.constraints =
// transferVmDescriptor.constraints` holds by `rfl` in `EffectVmEmitRecordRoot`, but record-v1 was
// never re-emitted — it was one gate short). Bytes match the `EmitAllJson` output again.
pub const DREGG_EFFECTVM_RECORD_V1_FP: &str =
    "b946de1bab6e17b1f8a6061c58041815f9a362903629f645dddcba89fa6fb25a";

// ==== IR-v2 descriptor consts (EPOCH flag-day; ADDITIVE — the v1 consts above stay LIVE) ====
//
// These are the byte-exact output of the Lean executable `EmitAllJsonV2.lean`
// (`lake env lean --run`, which wires `EffectVmEmitV2.v2Registry` through
// `DescriptorIR2.emitVmJson2`). Each is a VERSIONED v2 wire string (`"ir":2`) carrying the five
// EPOCH tables (main / poseidon2_chip / range / memory / map_ops) + the lookup/mem_op/map_op
// constraint grammar that `descriptor_ir2::parse_vm_descriptor2` interprets. They sit ALONGSIDE
// the v1 JSONs during the transition: the live prover still routes through the v1 path
// (`lean_descriptor_air::prove_vm_descriptor`); these are wired+fingerprinted ahead of the
// cutover lane. The registry key is the UNIQUE Lean def-name (the 8 setField slots share the wire
// `name` `dregg-effectvm-setfield-v1`, so name-keying would collide — def-name does not).
pub const DREGG_EFFECTVM_TRANSFER_IR2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-transfer-ir2.json");
pub const DREGG_EFFECTVM_TRANSFER_IR2_FP: &str =
    "4c4c2f876c02d081de5975defce877fb2ed0c58b77d5ab64ed0d76dc71f1b51f";
pub const DREGG_EFFECTVM_BURN_IR2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-burn-ir2.json");
pub const DREGG_EFFECTVM_BURN_IR2_FP: &str =
    "2a0f2e4a34ec990cc44b54fead4a41784cdf6a55ccedf315ce2b278bda567739";
pub const DREGG_EFFECTVM_MINT_IR2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-mint-ir2.json");
pub const DREGG_EFFECTVM_MINT_IR2_FP: &str =
    "7c255b00f590a25d148f2e3696ea96d9876ff3904f8945c6079e5156255d6b9b";
pub const DREGG_EFFECTVM_NOTE_SPEND_IR2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-note-spend-ir2.json");
pub const DREGG_EFFECTVM_NOTE_SPEND_IR2_FP: &str =
    "34a03fb0f276d15d047e41a4bbbab97899d3c9e5ebd8ac9563fa75b6829fa734";
pub const DREGG_EFFECTVM_NOTE_CREATE_IR2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-note-create-ir2.json");
pub const DREGG_EFFECTVM_NOTE_CREATE_IR2_FP: &str =
    "f05bfd5a8015bd76e65df9e8f5bf6c89f078b9a6368e04086282dddc19c13d1e";
pub const DREGG_EFFECTVM_CELL_SEAL_IR2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-cell-seal-ir2.json");
pub const DREGG_EFFECTVM_CELL_SEAL_IR2_FP: &str =
    "1ee1ad9bc7f1fab7b90b67c848fb3cfbb814cfecd5efa9fef6812448c8d31307";
pub const DREGG_EFFECTVM_CELL_DESTROY_IR2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-cell-destroy-ir2.json");
pub const DREGG_EFFECTVM_CELL_DESTROY_IR2_FP: &str =
    "cbb20a8f8da44955938c1b68f45809138928fb5ad65f79da67463be675da9784";
pub const DREGG_EFFECTVM_REFUSAL_IR2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-refusal-ir2.json");
pub const DREGG_EFFECTVM_REFUSAL_IR2_FP: &str =
    "954e4d79a86941581ada5c86587b427ab916e2714f1f7f2f3915ed0e2a0114a7";
pub const DREGG_EFFECTVM_SET_PERMS_IR2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-set-perms-ir2.json");
pub const DREGG_EFFECTVM_SET_PERMS_IR2_FP: &str =
    "a2c2f2f8943d75c9ad3ccba2b6374c4199218b53809c0b8b28138bd5c4cb43db";
pub const DREGG_EFFECTVM_SET_VK_IR2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-set-vk-ir2.json");
pub const DREGG_EFFECTVM_SET_VK_IR2_FP: &str =
    "7f3c852c37d2edbe5f9d2600e832bc9b9bfd7cfd5ac165585bcb7b009dff194f";
pub const DREGG_EFFECTVM_EXERCISE_IR2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-exercise-ir2.json");
pub const DREGG_EFFECTVM_EXERCISE_IR2_FP: &str =
    "3eb1702bb47de8176f85dd9692c03c94768d7cc976ea3be8106687ad9f1810ed";
pub const DREGG_EFFECTVM_PIPELINED_SEND_IR2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-pipelined-send-ir2.json");
pub const DREGG_EFFECTVM_PIPELINED_SEND_IR2_FP: &str =
    "c275deac4eb9f377beb6905a1b21c48a5bd33b5da20a9d42ea16eeb8591c00c6";
pub const DREGG_EFFECTVM_REFRESH_IR2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-refresh-ir2.json");
pub const DREGG_EFFECTVM_REFRESH_IR2_FP: &str =
    "32ed07389f36560e0ebd3431f77190faf70ab347e4de2d3b76d35c79f3f47194";
pub const DREGG_EFFECTVM_INCREMENT_NONCE_IR2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-increment-nonce-ir2.json");
pub const DREGG_EFFECTVM_INCREMENT_NONCE_IR2_FP: &str =
    "b5c43826ee081a268a3dc6a9db941248c051ec36ea352856f0f061c1d7f878bc";
pub const DREGG_EFFECTVM_REVOKE_IR2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-revoke-ir2.json");
pub const DREGG_EFFECTVM_REVOKE_IR2_FP: &str =
    "3d45b48669806a2cf501cc8f66a663bf355934e96ec6ea9d4989e37987033f6b";
pub const DREGG_EFFECTVM_INTRODUCE_IR2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-introduce-ir2.json");
pub const DREGG_EFFECTVM_INTRODUCE_IR2_FP: &str =
    "b68d0da9a5100d2ca90b8342ea656528ed91069f49974178137d21e028f94e89";
pub const DREGG_EFFECTVM_ATTENUATE_IR2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-attenuate-ir2.json");
pub const DREGG_EFFECTVM_ATTENUATE_IR2_FP: &str =
    "df107039870d8ffe23c59e22766ba4b29e1b1e5a70e22bc0b4cc6481c3ed346c";
// GRADUATED (cap-crown): RevokeCapability (sel 24). The v2 leg of the cap-REMOVAL effect — a
// held-membership map-read authenticated against the before cap_root + a ZERO-value remove-write
// (the slot's rights deleted), NO submask (revoke deletes a slot, it does not narrow rights). Lean
// source `EffectVmEmitV2.revokeCapabilityVmDescriptor2`; keystones `revokeV2_removes` /
// `revokeV2_held_determined` / `revokeV2_post_determined`.
pub const DREGG_EFFECTVM_REVOKE_CAP_IR2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-revoke-cap-ir2.json");
pub const DREGG_EFFECTVM_REVOKE_CAP_IR2_FP: &str =
    "6d0825bd4adcda8b804c4e0584e3af3e88e653d583c4c14c8c3a3a1c4a8a52f0";
// GRADUATED (Custom recursive-proof binding, sel 8): the runtime passthrough face graduated onto
// IR-v2 PLUS the `proof_bind` op (`customProofBind`) that ties the row's `custom_proof_commitment`
// to a VERIFYING external sub-proof of the recursion engine — the accumulator constraint the
// per-row IR gained (`DescriptorIR2.ProofBind`). Lean source
// `EffectVmEmitV2.customVmDescriptor2`. THE LAST rotation-cutover residue closed.
pub const DREGG_EFFECTVM_CUSTOM_IR2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-custom-ir2.json");
pub const DREGG_EFFECTVM_CUSTOM_IR2_FP: &str =
    "343b10b41d3bf801bc082d4281610a20429db594e3546ab62e59f2890239ae16";
pub const DREGG_EFFECTVM_SET_FIELD_DYN_IR2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-set-field-dyn-ir2.json");
pub const DREGG_EFFECTVM_SET_FIELD_DYN_IR2_FP: &str =
    "c060f6800557c6e45b63e84939b9d0a528246d8398a84fc0e9289146c7a235e3";
pub const DREGG_EFFECTVM_SET_FIELD_0_IR2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-set-field-0-ir2.json");
pub const DREGG_EFFECTVM_SET_FIELD_0_IR2_FP: &str =
    "d12eb49f75853fb96f2efa81afdc609add172d1f013c3e1ee49cf221966d1471";
pub const DREGG_EFFECTVM_SET_FIELD_1_IR2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-set-field-1-ir2.json");
pub const DREGG_EFFECTVM_SET_FIELD_1_IR2_FP: &str =
    "8a060dc3f1bb644cedfe7d194311ffe1649b00da150a97e01bac7745d8c28aa1";
pub const DREGG_EFFECTVM_SET_FIELD_2_IR2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-set-field-2-ir2.json");
pub const DREGG_EFFECTVM_SET_FIELD_2_IR2_FP: &str =
    "02ef3c44e9d98ba6aa13430fe8c4b6c0a5117e39417fbc30a7324643b5a0cbe9";
pub const DREGG_EFFECTVM_SET_FIELD_3_IR2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-set-field-3-ir2.json");
pub const DREGG_EFFECTVM_SET_FIELD_3_IR2_FP: &str =
    "58a341da9beecda18d728728cd2f74a523c9c6f891dffc42e1a4c5565218339f";
pub const DREGG_EFFECTVM_SET_FIELD_4_IR2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-set-field-4-ir2.json");
pub const DREGG_EFFECTVM_SET_FIELD_4_IR2_FP: &str =
    "9abb646332c85687040cc69b69d6e5ec4db9e368357642045ae70c80c24936ee";
pub const DREGG_EFFECTVM_SET_FIELD_5_IR2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-set-field-5-ir2.json");
pub const DREGG_EFFECTVM_SET_FIELD_5_IR2_FP: &str =
    "6be945966b4fe5c960e49cc3a9bfca623b5f0ba0eee9389e5a9b51222b10234a";
pub const DREGG_EFFECTVM_SET_FIELD_6_IR2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-set-field-6-ir2.json");
pub const DREGG_EFFECTVM_SET_FIELD_6_IR2_FP: &str =
    "3943f5a61562d3d26339af2908d3b75f71d10621dbf02851847b130ebc03c3c7";
pub const DREGG_EFFECTVM_SET_FIELD_7_IR2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-set-field-7-ir2.json");
pub const DREGG_EFFECTVM_SET_FIELD_7_IR2_FP: &str =
    "7f0a4396b5e7baaf7d7713092e06b1968e6ac1431f411543143028be7426c61f";

// ==== selector index -> (descriptor name, const json, fingerprint) ====
pub const SELECTOR_DESCRIPTORS: &[(usize, &str, &str, &str)] = &[
    (
        1,
        "dregg-effectvm-transfer-v1",
        DREGG_EFFECTVM_TRANSFER_V1_JSON,
        DREGG_EFFECTVM_TRANSFER_V1_FP,
    ), // TRANSFER: transferVmDescriptor
    (
        3,
        "dregg-effectvm-attenuateA-v1",
        DREGG_EFFECTVM_ATTENUATEA_V1_JSON,
        DREGG_EFFECTVM_ATTENUATEA_V1_FP,
    ), // GRANT_CAP: delegateVmDescriptor (unattenuated cap-root grant = attenuate template)
    (
        4,
        "dregg-effectvm-notespend-v1",
        DREGG_EFFECTVM_NOTESPEND_V1_JSON,
        DREGG_EFFECTVM_NOTESPEND_V1_FP,
    ), // NOTE_SPEND: noteSpendVmDescriptor
    (
        5,
        "dregg-effectvm-notecreate-v1",
        DREGG_EFFECTVM_NOTECREATE_V1_JSON,
        DREGG_EFFECTVM_NOTECREATE_V1_FP,
    ), // NOTE_CREATE: noteCreateVmDescriptor
    (
        12,
        "dregg-effectvm-makesovereign-v2",
        DREGG_EFFECTVM_MAKESOVEREIGN_V2_JSON,
        DREGG_EFFECTVM_MAKESOVEREIGN_V2_FP,
    ), // MAKE_SOVEREIGN: makeSovereignRuntimeVmDescriptor (GRADUATED: mode-bit +256 + nonce-tick; rebind face off-row)
    (
        13,
        "dregg-effectvm-createcellfromfactory-v2",
        DREGG_EFFECTVM_CREATECELLFROMFACTORY_V2_JSON,
        DREGG_EFFECTVM_CREATECELLFROMFACTORY_V2_FP,
    ), // CREATE_CELL_FROM_FACTORY: factoryActorVmDescriptor (GRADUATED: actor frozen-frame + nonce-tick; child face off-row)
    (
        24,
        "dregg-effectvm-revokecapability-v1",
        DREGG_EFFECTVM_REVOKECAPABILITY_V1_JSON,
        DREGG_EFFECTVM_REVOKECAPABILITY_V1_FP,
    ), // REVOKE_CAPABILITY: revokeCapabilityVmDescriptor (GRADUATED cap-crown v1 FACE; in-circuit slot DELETION = the v2 leg)
    (
        25,
        "dregg-effectvm-emitEvent-v1",
        DREGG_EFFECTVM_EMITEVENT_V1_JSON,
        DREGG_EFFECTVM_EMITEVENT_V1_FP,
    ), // EMIT_EVENT: emitEventVmDescriptor
    (
        26,
        "dregg-effectvm-setPermissionsA-v2",
        DREGG_EFFECTVM_SETPERMISSIONSA_V2_JSON,
        DREGG_EFFECTVM_SETPERMISSIONSA_V2_FP,
    ), // SET_PERMISSIONS: setPermsVmDescriptor (GRADUATED: nonce-tick + last-row PI pins)
    (
        27,
        "dregg-effectvm-setVK-v2",
        DREGG_EFFECTVM_SETVK_V2_JSON,
        DREGG_EFFECTVM_SETVK_V2_FP,
    ), // SET_VERIFICATION_KEY: setVKVmDescriptor (GRADUATED: nonce-tick + last-row PI pins)
    (
        29,
        "dregg-effectvm-refreshDelegation-v2",
        DREGG_EFFECTVM_REFRESHDELEGATION_V2_JSON,
        DREGG_EFFECTVM_REFRESHDELEGATION_V2_FP,
    ), // REFRESH_DELEGATION: refreshVmDescriptor (GRADUATED: nonce-tick + last-row PI pins)
    (
        30,
        "dregg-effectvm-revokeDelegation-v2",
        DREGG_EFFECTVM_REVOKEDELEGATION_V2_JSON,
        DREGG_EFFECTVM_REVOKEDELEGATION_V2_FP,
    ), // REVOKE_DELEGATION: revokeVmDescriptor (GRADUATED: frozen-frame + nonce-tick; cap-table move OFF-row)
    (
        31,
        "dregg-effectvm-createcell-v2",
        DREGG_EFFECTVM_CREATECELL_V2_JSON,
        DREGG_EFFECTVM_CREATECELL_V2_FP,
    ), // CREATE_CELL: createCellActorVmDescriptor (GRADUATED: actor frozen-frame + nonce-tick; child face off-row)
    (
        32,
        "dregg-effectvm-spawnA-v3-actorrow",
        DREGG_EFFECTVM_SPAWNA_V3_ACTORROW_JSON,
        DREGG_EFFECTVM_SPAWNA_V3_ACTORROW_FP,
    ), // SPAWN_WITH_DELEGATION: spawnActorVmDescriptor (GRADUATED: actor frozen-frame + nonce-tick; child face off-row)
    (
        34,
        "dregg-effectvm-exerciseA-holdlayer-v2",
        DREGG_EFFECTVM_EXERCISEA_HOLDLAYER_V2_JSON,
        DREGG_EFFECTVM_EXERCISEA_HOLDLAYER_V2_FP,
    ), // EXERCISE_VIA_CAPABILITY: exerciseVmDescriptor (GRADUATED: nonce-tick + last-row PI pins)
    (
        35,
        "dregg-effectvm-introduce-v2",
        DREGG_EFFECTVM_INTRODUCE_V2_JSON,
        DREGG_EFFECTVM_INTRODUCE_V2_FP,
    ), // INTRODUCE: introduceVmDescriptor (GRADUATED: frozen-frame + nonce-tick; cap-table grant OFF-row)
    (
        36,
        "dregg-effectvm-pipelinedSendA-v2",
        DREGG_EFFECTVM_PIPELINEDSENDA_V2_JSON,
        DREGG_EFFECTVM_PIPELINEDSENDA_V2_FP,
    ), // PIPELINED_SEND: pipelinedSendVmDescriptor (GRADUATED: nonce-tick + last-row PI pins)
    (
        40,
        "dregg-effectvm-bridgemint-v1",
        DREGG_EFFECTVM_BRIDGEMINT_V1_JSON,
        DREGG_EFFECTVM_BRIDGEMINT_V1_FP,
    ), // BRIDGE_MINT: bridgeMintVmDescriptor
    (
        46,
        "dregg-effectvm-burn-v1",
        DREGG_EFFECTVM_BURN_V1_JSON,
        DREGG_EFFECTVM_BURN_V1_FP,
    ), // BURN: burnVmDescriptor
    (
        47,
        "dregg-effectvm-celldestroy-v2",
        DREGG_EFFECTVM_CELLDESTROY_V2_JSON,
        DREGG_EFFECTVM_CELLDESTROY_V2_FP,
    ), // CELL_DESTROY: cellDestroyVmDescriptor (GRADUATED: nonce-tick + last-row PI pins)
    (
        48,
        "dregg-effectvm-attenuateA-v1",
        DREGG_EFFECTVM_ATTENUATEA_V1_JSON,
        DREGG_EFFECTVM_ATTENUATEA_V1_FP,
    ), // ATTENUATE_CAPABILITY: attenuateVmDescriptor (canonical cap-root move)
    (
        49,
        "dregg-effectvm-cellseal-v2",
        DREGG_EFFECTVM_CELLSEAL_V2_JSON,
        DREGG_EFFECTVM_CELLSEAL_V2_FP,
    ), // CELL_SEAL: cellSealVmDescriptor (GRADUATED: nonce-tick + last-row PI pins)
    (
        50,
        "dregg-effectvm-cellunseal-v2",
        DREGG_EFFECTVM_CELLUNSEAL_V2_JSON,
        DREGG_EFFECTVM_CELLUNSEAL_V2_FP,
    ), // CELL_UNSEAL: cellUnsealVmDescriptor (GRADUATED: frozen-frame + nonce-tick; lifecycle flip off-row)
    (
        51,
        "dregg-effectvm-receiptArchiveA-v2",
        DREGG_EFFECTVM_RECEIPTARCHIVEA_V2_JSON,
        DREGG_EFFECTVM_RECEIPTARCHIVEA_V2_FP,
    ), // RECEIPT_ARCHIVE: receiptArchiveActorVmDescriptor (GRADUATED: frozen-frame + nonce-tick; lifecycle write off-row)
    (
        52,
        "dregg-effectvm-refusal-v2",
        DREGG_EFFECTVM_REFUSAL_V2_JSON,
        DREGG_EFFECTVM_REFUSAL_V2_FP,
    ), // REFUSAL: refusalVmDescriptor (GRADUATED: nonce-tick + last-row PI pins)
    (
        53,
        "dregg-effectvm-incrementNonce-v2",
        DREGG_EFFECTVM_INCREMENTNONCE_V2_JSON,
        DREGG_EFFECTVM_INCREMENTNONCE_V2_FP,
    ), // INCREMENT_NONCE: incrementNonceVmDescriptor (GRADUATED: nonce-tick + last-row PI pins)
];

// ==== name-only descriptors (verified, but no dedicated Rust selector slot yet) ====
pub const NAME_ONLY_DESCRIPTORS: &[(&str, &str, &str)] = &[
    (
        "dregg-effectvm-mint-v1",
        DREGG_EFFECTVM_MINT_V1_JSON,
        DREGG_EFFECTVM_MINT_V1_FP,
    ), // mintVmDescriptor: supply MINT (balance credit); no dedicated EffectVM sel (distinct from BRIDGE_MINT)
];

// ==== IR-v2 descriptor registry (EPOCH; ADDITIVE — keyed by UNIQUE Lean def-name) ====
//
// The `EffectVmEmitV2.v2Registry` entries, byte-exact from `EmitAllJsonV2.lean`, fingerprinted.
// These prove+verify through `descriptor_ir2::{parse_vm_descriptor2, prove_vm_descriptor2,
// verify_vm_descriptor2}` (the multi-table batch STARK). The live prover does NOT route through
// these yet — they are wired ahead of the cutover lane so the flag-day flips a registry pointer,
// not an emission. Key = the Lean def-name (`transferVmDescriptor2`, `setFieldVmDescriptor2-3`, …)
// since the wire `name` collides across graduated/per-slot descriptors.
pub const V2_DESCRIPTORS: &[(&str, &str, &str)] = &[
    (
        "transferVmDescriptor2",
        DREGG_EFFECTVM_TRANSFER_IR2_JSON,
        DREGG_EFFECTVM_TRANSFER_IR2_FP,
    ),
    (
        "burnVmDescriptor2",
        DREGG_EFFECTVM_BURN_IR2_JSON,
        DREGG_EFFECTVM_BURN_IR2_FP,
    ),
    (
        "mintVmDescriptor2",
        DREGG_EFFECTVM_MINT_IR2_JSON,
        DREGG_EFFECTVM_MINT_IR2_FP,
    ),
    (
        "noteSpendVmDescriptor2",
        DREGG_EFFECTVM_NOTE_SPEND_IR2_JSON,
        DREGG_EFFECTVM_NOTE_SPEND_IR2_FP,
    ),
    (
        "noteCreateVmDescriptor2",
        DREGG_EFFECTVM_NOTE_CREATE_IR2_JSON,
        DREGG_EFFECTVM_NOTE_CREATE_IR2_FP,
    ),
    (
        "cellSealVmDescriptor2",
        DREGG_EFFECTVM_CELL_SEAL_IR2_JSON,
        DREGG_EFFECTVM_CELL_SEAL_IR2_FP,
    ),
    (
        "cellDestroyVmDescriptor2",
        DREGG_EFFECTVM_CELL_DESTROY_IR2_JSON,
        DREGG_EFFECTVM_CELL_DESTROY_IR2_FP,
    ),
    (
        "refusalVmDescriptor2",
        DREGG_EFFECTVM_REFUSAL_IR2_JSON,
        DREGG_EFFECTVM_REFUSAL_IR2_FP,
    ),
    (
        "setPermsVmDescriptor2",
        DREGG_EFFECTVM_SET_PERMS_IR2_JSON,
        DREGG_EFFECTVM_SET_PERMS_IR2_FP,
    ),
    (
        "setVKVmDescriptor2",
        DREGG_EFFECTVM_SET_VK_IR2_JSON,
        DREGG_EFFECTVM_SET_VK_IR2_FP,
    ),
    (
        "exerciseVmDescriptor2",
        DREGG_EFFECTVM_EXERCISE_IR2_JSON,
        DREGG_EFFECTVM_EXERCISE_IR2_FP,
    ),
    (
        "pipelinedSendVmDescriptor2",
        DREGG_EFFECTVM_PIPELINED_SEND_IR2_JSON,
        DREGG_EFFECTVM_PIPELINED_SEND_IR2_FP,
    ),
    (
        "refreshVmDescriptor2",
        DREGG_EFFECTVM_REFRESH_IR2_JSON,
        DREGG_EFFECTVM_REFRESH_IR2_FP,
    ),
    (
        "incrementNonceVmDescriptor2",
        DREGG_EFFECTVM_INCREMENT_NONCE_IR2_JSON,
        DREGG_EFFECTVM_INCREMENT_NONCE_IR2_FP,
    ),
    (
        "revokeVmDescriptor2",
        DREGG_EFFECTVM_REVOKE_IR2_JSON,
        DREGG_EFFECTVM_REVOKE_IR2_FP,
    ),
    (
        "introduceVmDescriptor2",
        DREGG_EFFECTVM_INTRODUCE_IR2_JSON,
        DREGG_EFFECTVM_INTRODUCE_IR2_FP,
    ),
    (
        "attenuateVmDescriptor2",
        DREGG_EFFECTVM_ATTENUATE_IR2_JSON,
        DREGG_EFFECTVM_ATTENUATE_IR2_FP,
    ),
    (
        "revokeCapabilityVmDescriptor2",
        DREGG_EFFECTVM_REVOKE_CAP_IR2_JSON,
        DREGG_EFFECTVM_REVOKE_CAP_IR2_FP,
    ),
    (
        "customVmDescriptor2",
        DREGG_EFFECTVM_CUSTOM_IR2_JSON,
        DREGG_EFFECTVM_CUSTOM_IR2_FP,
    ),
    (
        "setFieldDynVmDescriptor2",
        DREGG_EFFECTVM_SET_FIELD_DYN_IR2_JSON,
        DREGG_EFFECTVM_SET_FIELD_DYN_IR2_FP,
    ),
    (
        "setFieldVmDescriptor2-0",
        DREGG_EFFECTVM_SET_FIELD_0_IR2_JSON,
        DREGG_EFFECTVM_SET_FIELD_0_IR2_FP,
    ),
    (
        "setFieldVmDescriptor2-1",
        DREGG_EFFECTVM_SET_FIELD_1_IR2_JSON,
        DREGG_EFFECTVM_SET_FIELD_1_IR2_FP,
    ),
    (
        "setFieldVmDescriptor2-2",
        DREGG_EFFECTVM_SET_FIELD_2_IR2_JSON,
        DREGG_EFFECTVM_SET_FIELD_2_IR2_FP,
    ),
    (
        "setFieldVmDescriptor2-3",
        DREGG_EFFECTVM_SET_FIELD_3_IR2_JSON,
        DREGG_EFFECTVM_SET_FIELD_3_IR2_FP,
    ),
    (
        "setFieldVmDescriptor2-4",
        DREGG_EFFECTVM_SET_FIELD_4_IR2_JSON,
        DREGG_EFFECTVM_SET_FIELD_4_IR2_FP,
    ),
    (
        "setFieldVmDescriptor2-5",
        DREGG_EFFECTVM_SET_FIELD_5_IR2_JSON,
        DREGG_EFFECTVM_SET_FIELD_5_IR2_FP,
    ),
    (
        "setFieldVmDescriptor2-6",
        DREGG_EFFECTVM_SET_FIELD_6_IR2_JSON,
        DREGG_EFFECTVM_SET_FIELD_6_IR2_FP,
    ),
    (
        "setFieldVmDescriptor2-7",
        DREGG_EFFECTVM_SET_FIELD_7_IR2_JSON,
        DREGG_EFFECTVM_SET_FIELD_7_IR2_FP,
    ),
];

// ==== ROTATION v3-STAGED artifacts (THE ROTATION — `docs/ROTATION-CUTOVER.md`) ====
//
// Byte-exact from `EmitRotationV3.lean` (the verified emission is
// `Dregg2/Circuit/Emit/EffectVmEmitRotation.lean`). STAGED: nothing on the live wire
// reads these — they ride the recursion-gated IR-v2 path only (the staged probe proves
// through `prove_vm_descriptor2`, tests in `descriptor_ir2.rs`). NOT part of
// `V2_DESCRIPTORS` (its 26-entry pin is the graduation cohort) nor `ALL_DESCRIPTORS`
// (the live v1 registry stays byte-identical).

/// The Lean-pinned rotation layout manifest (`rotationLayoutManifest`, `#guard`-byte-pinned
/// in Lean; the Rust twin test `rotation_layout_matches_lean` rebuilds it from
/// `effect_vm::columns::rotation` + `pi::v3` and compares — both sides pin, neither parses).
pub const ROTATION_LAYOUT_V3_STAGED_JSON: &str =
    include_str!("../descriptors/rotation-layout-v3-staged.json");
pub const ROTATION_LAYOUT_V3_STAGED_FP: &str =
    "418064625e5e4b77d851c7b114be37cc4a7c8f547352771209dca3c33ebc366f";

/// The staged rotation-state probe descriptor (`rotationProbeVmDescriptor2` =
/// `graduateV1` of the 8-site chained absorption + the two PI pins; Lean keystones
/// `rotationProbeV2_pins_commit` / `rotationProbe_commit_binds_published`).
pub const DREGG_EFFECTVM_ROTATION_STATE_V3_STAGED_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-rotation-state-v3-staged.json");
pub const DREGG_EFFECTVM_ROTATION_STATE_V3_STAGED_FP: &str =
    "c1cab43f12d4e39e8426ff5aa036a7ee2050acb027884709282ec551f7409e1e";

/// The REGISTER-COUNT MEASUREMENT probes (`docs/ROTATION-CUTOVER.md` pre-gates): the same
/// staged rotation probe emitted at R=24 and R=32 registers from the PARAMETRIC Lean
/// emission (`Dregg2/Circuit/Emit/EffectVmEmitRotationR.lean`, driver `EmitRotationV3.lean`;
/// keystone `wireCommitR_binds` holds parametrically in R — no per-R axiom). The R=16
/// probe above is the deployed reference and its bytes DO NOT move (Lean `#guard`s the
/// graduated R=16 wire JSON byte-identical to the pinned emission). These exist to be
/// MEASURED (`descriptor_ir2.rs::rotation_probe_register_count_measurement`): registers
/// are ALWAYS-PAID commitment limbs in every turn proof; heap fields are METERED umem rows.
pub const DREGG_EFFECTVM_ROTATION_STATE_V3_STAGED_R24_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-rotation-state-v3-staged-r24.json");
pub const DREGG_EFFECTVM_ROTATION_STATE_V3_STAGED_R24_FP: &str =
    "360dcbf21daea44888b07d938ecb165b14670aa8242e56cd8c1f9d354a893077";
pub const DREGG_EFFECTVM_ROTATION_STATE_V3_STAGED_R32_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-rotation-state-v3-staged-r32.json");
pub const DREGG_EFFECTVM_ROTATION_STATE_V3_STAGED_R32_FP: &str =
    "4e6e0245e91e6f543d7abc0f35ee6cc5628ce29b508e47f82ad2824436ffeebf";

/// The v3-staged registry (keyed by Lean def-name, the `V2_DESCRIPTORS` pattern). Entry 0
/// is the deployed R=16 reference; entries 1-2 are the register-count measurement probes.
pub const V3_STAGED_DESCRIPTORS: &[(&str, &str, &str)] = &[
    (
        "rotationProbeVmDescriptor2",
        DREGG_EFFECTVM_ROTATION_STATE_V3_STAGED_JSON,
        DREGG_EFFECTVM_ROTATION_STATE_V3_STAGED_FP,
    ),
    (
        "rotationProbeVmDescriptorR24",
        DREGG_EFFECTVM_ROTATION_STATE_V3_STAGED_R24_JSON,
        DREGG_EFFECTVM_ROTATION_STATE_V3_STAGED_R24_FP,
    ),
    (
        "rotationProbeVmDescriptorR32",
        DREGG_EFFECTVM_ROTATION_STATE_V3_STAGED_R32_JSON,
        DREGG_EFFECTVM_ROTATION_STATE_V3_STAGED_R32_FP,
    ),
];

/// THE WIDENED CAVEAT OPERAND artifacts (staged — the second rotation wire-shape
/// pre-gate). The layout manifest is byte-pinned BOTH sides (Lean `#guard` in
/// `EffectVmEmitRotationCaveat.lean`; Rust twin `rotation_caveat_layout_matches_lean`
/// rebuilds from `columns::rotation::caveat` — both pin, neither parses); the probe
/// descriptor is the R=24 rotated block + the 29-felt caveat manifest block + its
/// chained commitment, three PI pins (state commit · height · caveat commit). Lean
/// keystones: `caveat_operand_no_aliasing` (slot/heap domain separation as a theorem),
/// `caveatCommit_binds` (a forged domain tag / tampered heap key moves the commit),
/// `rotationCaveatProbe_binds_published` (end-to-end, wire form).
pub const ROTATION_CAVEAT_LAYOUT_V3_STAGED_JSON: &str =
    include_str!("../descriptors/rotation-caveat-layout-v3-staged.json");
pub const ROTATION_CAVEAT_LAYOUT_V3_STAGED_FP: &str =
    "8cfcaf978f7123f9f159f9ae05ab85ef9a245c93d9d9e1b6e2ce7b9500c890a8";

pub const DREGG_EFFECTVM_ROTATION_CAVEAT_V3_STAGED_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-rotation-caveat-v3-staged-r24.json");
pub const DREGG_EFFECTVM_ROTATION_CAVEAT_V3_STAGED_FP: &str =
    "538bf7ba0d7c1e49da90dc780803671f0aba5f0dd3cc010d75c954dc930d364d";

/// The caveat-operand staged registry (kept SEPARATE from `V3_STAGED_DESCRIPTORS`
/// so the three rotation-probe pins stay byte-frozen and their coverage walker
/// unchanged).
pub const V3_STAGED_CAVEAT_DESCRIPTORS: &[(&str, &str, &str)] = &[(
    "rotationCaveatProbeVmDescriptor2",
    DREGG_EFFECTVM_ROTATION_CAVEAT_V3_STAGED_JSON,
    DREGG_EFFECTVM_ROTATION_CAVEAT_V3_STAGED_FP,
)];

/// THE FULL-COHORT REGEN at the rotated R=24 block (`ROTATION-CUTOVER.md` §5 item 1):
/// all 36 cohort descriptors re-emitted past their v1 layout with the rotated
/// BEFORE/AFTER blocks + the widened-caveat region (Lean `rotateV3` /
/// `EffectVmEmitRotationV3.lean`; `v3Registry` is the source) — the 28 v2-graduated members
/// (the 17 graduated cohort + attenuate WITH its phase-B map-ops/submask lookup + revoke, plus
/// the cap-crown `revokeCapability`) PLUS the 8 LIVE-path effects the STEP 1 widening
/// added (grantCap · makeSovereign ·
/// createCell · factory · spawn · receiptArchive · cellUnseal · emitEvent). The TSV is
/// `key\tname\tjson` per line, structurally covered by `v3_staged_registry_parses_and_covers`.
/// ⚠ SUPERSEDED ON THE LIVE WIRE (2026-07-18 bare-V3 stratum audit) — the earlier "HARDSWAP made
/// this the sole live per-turn effect-VM source" note is STALE TWICE OVER: the WIDE flag-day
/// repointed the deployed producer/verifiers to `WIDE_REGISTRY_STAGED_TSV` /
/// the DERIVED welded set (SDK `prove_cohort_run_chain` / `verify_effect_vm_rotated_inner`,
/// executor `verify_one_cohort_run`, node retention — all wide-only). What still consumes THIS
/// bare registry at HEAD: the `dregg-verifier rotated-replay-chain` CLI demonstration floor, the
/// 3 gentian Sat members (`settleEscrowSat`/`dischargeSat`/`vaultSat`, which have NO wide twins),
/// ~30 tests (subjects/foils/fixtures), and the Lean side — the wide emission is DEFINED as
/// `wideAppend` over these members (`v3RegistryWide`), so the Lean layer stays regardless. See
/// HORIZONLOG 2026-07-18 "bare-V3 1-felt stratum" for the retirement map.
/// Widths reflect the CURRENT geometry (revoked-root 178 flag-day + the 8-felt ProofBind flag-day
/// `36f04de71`), NOT the retired `409 = 188 + 221` v10 formula: narrow rotated members run
/// `trace_width` up to ≈1668 with 62 PIs (transfer-class), the graduated chip-lane columns included.
/// The commitment is the faithful 8-felt ~124-bit binding (state + ProofBind both 8-felt), not the
/// old four-appended-PI / ~31-bit form.
pub const V3_STAGED_REGISTRY_TSV: &str =
    include_str!("../descriptors/rotation-v3-staged-registry.tsv");
pub const V3_STAGED_REGISTRY_FP: &str =
    "158dad4988d193746b0f0444a94b7e0cd8191d3bb921d49e2bbd8a735bff8c49";

/// The wire-name suffix marking a descriptor as the rotated+umem WELD
/// ([`weld_umem_into_rotated_descriptor`]). A descriptor whose `name` ends with this is a STAGED
/// welded form — never a deployed-registry member.
pub const ROTATED_UMEM_WELD_SUFFIX: &str = "-umem-welded-staged";

/// The wire-name suffix marking a descriptor as the WIDE rotated+umem WELD
/// ([`weld_umem_into_wide_descriptor`]) — the WIDE (8-felt / ~124-bit faithful commit) twin of
/// [`ROTATED_UMEM_WELD_SUFFIX`]. A descriptor whose `name` ends with this is a STAGED welded form
/// over a WIDE descriptor (preserving the wide member's 16 commit PIs / 8-felt before-after
/// anchors); never a deployed-registry member.
pub const WIDE_UMEM_WELD_SUFFIX: &str = "-umem-wide-welded-staged";

/// The wire-name suffix marking a descriptor as the WIDE rotated+umem MULTI-DOMAIN WELD
/// ([`weld_umem_multidomain_into_wide_descriptor`]) — the two-domain twin of
/// [`WIDE_UMEM_WELD_SUFFIX`]. A descriptor whose `name` ends with this welds the MULTI-DOMAIN umem
/// cohort (one guarded `umemOp` per touched domain — the NOTE/BRIDGE economic verbs' `heap` balance
/// credit + `nullifiers` freshness insert) onto a WIDE descriptor, preserving the wide member's 16
/// commit PIs (8-felt ~124-bit anchors). Never a deployed-registry member.
pub const WIDE_UMEM_MULTIDOMAIN_WELD_SUFFIX: &str = "-umem-multidomain-wide-welded-staged";

/// **THE ROTATED+UMEM WELD (STAGED, VK-RISK-FREE) — the last precursor before the gated VK epoch.**
///
/// Weld the universal-memory COHORT leg INTO a rotated R=24 descriptor: keep the WHOLE rotated
/// constraint set (gates / transitions / pi-bindings / chip lookups) AND the rotated ROT_PI_COUNT-PI vector
/// (`ROT_PI_COUNT` — the OLD/NEW state-commit pins at PI `V1_PI_COUNT` / `+1` the IVC chain fold
/// reads as `old_root` / `new_root`), and APPEND a SINGLE-domain `umem_op` reconciliation leg over
/// 7 fresh main columns `[base .. base+7)` (`base` = the rotated trace width) plus the `umemory`
/// (id 6, arity 8) / `umem_boundary` (id 7, arity 7) tables — exactly the cohort emitter's width-7
/// `umemOp` shape (`key · present · value · prev_present · prev_value · prev_serial · guard`),
/// offset to `base`.
///
/// This is the deployed flag-day weld in struct form: the per-map memory reconciliation moves INTO
/// the rotated descriptor as the universal-memory leg (`prove_vm_descriptor2_umem` with a REAL
/// `UMemBoundaryWitness`), while the rotated PIs stay INTACT — which is exactly what resolves the
/// two reconciliation seams the staged cohort leg named: (a) the umem leg now rides the rotated
/// descriptor's committed PI vector, and (b) the IVC fold's `old_root`/`new_root` PI accessors keep
/// working over the welded leg (the 0-PI cohort form could not supply them).
///
/// STAGED: a NEW descriptor BESIDE the deployed rotated registry — no VK bump, nothing on the live
/// wire. `domain` is the cohort domain the welded effect touches (heap 1 / caps 2 / nullifiers 3),
/// checked against the leg's actual domain by the prover.
pub fn weld_umem_into_rotated_descriptor(
    rotated: &crate::descriptor_ir2::EffectVmDescriptor2,
    domain: u32,
) -> crate::descriptor_ir2::EffectVmDescriptor2 {
    let split = canonicity_splice_of(rotated);
    weld_umem_into_descriptor_with_suffix(rotated, domain, ROTATED_UMEM_WELD_SUFFIX, false, split)
}

/// **THE COHORT-SPECIALIZED ROTATED+UMEM WELD (STAGED, VK-RISK-FREE) — the IVC-fold perf lever.**
///
/// Identical to [`weld_umem_into_rotated_descriptor`] except the universal boundary table (id 7) is
/// declared with [`TableSem::UMemBoundaryCohort`](crate::descriptor_ir2::TableSem::UMemBoundaryCohort)
/// — the SINGLE-ROW specialization. The single-domain welded leg (e.g. a `Transfer`'s lone Balance
/// touch) reconciles AT MOST ONE `(domain, key)` cell, so the general boundary's ~29 columns of key
/// decomposition + lexicographic strict-increase comparator (which exist SOLELY to prove the declared
/// address list is `Nodup`) are dead weight: with one row, `Nodup` is `List.nodup_singleton` (Lean
/// `UniversalMemory.universal_memory_sound_single`, `#assert_axioms`-clean). This weld routes the leg
/// through the width-9 `Ir2Air::UMemBoundaryCohort`, quartering the boundary instance's FRI columns —
/// and that instance is re-paid up the WHOLE IVC aggregation tree, so the saving compounds. The
/// single-row discipline is enforced in-circuit (`next.is_real = 0` on every transition); a
/// multi-address witness is REFUSED at assembly and in the AIR, never silently mis-proved. A
/// multi-address single-domain leg must use the general [`weld_umem_into_rotated_descriptor`].
pub fn weld_umem_into_rotated_descriptor_cohort(
    rotated: &crate::descriptor_ir2::EffectVmDescriptor2,
    domain: u32,
) -> crate::descriptor_ir2::EffectVmDescriptor2 {
    let split = canonicity_splice_of(rotated);
    weld_umem_into_descriptor_with_suffix(rotated, domain, ROTATED_UMEM_WELD_SUFFIX, true, split)
}

/// **THE WIDE ROTATED+UMEM WELD (STAGED, VK-RISK-FREE) — the real flip precursor the VK epoch
/// needs.** Weld the universal-memory COHORT leg INTO a WIDE descriptor (a member of
/// [`WIDE_REGISTRY_STAGED_TSV`], the verified Lean `v3RegistryCapOpenWide`, carrying the two 60×8
/// BEFORE/AFTER carriers + the 16 wide commit PIs = the 8-felt ~124-bit before/after anchors).
///
/// IDENTICAL append shape to [`weld_umem_into_rotated_descriptor`] — the single-domain cohort
/// `umemOp` over 7 fresh main columns `[base .. base+7)` (`base` = the WIDE trace width, PAST the
/// wide carriers) plus the `umemory` / `umem_boundary` tables — but onto the WIDE base. **Crucially
/// it PRESERVES the wide descriptor's `public_input_count` AND every existing constraint (incl. all
/// 16 wide-commit `PiBinding`s), so the welded form keeps the 8-felt before/after anchors at the
/// SAME PI offsets (the leg's LAST 16 PIs) — NO narrowing.** The weld is purely ADDITIVE (it appends
/// columns / tables / one `umemOp` constraint and NEVER edits `public_input_count` or any PI
/// binding), which is exactly why a proof under the welded descriptor binds the ~124-bit commitment
/// identically to the wide descriptor — the no-narrowing scar the VK epoch refused to cross.
///
/// This is the genuine deployable flag-day weld: the per-map memory reconciliation moves INTO the
/// WIDE rotated descriptor as the universal-memory leg, while the WIDE PIs (the 8-felt commit
/// `verify_full_turn_bound` binds) stay intact. STAGED: a NEW descriptor BESIDE the deployed wide
/// registry — no VK bump, nothing on the live wire. `domain` is the cohort domain the welded effect
/// touches (heap 1 / caps 2 / nullifiers 3), checked against the leg's actual domain by the prover.
///
/// ⚑ THE SPLICE POSITION COMES FROM THE LEAN EMIT ([`UMEM_WELD_TABLE`]), keyed by the HOST's own
/// wire name — never from Rust arithmetic. See [`weld_umem_into_descriptor_with_suffix`]. A host
/// that is not a deployed wide member has no Lean-emitted contract row, so there is no defensible
/// place to put the op: this PANICS rather than guessing one, in every profile.
pub fn weld_umem_into_wide_descriptor(
    wide: &crate::descriptor_ir2::EffectVmDescriptor2,
    domain: u32,
) -> crate::descriptor_ir2::EffectVmDescriptor2 {
    let row = umem_weld_row_for_host(wide).unwrap_or_else(|| {
        panic!(
            "wide+umem weld: host '{}' ({} cols / {} PIs / {} constraints) matches NO row in the \
             Lean-emitted UMEM_WELD_TABLE, so the canonicity splice index is unknown. Every \
             deployed wide member has one; a host that does not is off-registry and must not be \
             welded (guessing the index would mint a DIFFERENT AIR under the same name).",
            wide.name,
            wide.trace_width,
            wide.public_input_count,
            wide.constraints.len()
        )
    });
    let welded = weld_umem_into_descriptor_with_suffix(
        wide,
        domain,
        WIDE_UMEM_WELD_SUFFIX,
        false,
        row.splice,
    );
    row.check(&welded);
    welded
}

/// **THE DERIVED WIDE+UMEM WELDED MEMBER** for a live registry `key` — what
/// `circuit/descriptors/rotation-wide-umem-welded-registry-staged.tsv` used to hand a verifier
/// pre-materialized, computed instead the way the PROVER has always computed it
/// ([`weld_umem_into_wide_descriptor`] over the bare wide member). `None` for a key with no wide
/// twin. Verified byte-for-byte against all 57 committed welded members before the TSV was deleted.
pub fn derive_welded_wide_member(key: &str) -> Option<crate::descriptor_ir2::EffectVmDescriptor2> {
    let row = umem_weld_row(key)?;
    let bare_json = WIDE_REGISTRY_STAGED_TSV.lines().find_map(|line| {
        let mut it = line.splitn(3, '\t');
        if it.next() == Some(key) {
            let _display = it.next();
            it.next()
        } else {
            None
        }
    })?;
    let bare = crate::descriptor_ir2::parse_vm_descriptor2(bare_json).ok()?;
    let welded = weld_umem_into_wide_descriptor(&bare, row.domain);
    // The weld resolved its row by the host's SHAPE (it is handed a descriptor, not a key). We hold
    // the KEY's row, so check against that one too: for a shape group with several members the two
    // rows agree by construction, and this is what makes "agree" a checked fact rather than a
    // reading of the table.
    row.check(&welded);
    Some(welded)
}

/// Every derived welded member, in registry order — the iteration the wire verifiers used to run
/// over the deleted TSV's lines.
pub fn welded_wide_members() -> Vec<(&'static str, crate::descriptor_ir2::EffectVmDescriptor2)> {
    UMEM_WELD_TABLE
        .iter()
        .filter_map(|row| derive_welded_wide_member(row.key).map(|d| (row.key, d)))
        .collect()
}

/// **THE WIDE ROTATED+UMEM MULTI-DOMAIN WELD (STAGED, VK-RISK-FREE) — the last family tail.** The
/// two-domain twin of [`weld_umem_into_wide_descriptor`]: weld the MULTI-DOMAIN umem cohort leg INTO
/// a WIDE descriptor (a member of [`WIDE_REGISTRY_STAGED_TSV`]). Where the single-domain weld appends
/// ONE `umemOp` over 7 fresh columns, this appends the FIXED multi-domain cohort shape (the verified
/// Lean `EffectVmEmitUMemCohortMulti.umemCohortDesc2`): `6 + domains.len()` fresh main columns
/// `[base .. base + 6 + domains.len())` — `base+0..base+5` shared (`key · present · value ·
/// prev_present · prev_value · prev_serial`), one PER-DOMAIN guard at `base + 6 + i` — and ONE
/// `umemOp` per touched domain (in the supplied COLUMN order, the producer's sorted-domain-code order
/// `{heap (1), nullifiers (3)}`), each guarded at its own column. The NOTE/BRIDGE economic verbs touch
/// TWO domains in one effect (a `nullifiers` freshness insert + a `heap` balance credit), on which the
/// single-domain weld fails closed; this is their WIDE weld.
///
/// IDENTICAL no-narrowing property to [`weld_umem_into_wide_descriptor`]: it PRESERVES
/// `public_input_count` AND every existing constraint (incl. all 16 wide-commit `PiBinding`s), so the
/// 8-felt before/after anchors ride through INTACT at the SAME PI offsets. The cross-DOMAIN economic
/// invariant (the credit == the spent/minted value) is NOT a memory-reconciliation property — it rides
/// the effect's own rotated AIR (the whole rotated constraint set the weld preserves), exactly as in the
/// narrow multi-domain cohort. STAGED: a NEW descriptor BESIDE the deployed wide registry — no VK bump,
/// nothing on the live wire. `domains` is the per-op domain set in column order (heap 1 / caps 2 /
/// nullifiers 3), checked against the leg's actual domains by the prover.
pub fn weld_umem_multidomain_into_wide_descriptor(
    wide: &crate::descriptor_ir2::EffectVmDescriptor2,
    domains: &[u32],
) -> crate::descriptor_ir2::EffectVmDescriptor2 {
    use crate::descriptor_ir2::{
        MemKind, TID_UMEM_BOUNDARY, TID_UMEMORY, TableDef2, TableSem, UMemOpSpec, VmConstraint2,
    };
    use crate::lean_descriptor_air::LeanExpr;

    // The first fresh universal-memory operand column (the base form occupies `[0, base)`).
    let base = wide.trace_width;
    let mut welded = wide.clone();
    welded.name = format!("{}{WIDE_UMEM_MULTIDOMAIN_WELD_SUFFIX}", wide.name);
    // Shared base cols 0..5 + one guard per domain.
    welded.trace_width = base + 6 + domains.len();
    for t in welded.tables.iter_mut() {
        if t.sem == TableSem::Main {
            t.arity = welded.trace_width;
        }
    }
    // The universal-memory tables: `umemory` (arity 8) + the GENERAL `umem_boundary` (arity 7) — the
    // multi-domain cohort reconciles 2+ `(domain,key)` cells, so the single-row cohort boundary
    // (whose `Nodup` is vacuous) does NOT apply; it carries the general lexicographic comparator (the
    // byte-pinned multi-domain cohort descriptor declares the general `umem_boundary`).
    welded.tables.push(TableDef2 {
        id: TID_UMEMORY,
        name: "umemory".to_string(),
        arity: 8,
        sem: TableSem::UMemory,
    });
    welded.tables.push(TableDef2 {
        id: TID_UMEM_BOUNDARY,
        name: "umem_boundary".to_string(),
        arity: 7,
        sem: TableSem::UMemBoundary,
    });
    // One welded universal-memory WRITE op per touched domain — byte-for-byte the multi-domain cohort
    // `umemOp` shape (shared key/value/prev cols, per-domain guard), offset to `base`.
    for (i, &domain) in domains.iter().enumerate() {
        welded.constraints.push(VmConstraint2::UMemOp(UMemOpSpec {
            guard: LeanExpr::Var(base + 6 + i),
            domain,
            key: LeanExpr::Var(base),
            present: LeanExpr::Var(base + 1),
            value: LeanExpr::Var(base + 2),
            prev_present: LeanExpr::Var(base + 3),
            prev_value: LeanExpr::Var(base + 4),
            prev_serial: LeanExpr::Var(base + 5),
            kind: MemKind::Write,
        }));
    }
    welded
}

/// The shared, purely-ADDITIVE umem-cohort weld (the body of both
/// [`weld_umem_into_rotated_descriptor`] and [`weld_umem_into_wide_descriptor`]): append the
/// single-domain cohort `umemOp` over 7 fresh main columns + the `umemory` / `umem_boundary` tables
/// onto `desc`, marking the result with `suffix`. It NEVER touches `public_input_count` nor any
/// existing constraint, so the base descriptor's whole PI vector + every PI binding survive
/// unchanged — the property that lets the WIDE weld keep the 16 wide-commit PIs (the 8-felt
/// ~124-bit anchors) intact.
///
/// `split` is the index the `umemOp` is INSERTED at. It is a caller obligation because the two
/// callers know it from different sources: the WIDE weld reads it out of the Lean emit
/// ([`UMEM_WELD_TABLE`]), the narrow rotated weld locates it with [`canonicity_splice_of`]. This
/// function only enforces that wherever it lands is genuinely the canonicity-block boundary — and
/// it enforces that in EVERY profile (see the note at the check).
fn weld_umem_into_descriptor_with_suffix(
    desc: &crate::descriptor_ir2::EffectVmDescriptor2,
    domain: u32,
    suffix: &str,
    cohort: bool,
    split: usize,
) -> crate::descriptor_ir2::EffectVmDescriptor2 {
    use crate::descriptor_ir2::{
        MemKind, TID_UMEM_BOUNDARY, TID_UMEMORY, TableDef2, TableSem, UMemOpSpec, VmConstraint2,
    };
    use crate::lean_descriptor_air::LeanExpr;

    // The first fresh universal-memory operand column (the base form occupies `[0, base)`).
    let base = desc.trace_width;
    let mut welded = desc.clone();
    welded.name = format!("{}{suffix}", desc.name);
    welded.trace_width = base + 7;
    // Widen the MAIN table arity (sem `Main`) to the welded width; the rotated chip/range/memory/
    // map tables keep their arities (the umem leg adds its own tables, below).
    for t in welded.tables.iter_mut() {
        if t.sem == TableSem::Main {
            t.arity = welded.trace_width;
        }
    }
    // Declare the universal-memory tables (the cohort emitter shape: `umemory` arity 8 carries the
    // domain-tagged Blum tuple + serial/gap lanes; `umem_boundary` arity 7 the declared
    // `(domain,key)` init/final image).
    welded.tables.push(TableDef2 {
        id: TID_UMEMORY,
        name: "umemory".to_string(),
        arity: 8,
        sem: TableSem::UMemory,
    });
    // The cohort weld declares the SINGLE-ROW boundary specialization: at most one declared
    // `(domain,key)` cell ⇒ the inter-row comparator + key decomposition are dropped (width 9 vs
    // 38; `Nodup` is free). The arity stays 7 (the witness-supplied init/final image shape is
    // unchanged); only the AIR routing + assembled trace width differ.
    welded.tables.push(TableDef2 {
        id: TID_UMEM_BOUNDARY,
        name: if cohort {
            "umem_boundary_cohort".to_string()
        } else {
            "umem_boundary".to_string()
        },
        arity: 7,
        sem: if cohort {
            TableSem::UMemBoundaryCohort
        } else {
            TableSem::UMemBoundary
        },
    });
    // The single welded universal-memory WRITE op over the appended 7 columns — the shape the Lean
    // `EffectVmEmitUMemCohort.umemCohortDesc` models, offset to `base`.
    let op = VmConstraint2::UMemOp(UMemOpSpec {
        guard: LeanExpr::Var(base + 6),
        domain,
        key: LeanExpr::Var(base),
        present: LeanExpr::Var(base + 1),
        value: LeanExpr::Var(base + 2),
        prev_present: LeanExpr::Var(base + 3),
        prev_value: LeanExpr::Var(base + 4),
        prev_serial: LeanExpr::Var(base + 5),
        kind: MemKind::Write,
    });
    // ⚑ SPLICED BEFORE THE TRAILING FIELDS-CANONICITY BLOCK, NOT APPENDED (2026-07-31).
    //
    // `EmitWideUMemWeldRegistryProbe.lean` applies `fieldsCanonical9Wire` to the ALREADY-welded
    // member, so on the wire the canonicity block is OUTERMOST and the `umemOp` sits at the
    // boundary between the host constraints and it. A bare `push` puts the op AFTER the canonicity
    // block and the two descriptors then differ by a permutation — which is not cosmetic:
    // `MainLayout::build` walks the constraint list in order to assign every range/submask aux
    // column, so a reordered list is a DIFFERENT AIR and a different VK.
    //
    // ⚑ THE BOUNDARY CHECK RUNS IN EVERY PROFILE (2026-07-31). It was a `debug_assert!` — a
    // fail-closed check compiled out of exactly the builds that ship — sitting under a `split`
    // Rust recomputed as `constraints.len() - 2 * 8 * (7 + 12)`. Both halves are gone: the WIDE
    // caller now takes `split` from the Lean emit's own `umemweld` contract row, and what remains
    // here is a real assertion that the index lands on the canonicity boundary (a row-local gate
    // first, a range lookup last). It is O(1) beside a whole-descriptor clone, so there was never
    // a cost reason for it to be debug-only.
    assert!(
        split < welded.constraints.len()
            && matches!(welded.constraints[split], VmConstraint2::WindowGate(_))
            && matches!(
                welded.constraints[welded.constraints.len() - 1],
                VmConstraint2::Lookup(_)
            ),
        "umem weld splice {split} of '{}' ({} constraints) is not the fields-canonicity boundary \
         (want a row-local gate at the splice and a range lookup last). The emit's shape and this \
         splice have diverged; move the splice with it rather than welding a different AIR under \
         the same name.",
        desc.name,
        welded.constraints.len()
    );
    welded.constraints.insert(split, op);
    welded
}

/// The number of constraints the Lean `fieldsCanonical9Wire` appends: two blocks of eight slots,
/// each slot contributing seven row-local gates and twelve range lookups.
///
/// ⚠ NAMED RESIDUAL. For the deployed WIDE members this number is NOT used — their splice comes
/// straight out of the Lean emit ([`UMEM_WELD_TABLE`]). It survives only for the STAGED NARROW
/// rotated weld, which has no committed registry and therefore no emitted contract row, so its
/// splice is still a Rust-side reconstruction of a Lean fact. The always-on boundary check in
/// [`weld_umem_into_descriptor_with_suffix`] is what keeps that reconstruction from failing
/// silently; the way to retire it is a `umemweld`-style companion line from the narrow emit, not a
/// second copy of this arithmetic.
const CANON9_BLOCK_LEN: usize = 2 * 8 * (7 + 12);

/// The splice index for a host with NO Lean-emitted contract row — the STAGED narrow rotated weld.
/// See [`CANON9_BLOCK_LEN`] for why this is a residual rather than the general mechanism.
fn canonicity_splice_of(desc: &crate::descriptor_ir2::EffectVmDescriptor2) -> usize {
    desc.constraints
        .len()
        .checked_sub(CANON9_BLOCK_LEN)
        .unwrap_or_else(|| {
            panic!(
                "umem weld: '{}' has {} constraints, fewer than the {CANON9_BLOCK_LEN}-constraint \
                 fields-canonicity block it must splice before",
                desc.name,
                desc.constraints.len()
            )
        })
}

// ⚑ DELETED 2026-07-31 — `WIDE_TRANSFER_STAGED_TSV` /
// `circuit/descriptors/rotation-wide-transfer-staged.tsv` (one row, 136 KB, key
// `transferVmDescriptor2R24Wide`), together with its Lean driver
// `metatheory/EmitWideTransferProbe.lean` and its producer
// `trace_rotated::generate_rotated_transfer_wide`.
//
// It was a committed FORK of `WIDE_REGISTRY_STAGED_TSV` row 0 that had already diverged: the
// deployed row 0 is availability-hardened, carries the two membership-claim PIs, carries the
// gentian capacity-floor refuse weld and is E1-compacted; the fork was NONE of those (width
// 1819 / 66 PIs vs the deployed 1782 / 68, and 560 of its 619 constraints appear nowhere in the
// deployed member). `EmitWideRegistryProbe.lean` still described it as "byte-identical (row 0)".
//
// It had ZERO production consumers — three test sites read it, and its producer had no callers
// outside those tests. Two of those tests were the only prove+verify roundtrip and the only
// 8-felt high-position collision tooth for transfer, so BOTH pointed at a descriptor no verifier
// resolves and a producer nothing ships. That is the reason to delete rather than keep: the fork
// was absorbing transfer's collision tooth and thereby ensuring it never pointed at the deployed
// face. Removing it does not lower assurance on the deployed member — it stops a dead object from
// reading as coverage of one. Re-pointing that tooth at the deployed row 0 (which needs the
// avail-shifted, refuse-welded producer, not `generate_rotated_transfer_wide`) is now a visible,
// nameable gap instead of an invisible one.

/// **THE DEPLOYED 8-FELT REGISTRY.** ⚑ READ THIS FIRST IF THE WORD `staged` HAS CONFUSED YOU. This
/// is the registry the deployed light client and executor actually resolve members from
/// (`turn/src/executor/proof_verify.rs::verify_one_cohort_run`,
/// `sdk/src/full_turn_proof.rs::verify_effect_vm_rotated_inner`), and — with
/// [`UMEM_WELD_TABLE_FP`] — it IS the VK-epoch identity
/// (`dregg_epoch::local_manifest`'s `registry_fp` is exactly these two fingerprints).
///
/// The `staged` in the filename and the "ADDITIVE / parallel path beside the live 1-felt registry"
/// language below are LEFT OVER FROM BEFORE THE WIDE FLAG DAY and are now backwards. `staged` once
/// meant "beside the deployed 1-felt V3 registry"; the wide flag day repointed every deployed
/// producer and verifier here, so the set named `staged` became the deployed one and
/// `V3_STAGED_REGISTRY_TSV` — the set the word was contrasting against — became the retired
/// stratum that no production verify path reads. The word survived its own contrast class and then
/// inverted. Nothing branches on it (no code parses `staged` out of a filename or a member name),
/// so it costs a reader a lookup and nothing else; it dies at the next re-emit that renames the
/// files, not before.
///
/// A member-for-member, name-stable
/// COVER of the V3 registry (`rotation-v3-staged-registry.tsv`, 57 members) made 8-felt-wide:
/// each live member wrapped through the proven `wideAppend host bb (bb+51)` at its real per-member
/// BEFORE-limb base `bb` (the underlying v1 FACE width). The `key\tname\tjson` per line (key = the
/// live registry key, e.g. `burnVmDescriptor2R24`), emitted from the verified Lean
/// `CapOpenEmit.v3RegistryCapOpenWide` + the WRITE-bearing tail + the three live-only members
/// (`transferCapOpenTB` / `heapWrite` / `supplyMint`), in the LIVE order
/// (`metatheory/EmitWideRegistryProbe.lean`). `grantCapWriteCapOpen` is reconciled OUT (it is not a
/// live `V3_STAGED_REGISTRY_TSV` member). ADDITIVE: the live 1-felt `V3_STAGED_REGISTRY_TSV` / FP / VK
/// are UNTOUCHED — this is the parallel wide path beside them. The transfer row (row 0) carries the
/// two `(sender_leaf, authorized_root)` membership-claim PI SLOTS and their teeth columns, and is
/// pinned ABSOLUTELY at 1782 cols / 68 PIs by `WIDE_MEMBER_GEOMETRY`.
/// ⚑ This said "+ the row-0 PI pin" until 2026-08-01. There is NO such pin: measured on these very
/// bytes, PI 50 and 51 have no `pi_binding`, and the teeth columns (1735/1736) are read by no
/// constraint. The slots are carried; the binding is not. Same for `mintVmDescriptor2R24` PI 46,
/// whose `prmCol 0` (col 68) is not referenced at all. Five of the seven carriers ARE pinned and
/// forced (custom 46/54, sovereign 58, factory 47, hatchery 55) — membership and bridge are the
/// two outliers, and `carrier_forgery_forge.rs` is RED on exactly those two. (It used to be
/// described as "the advance of `WIDE_TRANSFER_STAGED_TSV`" — that single-line fork was DELETED
/// 2026-07-31; it had diverged and no verifier resolved it.)
/// The wide carriers land PAST each member's host width, re-absorbing the SAME rotated limbs the
/// 1-felt block lays into a genuine 8-felt (~124-bit) commitment, carrying the 16 wide commit PIs =
/// the 8-felt before/after anchors. The committed width is NO LONGER host + the 960-column
/// `trace_rotated::WIDE_CARRIER_APPENDIX`: the S2 flag-day (`4dd3273bd2`) and the E1 per-member
/// dead-column compaction (`bd21266e6b` / `3ebf42e25f`) drop each member's own kill-set, so the
/// width is a PER-MEMBER fact — pinned member-by-member by the drift tooth in
/// `wide_registry_parses_and_is_name_stable`.
pub const WIDE_REGISTRY_STAGED_TSV: &str =
    include_str!("../descriptors/rotation-wide-registry-staged.tsv");
pub const WIDE_REGISTRY_STAGED_FP: &str =
    "66cb248ed9ce636a796944f1342399427b37176fc67aa9e7d7a95efa08b47417";

/// **THE LEAN-EMITTED WIDE+UMEM WELDED REGISTRY (STAGED, VK-RISK-FREE) — the WIDE+umem weld's
/// MISSING VERIFIER LEG.** A member-for-member, name-stable welded twin of the wire's WIDE cap-open
/// registry: the 45 AUTHORITY-crown emit-source members (`CapOpenEmit.v3RegistryCapOpenWide`) PLUS
/// the 9 §10 WRITE-bearing cap-open tail wrappers (`CapOpenEmit.v3RegistryCapOpenWriteWide` minus
/// `grantCapWriteCapOpen`, which has no bare wide twin) — the `…WriteCapOpenVmDescriptor2R24`
/// descriptors the deployed wire routes a cap WRITE turn to (delegate / introduce / refresh / revoke
/// (Delegation/Capability) / spawn-via-cap). Each member is welded with the universal-memory cohort
/// leg (`umemOp` over 7 fresh columns PAST the wide carriers + the `umemory` / `umem_boundary`
/// tables) at the domain its effect touches, emitted from the verified Lean
/// `EffectVmEmitUMemWeldWide.weldedWideRegistry` (driver `metatheory/EmitWideUMemWeldRegistryProbe.lean`).
/// The `key\tname\tjson` per line; the KEY is the LIVE registry key (`transferVmDescriptor2R24` /
/// `delegateWriteCapOpenVmDescriptor2R24` etc.), the NAME carries [`WIDE_UMEM_WELD_SUFFIX`].
///
/// The weld is purely ADDITIVE — it appends columns / tables / one `umemOp` and NEVER edits
/// `public_input_count` nor any PI binding — so every welded member keeps the 16 wide-commit PIs
/// (the 8-felt ~124-bit before/after anchors) at the SAME offsets (NO narrowing). A welded proof
/// from [`prove_wide_umem_welded_staged`] verifies UNIQUELY against its member here (the Lean weld is
/// byte-parity-pinned to the Rust [`weld_umem_into_wide_descriptor`] — the `wide_umem_weld_registry_*`
/// tests). This is the descriptor set the wire verifiers (`verify_effect_vm_rotated_with_cutover`,
/// the IVC `admit_welded_leg`) iterate as a NEW accepted form BESIDE the bare wide registry. ADDITIVE:
/// the live 1-felt / bare wide registries / FP / VK are UNTOUCHED; `umem_witness_enabled` stays false.
///
/// ⚑ **THE SET IS NOW DERIVED, NOT SHIPPED (2026-07-31).** `WIDE_UMEM_WELD_REGISTRY_TSV` /
/// `circuit/descriptors/rotation-wide-umem-welded-registry-staged.tsv` (10,049,999 bytes) and
/// `WIDE_UMEM_WELD_REGISTRY_FP` are DELETED. The file was a member-for-member 57/57 cover of
/// [`WIDE_REGISTRY_STAGED_TSV`] under one purely-additive transform, so — over and above the bare
/// wide registry, which is still committed and FP-pinned — it carried only the per-member
/// `(domain, splice index, shape)` rows now in [`UMEM_WELD_TABLE`], ~8 KB against 10 MB.
///
/// It was also, already, a pre-materialized copy of something the deployed PROVER computed at
/// runtime and never opened the file for (`sdk::full_turn_proof`'s
/// `weld_umem_into_wide_descriptor(&wide_desc, domain)`), so the two halves of the wire were
/// deriving and shipping the SAME object. Now both derive it. Use
/// [`derive_welded_wide_member`] / [`welded_wide_members`].
///
/// Verified before deletion, twice and independently: every one of the 57 committed welded members
/// equals `weld_umem_into_wide_descriptor(bare_wide[key], table[key].domain)` — once through
/// `descriptor_ir2_canonical::canonical_effect_vm_descriptor2_bytes` in Rust, once through a
/// standalone JSON re-derivation outside this crate. 57/57 both times.
pub const UMEM_WELD_TABLE: &[UMemWeldRow] = crate::effect_vm::umem_weld_generated::UMEM_WELD_TABLE;

/// The byte identity of the welded descriptor set — sha256 of the Lean `umemweld` companion lines
/// [`UMEM_WELD_TABLE`] is rendered from. Replaces the deleted `WIDE_UMEM_WELD_REGISTRY_FP` (sha256
/// of the deleted TSV) in `dregg_epoch::local_manifest`'s `registry_fp`, so a re-emit that moves any
/// member's domain or splice still moves the handshake identity.
pub const UMEM_WELD_TABLE_FP: &str = crate::effect_vm::umem_weld_generated::UMEM_WELD_TABLE_FP;

/// One Lean-emitted derivation-contract row: everything `weld_umem_into_wide_descriptor` needs on
/// top of a bare wide member, plus the welded shape the result is checked against.
///
/// The fields are the `umemweld\t…` companion line `EmitWideUMemWeldRegistryProbe.lean` prints, in
/// order. See `circuit/src/effect_vm/umem_weld_generated.rs` for what each one pins.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct UMemWeldRow {
    /// The LIVE registry key (`transferVmDescriptor2R24`), shared with [`WIDE_REGISTRY_STAGED_TSV`].
    pub key: &'static str,
    /// The universal-memory plane this member's effect reconciles (heap 1 / caps 2).
    pub domain: u32,
    /// Where the `umemOp` sits in the welded constraint list — LOCATED by the Lean emit.
    pub splice: usize,
    /// The welded member's trace width (host + 7).
    pub trace_width: usize,
    /// The welded member's PI count — equal to the host's (the weld never narrows).
    pub pi_count: usize,
    /// The welded member's constraint count (host + 1).
    pub constraints: usize,
    /// The welded member's wire name (the host's name + [`WIDE_UMEM_WELD_SUFFIX`]).
    pub name: &'static str,
}

impl UMemWeldRow {
    /// Check a freshly-derived welded member against every quantity this row pins. Runs on EVERY
    /// construction and in EVERY profile — a table that has drifted from the emit goes red here
    /// rather than quietly minting a different AIR under a committed name.
    fn check(&self, welded: &crate::descriptor_ir2::EffectVmDescriptor2) {
        assert!(
            welded.name == self.name
                && welded.trace_width == self.trace_width
                && welded.public_input_count == self.pi_count
                && welded.constraints.len() == self.constraints
                && matches!(
                    welded.constraints.get(self.splice),
                    Some(crate::descriptor_ir2::VmConstraint2::UMemOp(_))
                ),
            "derived welded member for {} does not match its Lean contract row: got name={} \
             width={} pi={} constraints={}, want name={} width={} pi={} constraints={} with the \
             umemOp at index {}",
            self.key,
            welded.name,
            welded.trace_width,
            welded.public_input_count,
            welded.constraints.len(),
            self.name,
            self.trace_width,
            self.pi_count,
            self.constraints,
            self.splice
        );
    }
}

/// The Lean contract row for a live registry `key`, or `None` if the key has no welded twin.
pub fn umem_weld_row(key: &str) -> Option<&'static UMemWeldRow> {
    UMEM_WELD_TABLE.iter().find(|r| r.key == key)
}

/// The Lean contract row for a HOST DESCRIPTOR — the lookup [`weld_umem_into_wide_descriptor`] uses,
/// which holds the wide member but not its registry key.
///
/// ⚑ THE NAME IS NOT A KEY, and resolving on it alone is a bug this repo has already paid for once
/// (`trace_rotated::wide_registry_key_for_descriptor_name` refuses for the same reason).
/// `attenuateVmDescriptor2R24` and `revokeCapabilityVmDescriptor2R24` are BOTH
/// `dregg-effectvm-attenuateA-v1-genuine-norecompute-tick-…` and their descriptors are NOT the same
/// object — 559 constraints against 558 — so a name-only lookup silently welds one member at the
/// other's splice. (Measured: the first draft of this function did exactly that, and the always-on
/// contract check below is what caught it.)
///
/// So the lookup is on the host's whole observable SHAPE, and candidates that disagree on the
/// splice REFUSE instead of picking one. Measured over the deployed set: 50 shape groups, the only
/// multi-member one being the 8 `setFieldVmDescriptor2-{slot}R24` twins, which agree on splice and
/// domain (they differ in which columns their pins name, not in any count).
fn umem_weld_row_for_host(
    host: &crate::descriptor_ir2::EffectVmDescriptor2,
) -> Option<&'static UMemWeldRow> {
    let candidates: Vec<&'static UMemWeldRow> = UMEM_WELD_TABLE
        .iter()
        .filter(|r| {
            r.name.len() == host.name.len() + WIDE_UMEM_WELD_SUFFIX.len()
                && r.name.starts_with(host.name.as_str())
                && r.name.ends_with(WIDE_UMEM_WELD_SUFFIX)
                && r.trace_width == host.trace_width + 7
                && r.pi_count == host.public_input_count
                && r.constraints == host.constraints.len() + 1
        })
        .collect();
    let first = *candidates.first()?;
    assert!(
        candidates.iter().all(|r| r.splice == first.splice),
        "wide+umem weld: host '{}' ({} constraints) matches {} contract rows that DISAGREE on the \
         canonicity splice ({:?}). The shape no longer determines the splice; the weld must be \
         resolved by registry KEY at the call site rather than guessing one.",
        host.name,
        host.constraints.len(),
        candidates.len(),
        candidates
            .iter()
            .map(|r| (r.key, r.splice))
            .collect::<Vec<_>>()
    );
    Some(first)
}

/// Every registry key whose derived welded member carries `welded_name` — the reverse of
/// [`umem_weld_row`], for a verifier holding a carried welded descriptor and no key.
///
/// ⚠ Returns a LIST, not an `Option`. Several registry keys share one display name
/// (`attenuateVmDescriptor2R24` and `revokeCapabilityVmDescriptor2R24` are both
/// `dregg-effectvm-attenuateA-v1-genuine-…`, and so are their welded twins), and they do NOT
/// necessarily carry the same geometry — see `trace_rotated::wide_registry_key_for_descriptor_name`,
/// which refuses for the same reason. A caller that picked `find(..)` would silently test one
/// candidate and reject a leg carrying the other.
pub fn umem_weld_keys_for_welded_name(welded_name: &str) -> Vec<&'static str> {
    UMEM_WELD_TABLE
        .iter()
        .filter(|r| r.name == welded_name)
        .map(|r| r.key)
        .collect()
}

/// The number of written-slot completion lanes the deployed setField members publish (the VALUE8
/// weld — the high bits of the written 32-byte field value).
///
/// ⚑ 7 → 8 AT THE NINE-LANE EPOCH (2026-07-31). The fields octet became a fields NONET: slot `j`
/// gained a NINTH lane at the new column `176 + j` (`RotatedLayout.fieldLaneCol slot 8`), so the
/// deployed members now pin lanes 1..=8 at PIs `[SETFIELD_VALUE8_PI_BASE, +8)` — verified against
/// the emitted bytes: `setFieldVmDescriptor2-0R24` pins the first seven to the contiguous window
/// `after_base + 113..=119` and the eighth to `after_base + 176`, the non-contiguous ninth lane.
/// (Those PIs were 46..=53 until the 2026-08-07 seven-slot compaction, and are 39..=46 now.)
/// That eighth pin is the whole
/// point of the epoch — with seven, the top of the value was still unbound on the wire.
pub const SETFIELD_VALUE8_PI_LEN: usize = 8;

/// The PI slot the deployed setField members' VALUE8 completion pins start at: immediately past
/// the rotated prefix, BEFORE the 4 dsl rc pins (Lean `withDfaRcPins (gentianDeployedBareRefuse
/// (withSetFieldCompletionPins slot …))` — rc rides outermost, so the value8 block is interior).
/// Derived from `ROT_PI_COUNT`; it was the literal `46` until the 2026-08-07 seven-slot PI
/// compaction took `V1_PI_COUNT` 42 → 35 (`docs/PI-DISPOSITION.md` §6).
pub const SETFIELD_VALUE8_PI_BASE: usize = crate::effect_vm::trace_rotated::ROT_PI_COUNT;

/// The IN-BLOCK offset of `fields[0]`'s first completion lane, so `fields[slot]`'s freed lanes are
/// `SETFIELD_VALUE8_LANE_BASE + 7·slot ..= +6` (Lean `setFieldCompletionBase`). ⚠ 113, not 112 — the
/// REVOKED-ROOT flag-day shifted the fields completion octet by one limb (`cell/src/commitment.rs`
/// is the authority); a base one lane low aims at the neighbouring slot.
pub const SETFIELD_VALUE8_LANE_BASE: usize = 113;

/// **THE setField VALUE8 PRODUCER SPLICE — the witness half of the deployed VALUE8 weld.**
///
/// The deployed `setFieldVmDescriptor2-{slot}R24` (Lean `v3RegistryBare`, freeze-EXCEPT +
/// `withSetFieldCompletionPins slot`) publishes the WRITTEN slot's 7 freed completion lanes as PIs
/// `46..=52`, so the light client reads the written field's high 224 bits off the PI vector. The
/// rotated generators build the 46-PI prefix + the 4 rc pins and know nothing about the per-member
/// tail, so this splices the 7 value8 PIs into position for a setField member.
///
/// It is **descriptor-driven, not column-arithmetic**: each spliced value is read out of the trace at
/// the column the descriptor's OWN `.piBinding .last` constraint names for that PI slot. That is what
/// makes it correct on BOTH the 1-felt member (`piCount 57`) and the S2/E1-**compacted** wide members
/// (`piCount 73`), whose completion columns are remapped by the compaction — no producer-side copy of
/// the layout exists to drift.
///
/// A no-op unless the descriptor genuinely wants exactly [`SETFIELD_VALUE8_PI_LEN`] more PIs than the
/// generator produced. Fails CLOSED (`Err`) if the descriptor wants them but does not pin them — a
/// silently short PI vector would be an UNSAT proof at best and an unbound high-224-bit field at worst.
pub fn splice_setfield_value8_pis(
    desc: &crate::descriptor_ir2::EffectVmDescriptor2,
    trace: &[Vec<crate::field::BabyBear>],
    dpis: Vec<crate::field::BabyBear>,
) -> Result<Vec<crate::field::BabyBear>, String> {
    use crate::descriptor_ir2::VmConstraint2;
    use crate::lean_descriptor_air::{VmConstraint, VmRow};
    if desc.public_input_count != dpis.len() + SETFIELD_VALUE8_PI_LEN
        || dpis.len() < SETFIELD_VALUE8_PI_BASE
    {
        return Ok(dpis);
    }
    let Some(last) = trace.last() else {
        return Err("setField VALUE8 splice: empty trace".to_string());
    };
    let pin_col = |pi: usize| -> Option<usize> {
        desc.constraints.iter().find_map(|c| match c {
            VmConstraint2::Base(VmConstraint::PiBinding {
                row: VmRow::Last,
                col,
                pi_index,
            }) if *pi_index == pi => Some(*col),
            _ => None,
        })
    };
    let mut out = dpis[..SETFIELD_VALUE8_PI_BASE].to_vec();
    for k in 0..SETFIELD_VALUE8_PI_LEN {
        let pi = SETFIELD_VALUE8_PI_BASE + k;
        let col = pin_col(pi).ok_or_else(|| {
            format!(
                "setField VALUE8 splice: '{}' declares {} PIs (7 past the generator's {}) but pins \
                 no last-row column at PI {pi} — refusing to publish an unbound completion lane",
                desc.name,
                desc.public_input_count,
                dpis.len()
            )
        })?;
        let v = *last.get(col).ok_or_else(|| {
            format!(
                "setField VALUE8 splice: '{}' pins PI {pi} at column {col}, past the trace width {}",
                desc.name,
                last.len()
            )
        })?;
        out.push(v);
    }
    out.extend_from_slice(&dpis[SETFIELD_VALUE8_PI_BASE..]);
    Ok(out)
}

// ============================================================================
// THE WIDE-CARRIER GEOMETRY VERSION BOUNDARY (the flag-day rotation, v2).
//
// v1 (RETIRED): 169 pre-iroot limbs → 57 carriers → 456-column block span → 912-column
//   appendix, commit carrier 56.
// v2 (LIVE):    178 pre-iroot limbs → 60 carriers → 480-column block span → 960-column
//   appendix, commit carrier 59 (`trace_rotated::WIDE_NUM_CARRIERS` et al., derived from
//   `NUM_PRE_LIMBS` by the shared `wide_carriers_for_limbs`).
//
// This is an APPROVED FLAG-DAY rotation: there is NO compatibility shim at the same
// assurance rung. A carried v1 registry member / VK-bearing descriptor is refused HERE with
// a TYPED error (`WideGeometryVersionError::RetiredV1`), never silently accepted or silently
// widened. The detector is STRUCTURAL and shift-invariant: it reads the descriptor's own 16
// wide anchor pins (the LAST 16 PI slots — 8 first-row BEFORE-commit columns, 8 last-row
// AFTER-commit columns) and measures the carrier BLOCK SPAN as the column distance between
// the BEFORE and AFTER commit carriers, which appended tails (umem welds, teeth, digest
// appendixes, refuse welds) never move.
// ============================================================================

/// The LIVE wide-carrier geometry version (see the boundary note above).
pub const WIDE_CARRIER_GEOMETRY_VERSION: u32 = 2;
/// The RETIRED v1 per-block carrier span (57 carriers × 8 = 456 columns over the 169-limb body).
pub const WIDE_CARRIER_BLOCK_SPAN_RETIRED_V1: usize = 456;

/// Typed refusal at the wide-carrier geometry-version boundary.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum WideGeometryVersionError {
    /// The artifact carries the RETIRED v1 (57-carrier / 456-block-span / 912-appendix)
    /// carrier shape. Old registries/VKs are version-refused, not widened.
    RetiredV1 {
        /// The presented descriptor's name.
        name: String,
        /// The measured BEFORE→AFTER commit-carrier span (456 for v1).
        block_span: usize,
    },
    /// The artifact's anchor pins measure a block span that matches NO known wide-carrier
    /// geometry version (neither the live v2 nor the retired v1).
    UnknownGeometry {
        /// The presented descriptor's name.
        name: String,
        /// The measured BEFORE→AFTER commit-carrier span.
        block_span: usize,
    },
    /// The artifact claims a wide PI tail but its 16 wide anchor pins are missing or
    /// malformed (no first-row BEFORE / last-row AFTER commit pins at the tail slots).
    MissingAnchors {
        /// The presented descriptor's name.
        name: String,
    },
}

impl core::fmt::Display for WideGeometryVersionError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::RetiredV1 { name, block_span } => write!(
                f,
                "'{name}': RETIRED wide-carrier geometry v1 (block span {block_span} = 57 \
                 carriers; the live version is v{WIDE_CARRIER_GEOMETRY_VERSION}: 60 carriers / \
                 480-column block / commit carrier 59) — old registries/VKs are version-refused, \
                 not silently widened"
            ),
            Self::UnknownGeometry { name, block_span } => write!(
                f,
                "'{name}': wide anchor pins measure carrier block span {block_span}, which is \
                 no known wide-carrier geometry version (live v{WIDE_CARRIER_GEOMETRY_VERSION} \
                 = 480; retired v1 = {WIDE_CARRIER_BLOCK_SPAN_RETIRED_V1})"
            ),
            Self::MissingAnchors { name } => write!(
                f,
                "'{name}': wide-shaped descriptor is missing its 16 wide anchor pins (no \
                 first-row BEFORE / last-row AFTER commit pins at the PI tail)"
            ),
        }
    }
}

impl std::error::Error for WideGeometryVersionError {}

/// **The structural wide-carrier geometry-version detector.** Reads the descriptor's own 16
/// wide anchor pins — the LAST 16 PI slots, of which slot `piCount-16` is the first-row
/// BEFORE-commit lane-0 pin and slot `piCount-8` the last-row AFTER-commit lane-0 pin — and
/// measures the carrier BLOCK SPAN as `after_col - before_col`. That span is exactly
/// `WIDE_NUM_CARRIERS × 8` for every `wideAppend`-derived member and is INVARIANT under every
/// appended tail (umem weld columns, teeth columns, digest appendixes, refuse welds), so it
/// classifies any carried wide artifact regardless of composition:
///
/// * `Ok(WIDE_CARRIER_GEOMETRY_VERSION)` — the live v2 span (480);
/// * `Err(RetiredV1)` — the retired v1 span (456): explicit version refusal;
/// * `Err(UnknownGeometry)` / `Err(MissingAnchors)` — fail closed on anything else.
pub fn wide_carrier_geometry_version(
    d: &crate::descriptor_ir2::EffectVmDescriptor2,
) -> Result<u32, WideGeometryVersionError> {
    use crate::descriptor_ir2::VmConstraint2;
    use crate::effect_vm::trace_rotated::WIDE_CARRIER_BLOCK_SPAN;
    use crate::lean_descriptor_air::{VmConstraint, VmRow};
    let pi = d.public_input_count;
    if pi < 16 {
        return Err(WideGeometryVersionError::MissingAnchors {
            name: d.name.clone(),
        });
    }
    let mut before0: Option<usize> = None; // first-row pin of PI slot pi-16 (BEFORE lane 0)
    let mut after0: Option<usize> = None; // last-row pin of PI slot pi-8 (AFTER lane 0)
    for c in &d.constraints {
        if let VmConstraint2::Base(VmConstraint::PiBinding { row, col, pi_index }) = c {
            match row {
                VmRow::First if *pi_index == pi - 16 => before0 = Some(*col),
                VmRow::Last if *pi_index == pi - 8 => after0 = Some(*col),
                _ => {}
            }
        }
    }
    let (Some(b), Some(a)) = (before0, after0) else {
        return Err(WideGeometryVersionError::MissingAnchors {
            name: d.name.clone(),
        });
    };
    let Some(block_span) = a.checked_sub(b) else {
        return Err(WideGeometryVersionError::MissingAnchors {
            name: d.name.clone(),
        });
    };
    if block_span == WIDE_CARRIER_BLOCK_SPAN {
        Ok(WIDE_CARRIER_GEOMETRY_VERSION)
    } else if block_span == WIDE_CARRIER_BLOCK_SPAN_RETIRED_V1 {
        Err(WideGeometryVersionError::RetiredV1 {
            name: d.name.clone(),
            block_span,
        })
    } else {
        Err(WideGeometryVersionError::UnknownGeometry {
            name: d.name.clone(),
            block_span,
        })
    }
}

/// **The v2 admission gate** — `Ok(())` iff the carried wide artifact rides the LIVE
/// wide-carrier geometry version. Every wide acceptance boundary (the IVC `admit_welded_leg`,
/// registry consumers) calls THIS, so the retired 57/56 shape is refused with the typed
/// [`WideGeometryVersionError`], never silently admitted.
pub fn require_wide_carrier_geometry_v2(
    d: &crate::descriptor_ir2::EffectVmDescriptor2,
) -> Result<(), WideGeometryVersionError> {
    wide_carrier_geometry_version(d).map(|_| ())
}

// ============================================================================
// THE CUSTOM PROOF-BIND CARRIER VERSION BOUNDARY (the faithful flag-day rotation, v3).
//
// v1 (RETIRED): the Custom member published a 4-felt `custom_proof_commitment`
//   (~62-bit birthday collision resistance) — 8 exposure pins total: commit limbs
//   0..4 (cols `PARAM_BASE+4..8`) at the exposure base, then the 4 low vk-hash
//   limbs (cols `PARAM_BASE..+4`) immediately after.
// v2 (RETIRED): the full 8-felt `WideHash` commitment, but only low4 of program VK.
// v3 (LIVE): 16 exposure
//   pins: commit limbs 0..4 (cols `PARAM_BASE+4..8`), commit limbs 4..8 (the
//   member-local COMMIT-TEETH columns past the host,
//   `trace_rotated::CUSTOM_COMMIT_TEETH_BASE`), then VK limbs 0..4 in params and
//   VK limbs 4..8 in member-local `CUSTOM_VK_TEETH_BASE` columns.
//
// APPROVED FLAG-DAY rotation (proof-bridge upstream blocker #2): NO compatibility
// shim at the same assurance rung. A carried v1 custom descriptor / VK is refused
// HERE with a TYPED error (`CustomCommitVersionError::RetiredV1`), never silently
// accepted, zero-padded, or widened. The detector is STRUCTURAL and
// shift-invariant: it locates the commitment exposure block by the FIRST-row pin
// of column `PARAM_BASE + CUSTOM_PROOF_COMMIT_BASE` (commit limb 0) and
// classifies the pins at the four slots after the low commit block — the v1
// layout puts the VK block there (param columns); v2 puts the commit teeth
// (non-param columns) there, with the VK block after.
// ============================================================================

/// The LIVE custom proof-bind commitment version (see the boundary note above).
pub const CUSTOM_COMMIT_VERSION: u32 = 3;
/// The RETIRED v1 commitment width (felts).
pub const CUSTOM_COMMIT_WIDTH_RETIRED_V1: usize = 4;
/// The full commitment width introduced by v2 and retained by live carrier v3 (felts).
pub const CUSTOM_COMMIT_WIDTH_V2: usize = 8;

/// Typed refusal at the custom proof-bind commitment version boundary.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CustomCommitVersionError {
    /// The artifact publishes the RETIRED v1 4-felt `custom_proof_commitment`
    /// (the VK block rides directly after the low commit limbs — no commit
    /// teeth). Old custom descriptors/VKs are version-refused, not widened.
    RetiredV1 {
        /// The presented descriptor's name.
        name: String,
        /// The exposure block's commitment PI base (slot of commit limb 0).
        commit_pi_lo: usize,
    },
    /// The artifact carries commitment8 but only the low four canonical program-VK
    /// felts. A low4 prefix is not a faithful program identity.
    RetiredV2Low4Vk { name: String, commit_pi_lo: usize },
    /// The artifact carries no first-row pin of the `custom_proof_commitment`
    /// column (`PARAM_BASE + CUSTOM_PROOF_COMMIT_BASE`) — it is not a
    /// custom-exposure member at all; fail closed.
    MissingCommitPins {
        /// The presented descriptor's name.
        name: String,
    },
    /// The pins after the low commit block match NEITHER the retired v1 VK
    /// block NOR the live v3 commit-teeth + VK-teeth layout; fail closed.
    UnknownLayout {
        /// The presented descriptor's name.
        name: String,
        /// The exposure block's commitment PI base (slot of commit limb 0).
        commit_pi_lo: usize,
    },
}

impl core::fmt::Display for CustomCommitVersionError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::RetiredV1 { name, commit_pi_lo } => write!(
                f,
                "'{name}': RETIRED custom proof-bind commitment v1 (4 felts / ~62-bit birthday, \
                 exposure at PI {commit_pi_lo}..{}) — the live version is \
                 v{CUSTOM_COMMIT_VERSION}: {CUSTOM_COMMIT_WIDTH_V2} felts (~124-bit) with the \
                 second squeeze block on the commit-teeth columns; old custom artifacts are \
                 version-refused, never zero-padded or silently widened",
                commit_pi_lo + CUSTOM_COMMIT_WIDTH_RETIRED_V1
            ),
            Self::MissingCommitPins { name } => write!(
                f,
                "'{name}': no first-row `custom_proof_commitment` exposure pin (col \
                 PARAM_BASE+CUSTOM_PROOF_COMMIT_BASE) — not a custom-exposure member (fail closed)"
            ),
            Self::RetiredV2Low4Vk { name, commit_pi_lo } => write!(
                f,
                "'{name}': RETIRED custom carrier v2 exposes commitment8 but only program-VK low4 at PI {}..{}; the live v{CUSTOM_COMMIT_VERSION} carrier requires exact VK8 and refuses prefix-only identity",
                commit_pi_lo + CUSTOM_COMMIT_WIDTH_V2,
                commit_pi_lo + CUSTOM_COMMIT_WIDTH_V2 + 4
            ),
            Self::UnknownLayout { name, commit_pi_lo } => write!(
                f,
                "'{name}': the pins after the low commit block (PI {commit_pi_lo}..{}) match \
                 neither the retired v1 VK block nor the live v{CUSTOM_COMMIT_VERSION} \
                 commit-teeth layout (fail closed)",
                commit_pi_lo + CUSTOM_COMMIT_WIDTH_RETIRED_V1
            ),
        }
    }
}

impl std::error::Error for CustomCommitVersionError {}

/// **The structural custom-commitment version detector.**
///
/// ## ⚑ What the custom member ACTUALLY binds — read this before changing the gate
///
/// **Nothing, in-AIR.** Not the proof commitment, not the program VK. The `proof_bind` op is a
/// DECLARATION: the deployed `Ir2Air::eval` groups it with the bus kinds and `continue`s without
/// emitting a bus interaction, and Lean's `VmConstraint2.holdsAt` is `trivial` for it. Every column
/// of both octets is read by no gate, lookup, hash site or range tooth. `require_no_unbacked_proof_bind`
/// has always said so: *"The declaration is NOT an in-AIR check … the ONLY thing that makes the
/// published claim mean anything is the per-turn fold connecting it to a re-proven sub-proof leaf."*
///
/// So the binding lives entirely in the FOLD, over PUBLISHED PI SLOTS. That matters here because
/// **this function classifies a LAYOUT, not a binding.** It answers "which exposure shape did this
/// artifact commit to", so a retired one is refused at admission. It has never answered, and cannot
/// answer, "is the commitment forced".
///
/// ## ⚑ FLAG DAY 2026-07-31 — 14 of the 16 exposure pins are gone, and nothing got weaker
///
/// The convergence re-emit shipped `UnforcedPiPins.dropUnforcedPins` registry-wide. Of the sixteen
/// `.piBinding .first` exposure pins, **fourteen were deleted** — every one whose column no non-pin
/// constraint read, which was all of them except the two the `proof_bind` names. The deployed
/// `customVmDescriptor2R24` now carries exactly two: commit limb 0 (PI `lo` → `PARAM_BASE +
/// CUSTOM_PROOF_COMMIT_BASE`) and VK limb 0 (PI `lo + 8` → `PARAM_BASE + CUSTOM_VK_HASH_BASE`).
///
/// **No refusal was lost.** A pin on a column nothing else reads is `local[c] == pi[k]` with the
/// prover choosing both sides; `unforced_pin_row_admits_any_value` proves overwriting the column and
/// its slot with an arbitrary value preserves every constraint. And `piCount` is UNCHANGED by the
/// subtraction, so the fold still reads the same 16 slots and its check is exactly as strong. What
/// was deleted is a claim, not a check.
///
/// This detector used to classify by that decorative 16-pin shape and therefore returned
/// `UnknownLayout` on the live member. It now classifies by the evidence that SURVIVES.
///
/// ## The classification
///
/// `lo` is the PI slot of the first-row pin on commit limb 0, `vk_lo` that of VK limb 0. The gap
/// `vk_lo - lo` IS the declared commitment width in felts — that is what the retirement is about:
///
/// * `Err(RetiredV1)` — `vk_lo == lo + 4`: the VK block rides directly after a 4-felt commitment
///   (~62-bit birthday). Explicit version refusal, never widened or zero-padded.
/// * `vk_lo == lo + 8` — commitment8. The VK width then decides:
///   - a pin in `vk_lo + 4 .. vk_lo + 8` ⇒ the artifact carries the full pre-subtraction exposure
///     with VK teeth ⇒ `Ok(3)`;
///   - pins inside the window but NONE in `vk_lo + 4 ..` ⇒ commitment8 with VK low4 only ⇒
///     `Err(RetiredV2Low4Vk)`;
///   - NO pin in the window besides the two anchors ⇒ the SUBTRACTED form. Classified `Ok(3)` iff
///     the artifact reserves the full 16-slot exposure window (`piCount >= lo + 16`) and its
///     `proof_bind` names exactly the two anchored columns.
/// * `Err(MissingCommitPins)` / `Err(UnknownLayout)` — fail closed.
///
/// ⚠ **NAMED RESIDUAL, and it is a real loss of discrimination.** In the subtracted form the bytes
/// cannot separate v2 from v3: both would show two anchors 8 slots apart, and a v2's 12-slot window
/// plus a 4-slot rc tail reserves the same 16 PIs. This is not a hole today because **no emitter
/// produces a subtracted v2** — a v2 artifact predates the subtraction and therefore still carries
/// its pins, which the `RetiredV2Low4Vk` arm catches. If the exposure width ever becomes
/// configurable, this classifier must key on a DECLARED width, not on a reserved window.
pub fn custom_commit_version(
    d: &crate::descriptor_ir2::EffectVmDescriptor2,
) -> Result<u32, CustomCommitVersionError> {
    use crate::descriptor_ir2::{ProofBindSpec, VmConstraint2};
    use crate::effect_vm::columns::{PARAM_BASE, param};
    use crate::lean_descriptor_air::{LeanExpr, VmConstraint, VmRow};

    let commit_col0 = PARAM_BASE + param::CUSTOM_PROOF_COMMIT_BASE;
    let vk_col0 = PARAM_BASE + param::CUSTOM_VK_HASH_BASE;
    // ALL first-row pins keyed by PI slot, plus the two anchors.
    let mut first_pins: std::collections::BTreeMap<usize, usize> =
        std::collections::BTreeMap::new();
    let mut commit_pi_lo: Option<usize> = None;
    let mut vk_pi_lo: Option<usize> = None;
    for c in &d.constraints {
        if let VmConstraint2::Base(VmConstraint::PiBinding { row, col, pi_index }) = c
            && *row == VmRow::First
        {
            first_pins.insert(*pi_index, *col);
            if *col == commit_col0 {
                commit_pi_lo = Some(*pi_index);
            }
            if *col == vk_col0 {
                vk_pi_lo = Some(*pi_index);
            }
        }
    }
    let Some(lo) = commit_pi_lo else {
        return Err(CustomCommitVersionError::MissingCommitPins {
            name: d.name.clone(),
        });
    };
    let unknown = || CustomCommitVersionError::UnknownLayout {
        name: d.name.clone(),
        commit_pi_lo: lo,
    };
    let Some(vk_lo) = vk_pi_lo else {
        // No VK exposure anchor at all: we cannot read the declared widths. Fail closed.
        return Err(unknown());
    };

    // THE RETIRED v1: the VK block rides `CUSTOM_COMMIT_WIDTH_RETIRED_V1` slots after the
    // commitment, i.e. the artifact declares a 4-felt proof commitment.
    if vk_lo == lo + CUSTOM_COMMIT_WIDTH_RETIRED_V1 {
        return Err(CustomCommitVersionError::RetiredV1 {
            name: d.name.clone(),
            commit_pi_lo: lo,
        });
    }
    // Anything other than a full commitment8 window between the anchors is unclassifiable.
    if vk_lo != lo + CUSTOM_COMMIT_WIDTH_V2 {
        return Err(unknown());
    }

    let pin_in =
        |range: std::ops::Range<usize>| range.into_iter().any(|k| first_pins.contains_key(&k));
    let window = lo..lo + 2 * CUSTOM_COMMIT_WIDTH_V2;

    // (a) THE FULL (pre-subtraction) EXPOSURE: a pin in the VK-HI quarter is the v3 signature, and
    //     its absence beside other window pins is exactly the v2 prefix-only-VK shape.
    if pin_in(vk_lo + 4..vk_lo + CUSTOM_COMMIT_WIDTH_V2) {
        return Ok(CUSTOM_COMMIT_VERSION);
    }
    let extra_window_pins = window
        .clone()
        .filter(|k| *k != lo && *k != vk_lo)
        .any(|k| first_pins.contains_key(&k));
    if extra_window_pins {
        return Err(CustomCommitVersionError::RetiredV2Low4Vk {
            name: d.name.clone(),
            commit_pi_lo: lo,
        });
    }

    // (b) THE SUBTRACTED FORM: the two anchors and nothing else. The surviving evidence is the
    //     reserved 16-slot exposure window, plus the `proof_bind` declaring exactly the two
    //     anchored columns — the tie between the exposure and the op the fold keys on. Both are
    //     required; neither is implied by the other.
    if d.public_input_count < lo + 2 * CUSTOM_COMMIT_WIDTH_V2 {
        return Err(unknown());
    }
    // ⚑ Since the 2026-08-05 widening the op names LANE VECTORS, so the classifier reads lane 0 of
    // each — the anchor the exposure window is keyed on — and additionally requires the seam to be
    // at the eight-lane width the deployed commitment actually has. A four-lane artifact fails here
    // as well as at the loader.
    let declares_the_anchors = d.constraints.iter().any(|c| match c {
        VmConstraint2::ProofBind(ProofBindSpec { commit, vk, .. }) => {
            commit.len() >= crate::descriptor_ir2::PROOF_BIND_MIN_LANES
                && vk.len() == commit.len()
                && matches!(commit.first(), Some(LeanExpr::Var(cc)) if *cc == commit_col0)
                && matches!(vk.first(), Some(LeanExpr::Var(vv)) if *vv == vk_col0)
        }
        _ => false,
    });
    if !declares_the_anchors {
        return Err(unknown());
    }
    Ok(CUSTOM_COMMIT_VERSION)
}

/// Require the LIVE (v2, 8-felt) custom proof-bind commitment layout; refuse the
/// retired 4-felt v1 (and anything unclassifiable) with a typed error. The custom
/// fold arm and the custom-wide leg mint call this at admission — old 4-felt
/// custom artifacts never enter the upgraded assurance rung.
pub fn require_custom_carrier_vk8(
    d: &crate::descriptor_ir2::EffectVmDescriptor2,
) -> Result<(), CustomCommitVersionError> {
    custom_commit_version(d).map(|_| ())
}

/// The typed refusal [`require_no_unbacked_proof_bind`] raises: a descriptor that DECLARES a
/// recursive proof-binding was about to be folded as a plain segment leaf, with nothing to back
/// the claim it publishes.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UnbackedProofBindError {
    /// The presented descriptor's name.
    pub name: String,
    /// How many `ProofBind` ops it declares (the custom member declares exactly one).
    pub declarations: usize,
}

impl core::fmt::Display for UnbackedProofBindError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let Self { name, declarations } = self;
        write!(
            f,
            "'{name}': declares {declarations} recursive proof-binding op(s) \
             (`DescriptorIR2.ProofBind`) but the leg carries NO carrier witness — a proof-bind \
             member has no re-exec rung. The declaration is NOT an in-AIR check (the deployed \
             evaluator has no `ProofBind` arm, and the two surviving `pi_binding` pins only \
             PUBLISH the binding columns — the other fourteen were deleted in 2026-07-31's \
             unforced-pin subtraction for pinning columns nothing reads); the ONLY thing that \
             makes the published claim mean anything is \
             the per-turn fold connecting it to a re-proven sub-proof leaf. Folding this leg as \
             a plain segment leaf would carry a prover-chosen commitment no sub-proof backs, and \
             a light client could not tell which arm was taken — refused fail-closed. Attach the \
             leg's `CarrierWitness` (`Custom` / `CustomIr2`) so the fold binds the claim."
        )
    }
}

impl std::error::Error for UnbackedProofBindError {}

/// Require that a descriptor about to be folded WITHOUT a carrier witness — as the PLAIN SEGMENT
/// LEAF, the fold's no-carrier arm — declares no `DescriptorIR2.ProofBind` op.
///
/// The exact twin of [`require_custom_carrier_vk8`] on the other polarity. That one guards the
/// carrier arm (a leg that HAS a custom witness must publish the live commitment8+VK8 exposure);
/// this one guards the ARM SELECTION itself (a leg whose descriptor declares a proof-binding must
/// not reach the plain arm at all). Both are keyed structurally on the leg's own committed
/// descriptor, never on a caller-passed flag — the whole failure mode is a prover picking the
/// unbound arm for a descriptor whose identity demands the bound one.
///
/// **Why `ProofBind` IS the custom-member identity here** (measured, not assumed): across all
/// three deployed staged registries — `V3_STAGED_REGISTRY_TSV` (60 members),
/// [`WIDE_REGISTRY_STAGED_TSV`] (57) and the DERIVED welded set ([`welded_wide_members`], 57) — EXACTLY
/// one member carries a `proof_bind` op, and in every one of them it is
/// `customVmDescriptor2R24`. Keying on the op rather than on the name means a member-name
/// suffix flag-day (`…-gentian-deployed-bare-refuse`, `…-umem-wide-welded-staged`) cannot slip a
/// custom leg past the guard, and a FUTURE proof-bind-declaring member is covered the day it is
/// emitted rather than the day someone remembers to extend a name list.
/// (`registry_proof_bind_declarations_are_exactly_the_custom_member` pins the measurement.)
pub fn require_no_unbacked_proof_bind(
    d: &crate::descriptor_ir2::EffectVmDescriptor2,
) -> Result<(), UnbackedProofBindError> {
    let declarations = proof_bind_declarations(d);
    if declarations == 0 {
        return Ok(());
    }
    Err(UnbackedProofBindError {
        name: d.name.clone(),
        declarations,
    })
}

/// How many `DescriptorIR2.ProofBind` ops a descriptor declares — the structural custom-member
/// detector [`require_no_unbacked_proof_bind`] keys on.
pub fn proof_bind_declarations(d: &crate::descriptor_ir2::EffectVmDescriptor2) -> usize {
    d.constraints
        .iter()
        .filter(|c| matches!(c, crate::descriptor_ir2::VmConstraint2::ProofBind(_)))
        .count()
}

/// The rotated probe layout at register count `r` (the Rust twin of the Lean parametric
/// layout `EffectVmEmitRotationR`: columns are FUNCTIONS of R; the chunking is 4-wide head,
/// 3-wide chip groups while ≥ 3 remain, singletons after — arity ∈ {2,4}, NEVER 3 — and the
/// iroot rides its own arity-2 final site, literally last).
pub fn rotation_layout_for(r: usize) -> RotationLayoutR {
    let m = r + 3; // post-head pre-iroot fresh inputs
    let num_sites = 1 + m / 3 + m % 3 + 1; // head + 3-groups + singletons + the iroot site
    RotationLayoutR {
        num_registers: r,
        committed_height: r + 6,
        iroot: r + 7,
        state_commit: r + 8,
        block_size: r + 9,
        chain_base: r + 9,
        num_chain: num_sites - 1,
        probe_width: r + 9 + num_sites - 1,
    }
}

/// See [`rotation_layout_for`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RotationLayoutR {
    pub num_registers: usize,
    pub committed_height: usize,
    pub iroot: usize,
    pub state_commit: usize,
    pub block_size: usize,
    pub chain_base: usize,
    pub num_chain: usize,
    pub probe_width: usize,
}

// ==== ALL unique descriptors (name -> json, fingerprint): the total name registry ====
pub const ALL_DESCRIPTORS: &[(&str, &str, &str)] = &[
    (
        "dregg-effectvm-attenuateA-v1",
        DREGG_EFFECTVM_ATTENUATEA_V1_JSON,
        DREGG_EFFECTVM_ATTENUATEA_V1_FP,
    ),
    (
        "dregg-effectvm-bridgemint-v1",
        DREGG_EFFECTVM_BRIDGEMINT_V1_JSON,
        DREGG_EFFECTVM_BRIDGEMINT_V1_FP,
    ),
    (
        "dregg-effectvm-burn-v1",
        DREGG_EFFECTVM_BURN_V1_JSON,
        DREGG_EFFECTVM_BURN_V1_FP,
    ),
    (
        "dregg-effectvm-celldestroy-v2",
        DREGG_EFFECTVM_CELLDESTROY_V2_JSON,
        DREGG_EFFECTVM_CELLDESTROY_V2_FP,
    ),
    (
        "dregg-effectvm-cellseal-v2",
        DREGG_EFFECTVM_CELLSEAL_V2_JSON,
        DREGG_EFFECTVM_CELLSEAL_V2_FP,
    ),
    (
        "dregg-effectvm-cellunseal-v2",
        DREGG_EFFECTVM_CELLUNSEAL_V2_JSON,
        DREGG_EFFECTVM_CELLUNSEAL_V2_FP,
    ),
    (
        "dregg-effectvm-createcell-v2",
        DREGG_EFFECTVM_CREATECELL_V2_JSON,
        DREGG_EFFECTVM_CREATECELL_V2_FP,
    ),
    (
        "dregg-effectvm-createcellfromfactory-v2",
        DREGG_EFFECTVM_CREATECELLFROMFACTORY_V2_JSON,
        DREGG_EFFECTVM_CREATECELLFROMFACTORY_V2_FP,
    ),
    (
        "dregg-effectvm-emitEvent-v1",
        DREGG_EFFECTVM_EMITEVENT_V1_JSON,
        DREGG_EFFECTVM_EMITEVENT_V1_FP,
    ),
    (
        "dregg-effectvm-exerciseA-holdlayer-v2",
        DREGG_EFFECTVM_EXERCISEA_HOLDLAYER_V2_JSON,
        DREGG_EFFECTVM_EXERCISEA_HOLDLAYER_V2_FP,
    ),
    (
        "dregg-effectvm-incrementNonce-v2",
        DREGG_EFFECTVM_INCREMENTNONCE_V2_JSON,
        DREGG_EFFECTVM_INCREMENTNONCE_V2_FP,
    ),
    (
        "dregg-effectvm-makesovereign-v2",
        DREGG_EFFECTVM_MAKESOVEREIGN_V2_JSON,
        DREGG_EFFECTVM_MAKESOVEREIGN_V2_FP,
    ),
    (
        "dregg-effectvm-mint-v1",
        DREGG_EFFECTVM_MINT_V1_JSON,
        DREGG_EFFECTVM_MINT_V1_FP,
    ),
    (
        "dregg-effectvm-notecreate-v1",
        DREGG_EFFECTVM_NOTECREATE_V1_JSON,
        DREGG_EFFECTVM_NOTECREATE_V1_FP,
    ),
    (
        "dregg-effectvm-notespend-v1",
        DREGG_EFFECTVM_NOTESPEND_V1_JSON,
        DREGG_EFFECTVM_NOTESPEND_V1_FP,
    ),
    (
        "dregg-effectvm-pipelinedSendA-v2",
        DREGG_EFFECTVM_PIPELINEDSENDA_V2_JSON,
        DREGG_EFFECTVM_PIPELINEDSENDA_V2_FP,
    ),
    (
        "dregg-effectvm-introduce-v2",
        DREGG_EFFECTVM_INTRODUCE_V2_JSON,
        DREGG_EFFECTVM_INTRODUCE_V2_FP,
    ),
    (
        "dregg-effectvm-receiptArchiveA-v2",
        DREGG_EFFECTVM_RECEIPTARCHIVEA_V2_JSON,
        DREGG_EFFECTVM_RECEIPTARCHIVEA_V2_FP,
    ),
    (
        "dregg-effectvm-refreshDelegation-v2",
        DREGG_EFFECTVM_REFRESHDELEGATION_V2_JSON,
        DREGG_EFFECTVM_REFRESHDELEGATION_V2_FP,
    ),
    (
        "dregg-effectvm-refusal-v2",
        DREGG_EFFECTVM_REFUSAL_V2_JSON,
        DREGG_EFFECTVM_REFUSAL_V2_FP,
    ),
    (
        "dregg-effectvm-revokecapability-v1",
        DREGG_EFFECTVM_REVOKECAPABILITY_V1_JSON,
        DREGG_EFFECTVM_REVOKECAPABILITY_V1_FP,
    ),
    (
        "dregg-effectvm-revokeDelegation-v2",
        DREGG_EFFECTVM_REVOKEDELEGATION_V2_JSON,
        DREGG_EFFECTVM_REVOKEDELEGATION_V2_FP,
    ),
    (
        "dregg-effectvm-setPermissionsA-v2",
        DREGG_EFFECTVM_SETPERMISSIONSA_V2_JSON,
        DREGG_EFFECTVM_SETPERMISSIONSA_V2_FP,
    ),
    (
        "dregg-effectvm-setVK-v2",
        DREGG_EFFECTVM_SETVK_V2_JSON,
        DREGG_EFFECTVM_SETVK_V2_FP,
    ),
    (
        "dregg-effectvm-spawnA-v3-actorrow",
        DREGG_EFFECTVM_SPAWNA_V3_ACTORROW_JSON,
        DREGG_EFFECTVM_SPAWNA_V3_ACTORROW_FP,
    ),
    (
        "dregg-effectvm-transfer-v1",
        DREGG_EFFECTVM_TRANSFER_V1_JSON,
        DREGG_EFFECTVM_TRANSFER_V1_FP,
    ),
    (
        "dregg-effectvm-record-v1",
        DREGG_EFFECTVM_RECORD_V1_JSON,
        DREGG_EFFECTVM_RECORD_V1_FP,
    ),
];

/// Look up the EffectVM descriptor JSON bound to a running-prover **selector index**
/// (`effect_vm::columns::sel`). Returns the byte-exact Lean-emitted wire JSON, or
/// `None` if no verified descriptor is registered for that selector yet.
pub fn descriptor_for_selector(sel: usize) -> Option<&'static str> {
    SELECTOR_DESCRIPTORS
        .iter()
        .find(|(s, _, _, _)| *s == sel)
        .map(|(_, _, json, _)| *json)
}

/// The descriptor `name` (canonical wire identity) bound to a selector index.
pub fn descriptor_name_for_selector(sel: usize) -> Option<&'static str> {
    SELECTOR_DESCRIPTORS
        .iter()
        .find(|(s, _, _, _)| *s == sel)
        .map(|(_, name, _, _)| *name)
}

/// Look up a descriptor JSON by its canonical `name` (e.g. `"dregg-effectvm-burn-v1"`).
/// This is the TOTAL registry: every unique emitted descriptor, including the
/// name-only ones with no dedicated selector. Returns the byte-exact wire JSON.
pub fn descriptor_for_name(name: &str) -> Option<&'static str> {
    ALL_DESCRIPTORS
        .iter()
        .find(|(n, _, _)| *n == name)
        .map(|(_, json, _)| *json)
}

/// The committed SHA-256 fingerprint of the descriptor JSON for `name`.
pub fn fingerprint_for_name(name: &str) -> Option<&'static str> {
    ALL_DESCRIPTORS
        .iter()
        .find(|(n, _, _)| *n == name)
        .map(|(_, _, fp)| *fp)
}

/// Look up an IR-v2 descriptor JSON by its Lean def-name key (e.g. `"transferVmDescriptor2"`,
/// `"setFieldVmDescriptor2-3"`). The byte-exact `emitVmJson2` wire (`"ir":2`), interpreted by
/// `descriptor_ir2::parse_vm_descriptor2`. ADDITIVE: the v1 path (`descriptor_for_selector` /
/// `descriptor_for_name`) stays the live one until the cutover lane flips the pointer.
pub fn descriptor2_for_key(key: &str) -> Option<&'static str> {
    V2_DESCRIPTORS
        .iter()
        .find(|(k, _, _)| *k == key)
        .map(|(_, json, _)| *json)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::descriptor_ir2::parse_vm_descriptor2;
    use crate::lean_descriptor_air::parse_vm_descriptor;

    /// Self-contained SHA-256 (FIPS 180-4), no external dep, so the drift
    /// fingerprints are reproducible from this file alone. Returns the lowercase
    /// hex digest of `data`.
    fn sha256_hex(data: &[u8]) -> String {
        const K: [u32; 64] = [
            0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4,
            0xab1c5ed5, 0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe,
            0x9bdc06a7, 0xc19bf174, 0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f,
            0x4a7484aa, 0x5cb0a9dc, 0x76f988da, 0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
            0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967, 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc,
            0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85, 0xa2bfe8a1, 0xa81a664b,
            0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070, 0x19a4c116,
            0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
            0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7,
            0xc67178f2,
        ];
        let mut h: [u32; 8] = [
            0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab,
            0x5be0cd19,
        ];
        let mut msg = data.to_vec();
        let bitlen = (data.len() as u64) * 8;
        msg.push(0x80);
        while msg.len() % 64 != 56 {
            msg.push(0);
        }
        msg.extend_from_slice(&bitlen.to_be_bytes());

        for chunk in msg.chunks(64) {
            let mut w = [0u32; 64];
            for i in 0..16 {
                w[i] = u32::from_be_bytes([
                    chunk[4 * i],
                    chunk[4 * i + 1],
                    chunk[4 * i + 2],
                    chunk[4 * i + 3],
                ]);
            }
            for i in 16..64 {
                let s0 = w[i - 15].rotate_right(7) ^ w[i - 15].rotate_right(18) ^ (w[i - 15] >> 3);
                let s1 = w[i - 2].rotate_right(17) ^ w[i - 2].rotate_right(19) ^ (w[i - 2] >> 10);
                w[i] = w[i - 16]
                    .wrapping_add(s0)
                    .wrapping_add(w[i - 7])
                    .wrapping_add(s1);
            }
            let (mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut hh) =
                (h[0], h[1], h[2], h[3], h[4], h[5], h[6], h[7]);
            for i in 0..64 {
                let s1 = e.rotate_right(6) ^ e.rotate_right(11) ^ e.rotate_right(25);
                let ch = (e & f) ^ ((!e) & g);
                let t1 = hh
                    .wrapping_add(s1)
                    .wrapping_add(ch)
                    .wrapping_add(K[i])
                    .wrapping_add(w[i]);
                let s0 = a.rotate_right(2) ^ a.rotate_right(13) ^ a.rotate_right(22);
                let maj = (a & b) ^ (a & c) ^ (b & c);
                let t2 = s0.wrapping_add(maj);
                hh = g;
                g = f;
                f = e;
                e = d.wrapping_add(t1);
                d = c;
                c = b;
                b = a;
                a = t1.wrapping_add(t2);
            }
            h[0] = h[0].wrapping_add(a);
            h[1] = h[1].wrapping_add(b);
            h[2] = h[2].wrapping_add(c);
            h[3] = h[3].wrapping_add(d);
            h[4] = h[4].wrapping_add(e);
            h[5] = h[5].wrapping_add(f);
            h[6] = h[6].wrapping_add(g);
            h[7] = h[7].wrapping_add(hh);
        }
        let mut out = String::with_capacity(64);
        for word in h {
            for byte in word.to_be_bytes() {
                out.push_str(&format!("{byte:02x}"));
            }
        }
        out
    }

    /// Sanity: the SHA-256 impl matches the FIPS test vector for "abc".
    #[test]
    fn sha256_self_test() {
        assert_eq!(
            sha256_hex(b"abc"),
            "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
        );
        assert_eq!(
            sha256_hex(b""),
            "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
        );
    }

    /// RIG (descriptor-pins, 2026-07-16) — every registered descriptor's committed
    /// `*_FP` constant equals the SHA-256 of its own `*_JSON` bytes.
    ///
    /// The module doc (lines 21-26) frames this as "self-consistency, not Lean
    /// agreement" and points at the generate-fresh `scripts/check-descriptor-drift.sh`
    /// as the real Lean↔JSON gate — that gate is CI-only and Lean-toolchain-dependent.
    /// This test rigs the WEAKER-but-real property the FP pins actually assert: the
    /// JSON and its committed fingerprint have not drifted APART. That is NOT a
    /// tautology (`X == X`) — the JSON file and the FP hex string are two independently
    /// editable artifacts, and `all_descriptors_parse` above only checks parseability,
    /// which a byte-changing-but-still-parseable hand-edit / bad merge / partial
    /// checkout survives silently. This is the identical `sha256_hex(x) == X_FP` check
    /// already wired 1300 lines below for the derived welded set and
    /// `V3_SETFIELD_VALUE8_STAGED_REGISTRY_TSV`, applied to the descriptors themselves.
    /// It does NOT prove Lean-agreement — only that nothing edited a descriptor JSON
    /// (or its FP) without re-running the emit script that repins both together.
    #[test]
    fn every_descriptor_fp_matches_its_json_bytes() {
        let mut n = 0usize;
        for (name, json, fp) in ALL_DESCRIPTORS {
            assert_eq!(
                sha256_hex(json.as_bytes()).as_str(),
                *fp,
                "descriptor {name}: sha256(JSON) != committed *_FP pin — the JSON and its \
                 fingerprint have DRIFTED APART (hand-edit / bad merge / stale FP)"
            );
            n += 1;
        }
        for (sel, name, json, fp) in SELECTOR_DESCRIPTORS {
            assert_eq!(
                sha256_hex(json.as_bytes()).as_str(),
                *fp,
                "selector {sel} ({name}): sha256(JSON) != committed *_FP pin"
            );
        }
        for (name, json, fp) in NAME_ONLY_DESCRIPTORS {
            assert_eq!(
                sha256_hex(json.as_bytes()).as_str(),
                *fp,
                "name-only descriptor {name}: sha256(JSON) != committed *_FP pin"
            );
        }
        for (key, json, fp) in V2_DESCRIPTORS {
            assert_eq!(
                sha256_hex(json.as_bytes()).as_str(),
                *fp,
                "v2 descriptor {key}: sha256(JSON) != committed *_FP pin"
            );
        }
        // A truncated/emptied registry must not let this pass vacuously.
        assert_eq!(
            n, 27,
            "ALL_DESCRIPTORS length changed ({n} != 27); re-audit the FP-pin gate"
        );
    }

    /// RIG (descriptor-pins, 2026-07-16) — every `descriptor_sha256` and
    /// `by_name_sha256` pin in `circuit/descriptors/PROVENANCE.json` equals the
    /// SHA-256 of the actual checked-in file it names.
    ///
    /// PROVENANCE.json's whole job is to let an operator or federation member
    /// independently confirm "these are the descriptor bytes this build runs." Yet NO
    /// Rust source references it and NO CI job checks it: the only checker is
    /// `verify_provenance()` in `scripts/emit_descriptors.py`, run by hand pre-ceremony
    /// (per VK-CEREMONY.md / VK-REGEN-CONTROLS.md). A hand-edit or bad merge that drifts
    /// a checked-in descriptor from its pin is invisible to `cargo test` today. This
    /// test bites that gap in pure Rust using the same FIPS-vector-tested `sha256_hex`.
    ///
    /// `fp_file_sha256` is deliberately NOT checked here: it pins SOURCE files (this
    /// file among them) that change on every legitimate edit, so it is a provenance
    /// snapshot, not a stable invariant — rigging it would make the test red on every
    /// source change. Named, not rigged.
    ///
    /// The anti-vacuity leg is a DERIVED COVERAGE invariant, not a pinned count. Until
    /// 2026-07-24 it read `assert_eq!((d, b), (75, 27))`, which rots on every legitimate
    /// descriptor addition (it had been stale-red at b = 55) and, worse, is satisfied by
    /// a map of the RIGHT SIZE covering the WRONG files. The replacement asserts the two
    /// maps cover EXACTLY the checked-in descriptor set — see below — which cannot go
    /// stale, still fails on a truncated map (a dropped pin leaves a checked-in
    /// descriptor uncovered), and additionally bites the hole a count is blind to: a lane
    /// lands a descriptor and never re-stamps PROVENANCE.
    #[test]
    fn provenance_json_pins_match_checked_in_descriptor_bytes() {
        use std::collections::BTreeSet;
        use std::path::Path;
        let descdir = Path::new(env!("CARGO_MANIFEST_DIR")).join("descriptors");
        let root = Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .expect("crate dir has a parent (the repo root)");
        let prov_bytes =
            std::fs::read(descdir.join("PROVENANCE.json")).expect("PROVENANCE.json must exist");
        let prov: serde_json::Value =
            serde_json::from_slice(&prov_bytes).expect("PROVENANCE.json must parse");

        // Per-file leg (UNCHANGED): every pin equals sha256 of the file it names.
        // Returns the pinned key set so the coverage leg below can compare against it.
        let check_map = |map_key: &str, subdir: Option<&str>| -> BTreeSet<String> {
            let map = prov[map_key]
                .as_object()
                .unwrap_or_else(|| panic!("PROVENANCE.json missing object `{map_key}`"));
            let mut keys = BTreeSet::new();
            for (fname, pin) in map {
                let pin = pin
                    .as_str()
                    .unwrap_or_else(|| panic!("{map_key}[{fname}] pin is not a string"));
                let path = match subdir {
                    Some(s) => descdir.join(s).join(fname),
                    None => descdir.join(fname),
                };
                let bytes = std::fs::read(&path).unwrap_or_else(|_| {
                    panic!(
                        "PROVENANCE {map_key} pins `{fname}` but {} is missing on disk",
                        path.display()
                    )
                });
                assert_eq!(
                    sha256_hex(&bytes).as_str(),
                    pin,
                    "PROVENANCE {map_key} pin for `{fname}` != sha256 of the file on disk (DRIFT)"
                );
                keys.insert(fname.clone());
            }
            keys
        };

        let pinned_top = check_map("descriptor_sha256", None);
        let pinned_by_name = check_map("by_name_sha256", Some("by-name"));

        // ---- Coverage leg: the set the stamp must cover, DERIVED ----
        //
        // Ground truth for "what belongs in the stamp" is `verify_provenance()` in
        // `scripts/emit_descriptors.py`: `descriptor_sha256` covers every file sitting
        // DIRECTLY in `circuit/descriptors/` (the `.tsv` staged registries included, since
        // the prover reads those bytes too) except PROVENANCE.json itself and the declared
        // `COVERAGE_EXEMPT` entries; `by_name_sha256` covers every file in
        // `circuit/descriptors/by-name/`. This test mirrors those two sets.
        //
        // TRACKED (`git ls-files`), not everything-on-disk — CHOSEN, not defaulted. This
        // tree is worked by ~10 concurrent lanes, so `circuit/descriptors/` routinely holds
        // another lane's untracked scratch emissions (at the time of writing:
        // `by-name/automatafl-legc-n*.json`). An untracked file is not yet a CLAIM about
        // what this build runs, and reddening the shared suite for one would block every
        // lane over a file that is not in the repo. A file in the INDEX is a claim — its
        // author said "this ships", and in this shared tree a co-tenant `commit -a` can
        // promote it to HEAD without them — so a tracked-but-unstamped descriptor is a real
        // provenance hole and SHOULD red. (`emit_descriptors.py` reads the whole directory
        // instead because it runs pre-ceremony on a clean tree, where the two sets
        // coincide.) If git is unavailable — a vendored source export, or the rsync'd
        // remote build lane `scripts/pbuild` creates (it excludes `.git/`) — we fall back
        // to the on-disk listing, which is STRICTER (untracked files count), never weaker.
        // The failure message names which set it compared against so a red in a `.git`-less
        // tree is not mistaken for a red in the repo.
        let tracked: Option<Vec<String>> = std::process::Command::new("git")
            .arg("-C")
            .arg(&descdir)
            .args(["ls-files", "-z"])
            .output()
            .ok()
            .filter(|o| o.status.success())
            .map(|o| {
                String::from_utf8_lossy(&o.stdout)
                    .split('\0')
                    .filter(|s| !s.is_empty())
                    .map(str::to_string)
                    .collect()
            });
        let dir_files = |dir: &Path| -> BTreeSet<String> {
            std::fs::read_dir(dir)
                .unwrap_or_else(|e| panic!("cannot list {}: {e}", dir.display()))
                .filter_map(Result::ok)
                .filter(|e| e.path().is_file())
                .map(|e| e.file_name().to_string_lossy().into_owned())
                .collect()
        };
        let (present_top, present_by_name): (BTreeSet<String>, BTreeSet<String>) = match &tracked {
            Some(rels) => (
                rels.iter().filter(|r| !r.contains('/')).cloned().collect(),
                rels.iter()
                    .filter_map(|r| r.strip_prefix("by-name/"))
                    .filter(|r| !r.contains('/'))
                    .map(str::to_string)
                    .collect(),
            ),
            None => (dir_files(&descdir), dir_files(&descdir.join("by-name"))),
        };

        // ⚑ EVERY OTHER DESCRIPTOR SUBDIRECTORY, BY DISCOVERY — the same repair the ceremony
        // checker took on 2026-08-01, applied to the mirror that had NOT taken it.
        //
        // This test named `descriptor_sha256` and `by_name_sha256` and nothing else, so
        // `circuit/descriptors/table-airs/` — the ELEVEN shared table AIRs, among them the
        // Poseidon2 chip every descriptor's hash sites lower into and the map-ops/map-absent
        // double-spend gate — was outside the only provenance check in this repo that ACTUALLY
        // RUNS. `emit_descriptors.py --verify-provenance` covers them and was invoked by nothing
        // (13 references, all prose); this test executes on every `cargo test -p dregg-circuit`
        // and could not see them. Between the two, ten of ten tracked table AIRs were wrong in
        // HEAD — eight mismatched pins, two with no row at all — with nothing red anywhere.
        //
        // A hand-named leg list cannot go red when a leg is missing from it; it just covers less.
        // So the set is DISCOVERED from the same listing the coverage leg above already derives,
        // and a subdirectory landing tomorrow is mirrored the day it appears. `check_map` panics
        // on an absent `<sub>_sha256` object, so a NEW subdirectory with no stamp leg is loud.
        let mut present_subdirs: std::collections::BTreeMap<String, BTreeSet<String>> =
            Default::default();
        match &tracked {
            Some(rels) => {
                for r in rels {
                    if let Some((dir, base)) = r.split_once('/') {
                        if dir != "by-name" && !base.contains('/') {
                            present_subdirs
                                .entry(dir.to_string())
                                .or_default()
                                .insert(base.to_string());
                        }
                    }
                }
            }
            None => {
                for e in std::fs::read_dir(&descdir).expect("descriptors dir is listable") {
                    let p = e.expect("dir entry").path();
                    let name = p
                        .file_name()
                        .unwrap_or_default()
                        .to_string_lossy()
                        .into_owned();
                    if p.is_dir() && name != "by-name" {
                        present_subdirs.insert(name, dir_files(&p));
                    }
                }
            }
        }
        let source = match &tracked {
            Some(_) => "tracked by git",
            None => "present on disk (NO git index here — untracked files count too)",
        };

        // The exemption set is READ OUT of the ceremony checker rather than copied, so
        // there is exactly ONE authority for "this artifact is not owned by the stamp" and
        // no second hand-maintained list to rot (each entry is required, there, to carry a
        // co-located regen/check). A reformat that breaks this parse panics loudly rather
        // than silently widening what the test accepts.
        let script_path = root.join("scripts").join("emit_descriptors.py");
        let script = std::fs::read_to_string(&script_path).unwrap_or_else(|e| {
            panic!(
                "{} must be readable (it defines COVERAGE_EXEMPT): {e}",
                script_path.display()
            )
        });
        let exempt: BTreeSet<String> = {
            let marker = "COVERAGE_EXEMPT = frozenset({";
            let start = script.find(marker).unwrap_or_else(|| {
                panic!(
                    "emit_descriptors.py: `{marker}` not found — the stamp's exemption set \
                     moved; re-point this mirror (do NOT hand-copy the list)"
                )
            });
            let body = &script[start + marker.len()..];
            let end = body
                .find("})")
                .expect("emit_descriptors.py: COVERAGE_EXEMPT literal is unterminated");
            body[..end]
                .split('"')
                .skip(1)
                .step_by(2)
                .map(str::to_string)
                .collect()
        };

        let want_top: BTreeSet<String> = present_top
            .iter()
            .filter(|n| n.as_str() != "PROVENANCE.json" && !exempt.contains(n.as_str()))
            .cloned()
            .collect();
        let want_by_name = present_by_name;

        let compare = |map_key: &str, pinned: &BTreeSet<String>, want: &BTreeSet<String>| {
            // The derivation itself must not come back empty — that (a broken glob, a moved
            // directory) is the only way this leg could go vacuous, and it is the exact
            // failure mode the old hand-pinned count was there to prevent.
            assert!(
                !want.is_empty(),
                "PROVENANCE {map_key}: the checked-in descriptor set derived EMPTY — this \
                 test would be vacuous; the derivation is broken, not the stamp"
            );
            let unstamped: Vec<&str> = want.difference(pinned).map(String::as_str).collect();
            assert!(
                unstamped.is_empty(),
                "PROVENANCE {map_key} does NOT cover descriptor(s) {unstamped:?} ({source}) — \
                 they landed without re-stamping, so nothing attests their bytes. Fix at the \
                 SOURCE: re-run the emit/stamp ceremony (`scripts/emit_descriptors.py`, see \
                 docs/VK-REGEN-CONTROLS.md); do NOT hand-add rows."
            );
            let ghosts: Vec<&str> = pinned.difference(want).map(String::as_str).collect();
            assert!(
                ghosts.is_empty(),
                "PROVENANCE {map_key} pins {ghosts:?}, which are not part of the descriptor set \
                 ({source}) — deleted, renamed, or newly exempted without re-stamping"
            );
        };
        compare("descriptor_sha256", &pinned_top, &want_top);
        compare("by_name_sha256", &pinned_by_name, &want_by_name);

        // ⚠ THE DISCOVERY ITSELF NEEDS A FLOOR, from an INDEPENDENT source. Everything above is
        // driven by `present_subdirs`, so a discovery that silently comes back short does not go
        // red — it just covers less, which is precisely the failure this leg was added to end.
        // The stamp's own leg KEYS are that second source: they are written by the ceremony
        // (`build_provenance`'s `subdir_hash_legs`) and read here from the file, sharing no input
        // with a `git ls-files` of the directory. The two must name the same subdirectories.
        // (A constant compared against its own definition is decoration; two sources are a gate.)
        let stamped_subdirs: BTreeSet<String> = prov
            .as_object()
            .expect("PROVENANCE.json is an object")
            .keys()
            .filter_map(|k| k.strip_suffix("_sha256"))
            .filter(|k| !matches!(*k, "descriptor" | "by_name" | "fp_file"))
            .map(str::to_string)
            .collect();
        let discovered: BTreeSet<String> = present_subdirs.keys().cloned().collect();
        assert_eq!(
            discovered, stamped_subdirs,
            "PROVENANCE.json's descriptor SUBDIRECTORY legs and the checked-in subdirectories \
             ({source}) name different sets. Either a subdirectory of circuit/descriptors/ has \
             no `<name>_sha256` leg (its artifacts are unattested — re-run the stamp ceremony, \
             see docs/VK-REGEN-CONTROLS.md) or the stamp pins a subdirectory that is gone."
        );

        for (dir, want) in &present_subdirs {
            let key = format!("{dir}_sha256");
            let pinned = check_map(&key, Some(dir));
            compare(&key, &pinned, want);
        }
    }

    /// Every registered descriptor re-parses via `parse_vm_descriptor` into the
    /// structure the prover consumes, with the parsed `name` matching the registry
    /// key and a positive trace width. (The Lean↔JSON drift gate is generate-fresh
    /// `scripts/check-descriptor-drift.sh`, not a self-consistent FP rehash.)
    #[test]
    fn all_descriptors_parse() {
        assert_eq!(ALL_DESCRIPTORS.len(), 27, "expected 27 unique descriptors");
        for (name, json, _fp) in ALL_DESCRIPTORS {
            let desc = parse_vm_descriptor(json)
                .unwrap_or_else(|e| panic!("descriptor {name} failed to parse: {e}"));
            assert_eq!(
                &desc.name, name,
                "descriptor {name}: parsed name {:?} != registry key",
                desc.name
            );
            assert!(desc.trace_width > 0, "descriptor {name}: zero trace_width");
        }
    }

    /// The selector table is consistent with the name registry: each selector's
    /// JSON is identical to the `ALL_DESCRIPTORS` entry of the same name, and every
    /// selector descriptor parses.
    #[test]
    fn selector_table_consistent() {
        for (sel, name, json, _fp) in SELECTOR_DESCRIPTORS {
            let by_name = descriptor_for_name(name)
                .unwrap_or_else(|| panic!("selector {sel} name {name} not in ALL_DESCRIPTORS"));
            assert_eq!(
                *json, by_name,
                "selector {sel}: JSON differs from name registry"
            );
            assert_eq!(descriptor_for_selector(*sel), Some(*json));
            assert_eq!(descriptor_name_for_selector(*sel), Some(*name));
            parse_vm_descriptor(json)
                .unwrap_or_else(|e| panic!("selector {sel} descriptor failed to parse: {e}"));
        }
        // No selector index is registered twice.
        let mut sels: Vec<usize> = SELECTOR_DESCRIPTORS.iter().map(|(s, _, _, _)| *s).collect();
        sels.sort_unstable();
        let n = sels.len();
        sels.dedup();
        assert_eq!(sels.len(), n, "duplicate selector index in registry");
        // The transfer selector (1) resolves to the transfer descriptor.
        assert_eq!(
            descriptor_name_for_selector(crate::effect_vm::columns::sel::TRANSFER),
            Some("dregg-effectvm-transfer-v1")
        );
        // An unregistered selector (NOOP) yields None.
        assert_eq!(
            descriptor_for_selector(crate::effect_vm::columns::sel::NOOP),
            None
        );
    }

    /// The name-only descriptors are real, distinct, and present in the total
    /// registry (they just lack a dedicated Rust selector slot).
    #[test]
    fn name_only_descriptors_present() {
        assert_eq!(NAME_ONLY_DESCRIPTORS.len(), 1);
        for (name, json, _fp) in NAME_ONLY_DESCRIPTORS {
            assert_eq!(descriptor_for_name(name), Some(*json));
            // not bound to any selector
            assert!(
                SELECTOR_DESCRIPTORS.iter().all(|(_, n, _, _)| n != name),
                "name-only descriptor {name} unexpectedly has a selector"
            );
        }
    }

    /// THE IR-v2 ROUND-TRIP: every `V2_DESCRIPTORS` entry round-trips through the v2 decoder
    /// `descriptor_ir2::parse_vm_descriptor2` — a `"ir":2` wire with the five EPOCH tables and the
    /// lookup/mem_op/map_op grammar, NOT the v1 wire — into the structure the prover consumes
    /// (five tables, positive width, empty v1 carriers). The Lean↔JSON drift gate is generate-fresh
    /// `scripts/check-descriptor-drift.sh`, not a self-consistent FP rehash.
    #[test]
    fn v2_descriptors_parse() {
        assert_eq!(V2_DESCRIPTORS.len(), 28, "expected 28 IR-v2 descriptors");
        for (key, json, _fp) in V2_DESCRIPTORS {
            // round-trips through the v2 multi-table decoder
            let d = parse_vm_descriptor2(json)
                .unwrap_or_else(|e| panic!("v2 descriptor {key} failed parse_vm_descriptor2: {e}"));
            assert_eq!(
                d.tables.len(),
                5,
                "v2 descriptor {key}: not the five EPOCH tables"
            );
            assert!(d.trace_width > 0, "v2 descriptor {key}: zero trace_width");
            // graduated v1 descriptors carry NO legacy hash-site/range carriers (lookup-shaped).
            assert!(
                d.hash_sites.is_empty() && d.ranges.is_empty(),
                "v2 descriptor {key}: a graduated descriptor must carry empty v1 carriers"
            );
            // the accessor resolves it
            assert_eq!(descriptor2_for_key(key), Some(*json));
        }
        // The transfer v2 graduated descriptor is present and 186-wide (the validated reference).
        let t = parse_vm_descriptor2(
            descriptor2_for_key("transferVmDescriptor2").expect("transfer v2 present"),
        )
        .unwrap();
        assert_eq!(
            t.trace_width, 216,
            "graduated transfer = 188 base + 7·4 chip lane cols (Phase B-GATE: 4 hash sites)"
        );
        assert_eq!(t.public_input_count, 35);
    }

    /// THE ROTATION LAYOUT DRIFT GUARD (staged): rebuild the Lean
    /// `rotationLayoutManifest` byte-for-byte from `effect_vm::columns::rotation`
    /// + `pi::v3` and compare against the committed Lean-emitted file. Both sides
    /// PIN (Lean `#guard`s the same literal), neither parses — a layout fact can
    /// only change by re-emitting from Lean AND re-anchoring these constants.
    #[test]
    fn rotation_layout_matches_lean() {
        use crate::effect_vm::columns::rotation as rot;
        use crate::effect_vm::pi;
        let twin = format!(
            "{{\"v\":\"dregg-rotation-layout-v3-staged\",\"block_size\":{},\"cells_root\":{},\
             \"reg_base\":{},\"num_registers\":{},\"cap_root\":{},\"nullifier_root\":{},\
             \"heap_root\":{},\"lifecycle\":{},\"epoch\":{},\"committed_height\":{},\
             \"iroot\":{},\"state_commit\":{},\"chain_base\":{},\"num_chain\":{},\
             \"probe_width\":{},\"chain_arity\":{},\"pi_v3\":{{\"v2_base_count\":{},\
             \"committed_height\":{},\"rate_bound_tag\":{},\"challenge_window_tag\":{}}}}}",
            rot::BLOCK_SIZE,
            rot::CELLS_ROOT,
            rot::REG_BASE,
            rot::NUM_REGISTERS,
            rot::CAP_ROOT,
            rot::NULLIFIER_ROOT,
            rot::HEAP_ROOT,
            rot::LIFECYCLE,
            rot::EPOCH,
            rot::COMMITTED_HEIGHT,
            rot::IROOT,
            rot::STATE_COMMIT,
            rot::CHAIN_BASE,
            rot::NUM_CHAIN,
            rot::PROBE_WIDTH,
            rot::CHAIN_ARITY,
            pi::BASE_COUNT,
            pi::v3::COMMITTED_HEIGHT,
            pi::v3::RATE_BOUND_TAG,
            pi::v3::CHALLENGE_WINDOW_TAG,
        );
        assert_eq!(
            twin, ROTATION_LAYOUT_V3_STAGED_JSON,
            "rotation layout drift: columns::rotation / pi::v3 no longer match the \
             Lean-emitted manifest (re-emit EmitRotationV3.lean and re-anchor)"
        );
    }

    /// The v3-staged probe registry: round-trip through the IR-v2 decoder + PRESENCE
    /// at EVERY register count — each probe's chip-lookup chain must absorb EVERY
    /// rotated limb column exactly once, in the absorption order, with the final
    /// digest on `STATE_COMMIT` (a re-emit that drops a limb — e.g. the heap_root, or
    /// a widened register — fails HERE, before any prover runs). The presence-refusal
    /// tooth scales with the block: a wider block with untested columns would be
    /// worse than a narrow one.
    #[test]
    fn v3_staged_descriptors_parse_and_cover_all_limbs() {
        use crate::descriptor_ir2::VmConstraint2;
        use crate::effect_vm::columns::rotation as rot;
        use crate::lean_descriptor_air::LeanExpr;
        assert_eq!(
            V3_STAGED_DESCRIPTORS.len(),
            3,
            "expected 3 v3-staged descriptors"
        );
        // The R=16 entry is the deployed reference: its parametric twin must agree with
        // the pinned `columns.rs::rotation` constants exactly.
        let l16 = rotation_layout_for(16);
        assert_eq!(l16.committed_height, rot::COMMITTED_HEIGHT);
        assert_eq!(l16.iroot, rot::IROOT);
        assert_eq!(l16.state_commit, rot::STATE_COMMIT);
        assert_eq!(l16.block_size, rot::BLOCK_SIZE);
        assert_eq!(l16.chain_base, rot::CHAIN_BASE);
        assert_eq!(l16.num_chain, rot::NUM_CHAIN);
        assert_eq!(l16.probe_width, rot::PROBE_WIDTH);
        // R=24: exact 3-fill (no mid arity-2 site); R=32: two arity-2 mid sites.
        assert_eq!(rotation_layout_for(24).probe_width, 43);
        assert_eq!(rotation_layout_for(24).num_chain, 10);
        assert_eq!(rotation_layout_for(32).probe_width, 55);
        assert_eq!(rotation_layout_for(32).num_chain, 14);
        for (key, json, _fp) in V3_STAGED_DESCRIPTORS {
            let r = match *key {
                "rotationProbeVmDescriptor2" => 16,
                "rotationProbeVmDescriptorR24" => 24,
                "rotationProbeVmDescriptorR32" => 32,
                other => panic!("unknown v3-staged key {other}"),
            };
            let lay = rotation_layout_for(r);
            let d = parse_vm_descriptor2(json)
                .unwrap_or_else(|e| panic!("v3 staged {key} failed parse_vm_descriptor2: {e}"));
            // Phase B-GATE: graduated width = probe width + 7·n_sites lane cols
            // (n_sites = num_chain head/body absorbs + 1 iroot absorb).
            assert_eq!(
                d.trace_width,
                lay.probe_width + 7 * (lay.num_chain + 1),
                "{key}: probe width + 7·n_sites chip lane cols"
            );
            assert_eq!(d.public_input_count, 2);
            assert!(
                d.hash_sites.is_empty() && d.ranges.is_empty(),
                "graduated carriers only"
            );
            // PRESENCE: walk the chip lookups in order; collect fresh (non-chain) absorbed
            // columns; they must be exactly 0..=IROOT in order, and each non-final site's
            // digest must be the next chain carrier, the final site's digest STATE_COMMIT.
            // Also: every site's fresh-input arity ∈ {4 head, 3, 1} (+1 digest ⇒ chip
            // arity ∈ {2,4}; an arity-3 site would REFUSE on the deployed chip AIR).
            let mut absorbed: Vec<usize> = Vec::new();
            let mut digests: Vec<usize> = Vec::new();
            for c in &d.constraints {
                if let VmConstraint2::Lookup(l) = c {
                    let vars: Vec<usize> = l
                        .tuple
                        .iter()
                        .filter_map(|e| match e {
                            LeanExpr::Var(v) => Some(*v),
                            _ => None,
                        })
                        .collect();
                    // Phase B-GATE: the 17-wide tuple's var run is `[input vars …, out0 (digest),
                    // lane1..lane7]`. The output block is the last CHIP_OUT_LANES vars; the digest
                    // (out0) is its HEAD, the inputs are everything before it.
                    use crate::descriptor_ir2::CHIP_OUT_LANES;
                    let split = vars.len() - CHIP_OUT_LANES;
                    let inputs = &vars[..split];
                    let digest = &vars[split];
                    digests.push(*digest);
                    let fresh: Vec<usize> = inputs
                        .iter()
                        .copied()
                        .filter(|v| *v < lay.block_size)
                        .collect();
                    let chained = inputs.len() - fresh.len();
                    assert!(
                        (chained == 0 && fresh.len() == 4)
                            || (chained == 1 && (fresh.len() == 3 || fresh.len() == 1)),
                        "{key}: site shape must be 4-fresh head or digest+3 / digest+1 \
                         (chip arity ∈ {{2,4}}), got {chained} chained + {} fresh",
                        fresh.len()
                    );
                    absorbed.extend(fresh);
                }
            }
            let expected: Vec<usize> = (0..=lay.iroot).collect();
            assert_eq!(
                absorbed, expected,
                "{key}: the probe must absorb every rotated limb column exactly once, in \
                 the absorption order (cells root, {r} registers, cap/nullifier/heap \
                 roots, lifecycle, epoch, committed height, iroot LAST)"
            );
            let expected_digests: Vec<usize> = (0..lay.num_chain)
                .map(|k| lay.chain_base + k)
                .chain(std::iter::once(lay.state_commit))
                .collect();
            assert_eq!(
                digests, expected_digests,
                "{key}: chained digest carriers, final = STATE_COMMIT"
            );
        }
    }

    /// THE CAVEAT-OPERAND LAYOUT DRIFT GUARD (staged): rebuild the Lean
    /// `rotationCaveatLayoutManifest` byte-for-byte from
    /// `columns::rotation::caveat` and compare against the committed
    /// Lean-emitted file. Both sides PIN (Lean `#guard`s the same literal),
    /// neither parses.
    #[test]
    fn rotation_caveat_layout_matches_lean() {
        use crate::effect_vm::columns::rotation::caveat as cav;
        let twin = format!(
            "{{\"v\":\"dregg-rotation-caveat-layout-v3-staged\",\"r\":{},\
             \"caveat_base\":{},\"count_col\":{},\"entry_base\":{},\"entry_size\":{},\
             \"max_caveats\":{},\"manifest_size\":{},\"chain_base\":{},\"num_chain\":{},\
             \"caveat_commit\":{},\"probe_width\":{},\"domain_registers\":{},\
             \"domain_heap\":{},\"pub_commit\":{},\"pub_height\":{},\"pub_caveat\":{}}}",
            cav::R,
            cav::BASE,
            cav::COUNT_COL,
            cav::ENTRY_BASE,
            cav::ENTRY_SIZE,
            cav::MAX_CAVEATS,
            cav::MANIFEST_SIZE,
            cav::CHAIN_BASE,
            cav::NUM_CHAIN,
            cav::CAVEAT_COMMIT,
            cav::PROBE_WIDTH,
            cav::DOMAIN_REGISTERS,
            cav::DOMAIN_HEAP,
            cav::PUB_COMMIT,
            cav::PUB_HEIGHT,
            cav::PUB_CAVEAT,
        );
        assert_eq!(
            twin, ROTATION_CAVEAT_LAYOUT_V3_STAGED_JSON,
            "caveat-operand layout drift: columns::rotation::caveat no longer matches \
             the Lean-emitted manifest (re-emit EmitRotationV3.lean and re-anchor)"
        );
    }

    /// The staged caveat probe: round-trip through the IR-v2 decoder + PRESENCE — the
    /// chip-lookup chain must absorb the WHOLE R=24 rotated block (cells root … iroot)
    /// AND the WHOLE 29-felt caveat manifest block (count + every entry's type tag,
    /// DOMAIN TAG, KEY, params) exactly once, in order, with the rotation digest
    /// landing on `state_commit` and the caveat digest on `CAVEAT_COMMIT`. A re-emit
    /// that drops a manifest column (e.g. a domain tag) fails HERE, before any prover
    /// runs.
    #[test]
    fn v3_staged_caveat_descriptor_parses_and_covers_manifest() {
        use crate::descriptor_ir2::VmConstraint2;
        use crate::effect_vm::columns::rotation::caveat as cav;
        use crate::lean_descriptor_air::LeanExpr;
        assert_eq!(V3_STAGED_CAVEAT_DESCRIPTORS.len(), 1);
        let (key, json, _fp) = V3_STAGED_CAVEAT_DESCRIPTORS[0];
        let d = parse_vm_descriptor2(json)
            .unwrap_or_else(|e| panic!("{key} failed parse_vm_descriptor2: {e}"));
        // Phase B-GATE: graduated width = caveat probe width + 7·n_sites chip lane cols (the
        // before/after rotated absorbs + the caveat absorbs); the surplus is a multiple of 7.
        assert!(
            d.trace_width >= cav::PROBE_WIDTH && (d.trace_width - cav::PROBE_WIDTH) % 7 == 0,
            "{key}: caveat probe width + 7·n_sites chip lane cols"
        );
        assert_eq!(d.public_input_count, 3, "{key}: three PI pins");
        assert!(
            d.hash_sites.is_empty() && d.ranges.is_empty(),
            "graduated carriers only"
        );
        let rot = rotation_layout_for(cav::R);
        // Walk the chip lookups in order; collect fresh (non-carrier) absorbed columns.
        // Fresh = a rotated limb column (0..=iroot) or a caveat manifest column
        // (BASE..BASE+MANIFEST_SIZE). Expected coverage: the rotation absorption order,
        // then the manifest columns in order. Digest carriers: the rotation chain +
        // state_commit, then the caveat chain + CAVEAT_COMMIT.
        let is_fresh =
            |v: usize| v <= rot.iroot || (cav::BASE..cav::BASE + cav::MANIFEST_SIZE).contains(&v);
        let mut absorbed: Vec<usize> = Vec::new();
        let mut digests: Vec<usize> = Vec::new();
        for c in &d.constraints {
            if let VmConstraint2::Lookup(l) = c {
                let vars: Vec<usize> = l
                    .tuple
                    .iter()
                    .filter_map(|e| match e {
                        LeanExpr::Var(v) => Some(*v),
                        _ => None,
                    })
                    .collect();
                // Phase B-GATE: 17-wide tuple — output block is the last CHIP_OUT_LANES vars; out0
                // (the digest) is its head, inputs precede it.
                use crate::descriptor_ir2::CHIP_OUT_LANES;
                let split = vars.len() - CHIP_OUT_LANES;
                let inputs = &vars[..split];
                let digest = &vars[split];
                digests.push(*digest);
                let fresh: Vec<usize> = inputs.iter().copied().filter(|v| is_fresh(*v)).collect();
                let chained = inputs.len() - fresh.len();
                assert!(
                    (chained == 0 && fresh.len() == 4)
                        || (chained == 1 && (fresh.len() == 3 || fresh.len() == 1)),
                    "{key}: site shape must be 4-fresh head or carrier+3 / carrier+1 \
                     (chip arity ∈ {{2,4}}), got {chained} chained + {} fresh",
                    fresh.len()
                );
                absorbed.extend(fresh);
            }
        }
        let expected: Vec<usize> = (0..=rot.iroot)
            .chain(cav::BASE..cav::BASE + cav::MANIFEST_SIZE)
            .collect();
        assert_eq!(
            absorbed, expected,
            "{key}: must absorb every rotated limb AND every caveat manifest felt \
             (count, type tags, DOMAIN TAGS, KEYS, params) exactly once, in order"
        );
        let expected_digests: Vec<usize> = (0..rot.num_chain)
            .map(|k| rot.chain_base + k)
            .chain(std::iter::once(rot.state_commit))
            .chain((0..cav::NUM_CHAIN).map(|k| cav::CHAIN_BASE + k))
            .chain(std::iter::once(cav::CAVEAT_COMMIT))
            .collect();
        assert_eq!(
            digests, expected_digests,
            "{key}: rotation chain → state_commit, then caveat chain → CAVEAT_COMMIT"
        );
    }

    /// THE FULL-COHORT REGEN guard (`ROTATION-CUTOVER.md` §5 item 1): every line of the
    /// staged 26-descriptor registry round-trips through the IR-v2 decoder, and each
    /// descriptor carries the rotated appendix EXACTLY — two rotated state blocks (each
    /// absorbing cells-root … iroot in order onto its own state-commit carrier) + the
    /// widened-caveat region (the 29-felt manifest onto CAVEAT_COMMIT), with the four
    /// appended PI pins (rotated OLD/NEW commit · height · caveat commit) at the
    /// descriptor's own `piCount..piCount+3`. A re-emit that drops a limb, a manifest felt,
    /// or a PI pin fails HERE, before any prover runs. STAGED: nothing on the live wire.
    #[test]
    fn v3_staged_registry_parses_and_covers() {
        use crate::descriptor_ir2::VmConstraint2;
        use crate::effect_vm::columns::EFFECT_VM_WIDTH;
        use crate::effect_vm::columns::rotation::caveat as cav;
        use crate::lean_descriptor_air::{LeanExpr, VmConstraint};

        // The DEPLOYED rotated geometry (the v12 pre_limbs re-lay: NUM_PRE_LIMBS = 112 — the bare
        // R=24 registers + cells/cap/nullifier/commitments/heap/lifecycle/epoch/height/disc roots +
        // the 8-felt completion limbs 37..87 + the v12 carrier-material octets 88..111). Source-of-truth = the canonical
        // `trace_rotated` constants (which STEP-1 grew), NOT re-hardcoded literals; mirrors the Lean
        // `EffectVmEmitRotationV3` §1 constants and the caveat region inside it.
        use crate::effect_vm::trace_rotated::{
            B_CHAIN_BASE, B_COMMITTED_HEIGHT, B_IROOT, B_SPAN, B_STATE_COMMIT,
        };
        const V1_WIDTH: usize = EFFECT_VM_WIDTH;
        // chain carriers occupy `[B_CHAIN_BASE, B_SPAN)` (the head digest + one per 3-wide group).
        const B_NUM_CHAIN: usize = B_SPAN - B_CHAIN_BASE; // 37 (v12: 112 limbs)
        // The caveat region grew 39 → 43 with the dsl rc-EMIT (the 4-felt `Witnessed{Dfa}`
        // route-commitment carrier at in-region 39..=42) and 43 → 45 with the rc FOLD, which
        // ABSORBS that carrier into the published commitment through two further chip sites. All
        // three offsets are Lean-emitted (`layout_generated`); only the PI pins (`withDfaRcPins`)
        // are per-member.
        use crate::effect_vm::trace_rotated::{
            C_COMMIT, C_DFA_RC_OFF, C_MANIFEST_COMMIT, C_RC_CARRIER, C_SPAN, DFA_RC_LEN,
        };
        const APPENDIX_SPAN: usize = 2 * B_SPAN + C_SPAN;

        let mut n = 0usize;
        for line in V3_STAGED_REGISTRY_TSV.lines() {
            if line.is_empty() {
                continue;
            }
            n += 1;
            let mut it = line.splitn(3, '\t');
            let key = it.next().expect("tsv key");
            let name = it.next().expect("tsv name");
            let json = it.next().expect("tsv json");
            let d = parse_vm_descriptor2(json)
                .unwrap_or_else(|e| panic!("v3 registry {key} failed parse_vm_descriptor2: {e}"));

            // THE CAP-OPEN MEMBERS (the LIVE `transferCapOpenEffV3`/`attenuateCapOpenEffV3` + 6 fan-out) carry
            // the 59-column cap-membership APPENDIX past the shared rotated layout (= V1_WIDTH +
            // APPENDIX_SPAN + 59) plus 1 leaf + 16 node chip-lookups + the cap-open base gates. The
            // appendix is 59 = the 58 prior columns + 1 `effBit` column (residual (a): the turn's
            // ACTUAL effect-kind bit, against which the general `facetEffGate` binds the leaf mask —
            // not the constant EFFECT_TRANSFER). Both share the appendix (base-agnostic), so they are
            // audited on the SAME own contract (width, PI count, cap-open chip lookups present) and
            // SKIP the rotated-cohort absorb/digest/pin equalities below.
            // The cap-open authority members: the 2 transfer/attenuate legs + the 6 effect-general
            // fan-out legs (delegate, introduce, grantCap, revoke, refreshDelegation,
            // revokeCapability), each carrying the SAME 59-column appendix (base-agnostic) over its
            // own rotated base. The fan-out legs' appendix binds the cap to THAT effect-kind bit (the
            // general `facetEffGate` / `effBitGateFor (1<<<n)`), not the constant EFFECT_TRANSFER.
            if key.contains("CapOpen") {
                // The TURN-IDENTITY weld (`transferCapOpenTBVmDescriptor2R24`,
                // `CapOpenTurnPins.effCapOpenV3TB`) is the cap-open PLUS **one** PI slot and **no**
                // column: the pin it appends names the EXISTING `capOpenCols.src` column, which
                // `targetBindGate` and the depth-16 membership open already read. So the TB member's
                // `trace_width` EQUALS its non-TB twin's, and it carries 46 + 1 = 47 PIs.
                //
                // ⚑ 2026-07-31: this read "+2 turn-identity columns … and 46 + 3 = 49 PIs". The weld
                // used to add `capOpenActorCol`/`capOpenDstCol` and pin them to PI 47/48 as the
                // turn's `actor`/`dst`. Those two columns were introduced BY that weld and read by
                // no other constraint in the member, so each pin was `local[c] == pi[k]` with the
                // prover choosing both sides — a published felt for *who acted* that a light client
                // could not rely on, and `last_row_anchor_forge` measured the forge succeeding at
                // the AIR. Both columns and both pins are gone at the Lean source. The successor
                // that publishes actor/dst AND forces them (through the Lamport turn-digest lookup
                // whose 8-felt output the signed message recomposes) is
                // `Dregg2/Circuit/Emit/TurnAuthCapOpenWeld.lean`, staged.
                let is_tb = key.contains("CapOpenTB");
                let extra_cols = 0;
                let _ = is_tb;
                // The spawn cap-open members (`spawnCapOpen`/`spawnWriteCapOpen`) are the ONLY cap-fanout
                // members built over a BIRTH base (`spawnV3`/`spawnWriteV3`): spawn carries the extra
                // new-cell-key PI weld (`ROT_NEW_CELL_KEY_PI = ROT_PI_COUNT`, the child id pinned on
                // row 0), so its rotated base publishes `ROT_PI_COUNT + 1` PIs. So the cap-open wrapper
                // inherits that. Every other cap-open member rides a non-birth base (`ROT_PI_COUNT`).
                // (Those were 47 / 46 before the 2026-08-07 seven-slot compaction.)
                let is_spawn = key.starts_with("spawn");
                let extra_pis = if is_tb { 1 } else { 0 } + if is_spawn { 1 } else { 0 };
                // Phase H-CAP-8: the FAITHFUL 8-FELT cap-open appendix. The native `node8` arity-16
                // tree commits the WHOLE 8-felt digest group per absorb (the 7 spare permutation
                // lanes are PROMOTED into the bound fold — no separate `7·17` lane tail). The Lean
                // twin `CapOpenEmit.CAP_OPEN_SPAN = 7 + 8 + DEPTH·17 + 8 + 2 + MASK_BITS`:
                //   7 leaf scalar + 8 leaf-digest + DEPTH·(8 sib + 1 dir + 8 node) + 8 cap_root
                //   + src + effBit + 32 mask-bit = 7 + 8 + 16·17 + 8 + 2 + 32 = 329.
                let cap_span = 7 + 8 + 16 * 17 + 8 + 2 + 32; // CAP_OPEN_SPAN = 329
                // The cap-WRITE members (`effCapOpenWriteV3`: attenuate + the delegation-mutating
                // writes) carry the AFTER-SPINE recompute appendix PAST the 329-col read appendix —
                // `CapOpenEmit.AFTER_SPINE_SPAN = 15 + 8·DEPTH = 143` (after-leaf + after-leaf-digest
                // + DEPTH·8 after-node), forcing the faithful 8-felt cap-WRITE (`*_forces_write8`).
                let after_spine_span = 15 + 8 * 16; // AFTER_SPINE_SPAN = 143
                // THE AVAILABILITY-WELD PAD (GAP #4, cap-open member): a hardened `…-v1-avail`
                // transfer cap-open member widens its v1 FACE by the avail witness columns, so its
                // rotated base — and hence the graduated width the cap-open appendix anchors at —
                // shifts by the pad. Zero for every bare member.
                let cap_avail_pad =
                    crate::effect_vm::trace_rotated::avail_pad_for_descriptor_name(name);
                let rot_base = V1_WIDTH + APPENDIX_SPAN + cap_avail_pad;
                let appendix = cap_span + extra_cols;
                // The rotated base graduates by `7·n_rot_sites` wire-commit lane cols (still 7-felt;
                // only the CAP DIGEST groups went 8-felt). So the width is
                //   rot_base + 7·n_sites + 329 (+ 143 after-spine for write/attenuate).
                // The TB weld contributes NO column (see above), so it does not appear here.
                // 143 % 7 ≠ 0, so the with/without-after-spine forms are mutually EXCLUSIVE — the
                // residual cleanly decides which member this is (no name-keyed dispatch).
                assert!(
                    d.trace_width >= rot_base + appendix,
                    "{key}: cap-open trace width below rotated base + 329 cap-membership appendix"
                );
                let surplus = d.trace_width - rot_base - appendix;
                let has_after_spine = surplus % 7 != 0;
                let lane_surplus = if has_after_spine {
                    surplus.checked_sub(after_spine_span)
                } else {
                    Some(surplus)
                };
                assert!(
                    matches!(lane_surplus, Some(s) if s % 7 == 0),
                    "{key}: cap-open trace width = rotated base (+ 7·n_rot_sites lane cols) + 329 \
                     cap-membership appendix (+143 after-spine for write/attenuate). The TB weld \
                     adds NO column: it pins the EXISTING `src` column."
                );
                let rot_pi_count = crate::effect_vm::trace_rotated::ROT_PI_COUNT;
                assert_eq!(
                    d.public_input_count,
                    rot_pi_count + extra_pis,
                    "{key}: cap-open carries the rotated {rot_pi_count}-PI vector (+1 turn-identity \
                     `src` PI for TB, +1 new-cell-key PI for the spawn birth base)"
                );
                // The cap-open READ appendix declares EXACTLY 17 poseidon2 chip lookups whose DIGEST
                // (out0, tuple col CHIP_RATE+1) lands in the cap-membership CORE column block
                // `[cap_open_base, cap_open_base + 287)` (= leaf 7 + leaf-digest 8 + DEPTH·17 level
                // blocks; `capRoot` starts at +287): 1 leaf absorb + 16 node absorbs. The after-spine
                // recompute's own 17 lookups land at `[cap_open_base + 329, …)` — PAST the core
                // window — so a write member still counts exactly the read spine's 17.
                use crate::descriptor_ir2::CHIP_RATE;
                // Recover the appendix base from the total width. The cap appendix starts at the
                // GRADUATED rotated width (`base.traceWidth`); for write/attenuate members the
                // after-spine sits past it, so subtract it too: `cap_open_base = trace_width -
                // CAP_OPEN_SPAN(329) (- AFTER_SPINE_SPAN(143) if write)`.
                let cap_membership_core = 7 + 8 + 16 * 17; // leaf + leaf-digest + DEPTH·17 = 287
                let cap_open_base = d.trace_width
                    - cap_span
                    - extra_cols
                    - if has_after_spine { after_spine_span } else { 0 };
                let cap_lookups = d
                    .constraints
                    .iter()
                    .filter(|c| {
                        if let VmConstraint2::Lookup(l) = c {
                            matches!(
                                l.tuple.get(CHIP_RATE + 1),
                                Some(LeanExpr::Var(v))
                                    if *v >= cap_open_base && *v < cap_open_base + cap_membership_core
                            )
                        } else {
                            false
                        }
                    })
                    .count();
                assert_eq!(
                    cap_lookups, 17,
                    "{key}: cap-open read appendix declares 1 leaf + 16 node chip lookups"
                );
                continue;
            }

            // Phase B-GATE: graduation appends `7·n_sites` chip lane columns past the rotated base,
            // so the GRADUATED width's surplus over the appendix is a multiple of 7 (n_sites varies
            // by v1 face; concrete widths pinned by the emit goldens + fingerprints). Two deployed
            // welds ride KNOWN, non-lane columns PAST the graduated width — account for each
            // EXPLICITLY (never fold it into the 7·n_sites lane count), CONFIRM it landed, and strip
            // back to the graduated width before the mod-7 lane check:
            //   · the GENTIAN FLAG-DAY bare-floor-refuse weld (`BareCohortFloorRefuse`) appends three
            //     disjoint decode+refuse aux blocks ANCHORED at GRAD_ROT_WIDTH onto every deployed
            //     bare cohort member (the `-gentian-deployed-bare-refuse` suffix), extending its width
            //     to exactly `floor_col(last)+1`;
            //   · the STAGED discharge/vault satisfaction descriptors ride their satisfaction-gate
            //     FIELD columns past the graduated transfer base (settleEscrow's ride EXISTING field
            //     columns and add none; discharge/vault add the cursor/total/due + G5 free-param /
            //     no-dilution gadget columns).
            use crate::effect_vm::bare_floor_refuse_weld as refuse;
            use crate::effect_vm::trace_rotated::GRAD_ROT_WIDTH;
            // THE AVAILABILITY-WELD PAD (GAP #4): a hardened `…-v1-avail` transfer/burn member
            // widens its v1 FACE by the avail witness columns, so its rotated appendix, refuse
            // anchor, and rc carrier all shift by the pad. Zero for every bare member.
            let avail_pad = crate::effect_vm::trace_rotated::avail_pad_for_descriptor_name(name);
            // §HETEROGENEOUS GEOMETRY. Two members do NOT graduate to `GRAD_ROT_WIDTH`, and the
            // reason is the ROTATION-SITE COUNT, not the face width:
            //   * `setFieldDynV1Face` has the SAME v1 face width (`EFFECT_VM_WIDTH`) as the cohort but
            //     `hashSites := []` — ZERO hash sites against the standard 4. Since
            //     `GRAD_ROT_WIDTH = ROT_WIDTH + 7·N_ROT_SITES`, dropping 4 sites drops exactly
            //     4·7 = 28 LANE columns, so it graduates at 1647 − 28 = 1619 (width 1664).
            //   * `custom` rides that same zero-site shape PLUS 8 exact carrier teeth columns
            //     (commit high4 + VK high4), appended PAST the lanes: base 1627.
            // The lane deficit is a multiple of 7 BY CONSTRUCTION (it is 7 per dropped site), so it
            // cannot break the `% 7` lane invariant below. Custom's 4 teeth CAN — they are not lane
            // columns — so they are the only thing that must come out before the modulus is taken.
            const SETFIELD_DYN_LANE_DEFICIT: usize = 28; // 4 dropped hash sites × 7 lane cols
            const CUSTOM_CARRIER_TEETH: usize = 8;
            let (lane_deficit, commit_teeth) = match key {
                "customVmDescriptor2R24" => (SETFIELD_DYN_LANE_DEFICIT, CUSTOM_CARRIER_TEETH),
                "setFieldDynVmDescriptor2R24" => (SETFIELD_DYN_LANE_DEFICIT, 0),
                _ => (0, 0),
            };
            let is_refuse_welded = name.ends_with("-gentian-deployed-bare-refuse");
            let graduated_width = if is_refuse_welded {
                // The three per-tag refuse blocks anchor at the member's OWN graduated width
                // (GRAD_ROT_WIDTH + its avail pad); the deployed width extends EXACTLY to cover
                // the last floor column (`floor_col(NB-1)+1`). CONFIRM the flip is REAL: assert
                // that exact geometry AND that all three `floor_col(b) == 0` refuse gates are
                // PRESENT in the committed descriptor (a positive coverage tooth for the
                // flag-day, not a width fudge). Derived from the weld's own constants, so a
                // stride/block change moves BOTH the width tooth and the gate check together.
                const NB: usize = refuse::CAPACITY_TAGS.len();
                // The refuse blocks anchor at the member's OWN graduated base (see §HETEROGENEOUS
                // GEOMETRY above), so re-base the cohort's `GRAD_ROT_WIDTH`-anchored `floor_col`.
                let member_base = GRAD_ROT_WIDTH - lane_deficit + commit_teeth;
                let rebase = |c: usize| c - GRAD_ROT_WIDTH + member_base;
                let refuse_end = rebase(refuse::floor_col(NB - 1)) + 1 + avail_pad;
                assert_eq!(
                    d.trace_width, refuse_end,
                    "{key}: refuse-welded member width must extend exactly to cover the {NB} \
                     bare-floor-refuse aux blocks anchored at its own graduated width"
                );
                for b in 0..NB {
                    let fc = rebase(refuse::floor_col(b)) + avail_pad;
                    assert!(
                        d.constraints.iter().any(|c| matches!(
                            crate::descriptor_ir2::row_local_body(c).as_deref(),
                            Some(LeanExpr::Var(v)) if *v == fc
                        )),
                        "{key}: bare-floor-refuse gate (floor_col({b}) == {fc} == 0) missing — the \
                         gentian flag-day weld did not land on this cohort member"
                    );
                }
                member_base + avail_pad
            } else if key == "dischargeSatVmDescriptor2R24" || key == "vaultSatVmDescriptor2R24" {
                // The STAGED discharge/vault satisfaction descriptors graduate on the transfer base
                // (GRAD_ROT_WIDTH) and carry their satisfaction-gate FIELD columns PAST it. Pin the
                // exact committed widths (a drift tooth on the satisfaction-gadget span, read from the
                // committed registry TSV) and strip back to the graduated base for the lane check.
                let expected = if key == "dischargeSatVmDescriptor2R24" {
                    // 1720 -> 1764 at the nine-lane epoch, 1764 -> 1780 at the rc FOLD:
                    // GRAD_ROT_WIDTH + the cursor/total/due + G5 free-param bind columns.
                    // ⚑ 1780 -> 1892 at the FIELDS-CANONICITY emit: the satisfaction-gate span is
                    // UNCHANGED (73 columns past the graduated base, and it must be — the wrap adds
                    // no gadget); the whole +112 is `GRAD_ROT_WIDTH` 1707 -> 1819 carrying the
                    // canonicity aux region through `APPENDIX_SPAN` 539 -> 651, with `N_ROT_SITES`
                    // unmoved (`fieldsCanonical9At_hashSites`). 1819 + 73 = 1892.
                    // ⚑ 1892 -> 1914 at the KEY NONET (`76c3f7b9b`). The satisfaction span is AGAIN
                    // unchanged at 73; the whole +22 is `GRAD_ROT_WIDTH` 1819 -> 1841, and it splits:
                    //    +8  `APPENDIX_SPAN` 651 -> 659 = 2·(B_SPAN 247 -> 251), the two rotated
                    //        blocks each gaining 3 pre-limbs + 1 chain carrier. `C_SPAN` (45) and
                    //        `CANON9_SPAN` (112) are untouched, so the appendix moves by the blocks
                    //        alone.
                    //   +14  `ROT_APPENDIX_SITES` 136 -> 138 × the 7 graduated lane columns each.
                    //        Two sites, one per block: the extra chain carrier is one more absorb.
                    // 1841 + 73 = 1914, and `settleEscrowSatVmDescriptor2R24` emits at 1841 flat —
                    // a third reading of the same base, from the same TSV.
                    1914
                } else {
                    // GRAD_ROT_WIDTH + the no-dilution (Ta·m ≤ Sa·d) satisfaction columns.
                    // Re-pinned 2121 → 2185 from the emitted TSV: the satisfaction-gadget span grew
                    // by 64 columns with the arity-3 IMT / AAFI accumulator rewiring. This is a raw
                    // drift tooth (a literal read off the committed artifact), so it MUST be re-read
                    // whenever the gadget changes — it does not derive itself. Re-read again
                    // 2185 -> 2229 at the nine-lane epoch, 2229 -> 2245 at the rc FOLD (both members
                    // ride GRAD_ROT_WIDTH, so both moved by the same +16).
                    // ⚑ 2245 -> 2357 at the FIELDS-CANONICITY emit, the SAME +112 as discharge and
                    // for the same reason: 1819 + 538 (the unchanged satisfaction span). That both
                    // members moved by exactly the base's delta is the check — a satisfaction gadget
                    // that had ALSO grown would show up as a member-specific residue here.
                    // ⚑ 2357 -> 2379 at the KEY NONET, and the check fires clean a second time:
                    // +22, EXACTLY discharge's delta and exactly `GRAD_ROT_WIDTH` 1819 -> 1841
                    // (decomposed on the discharge arm above). 1841 + 538 — the no-dilution span is
                    // unmoved, so neither gadget grew under the widening.
                    2379
                };
                assert_eq!(
                    d.trace_width, expected,
                    "{key}: staged satisfaction descriptor width = graduated base + its \
                     satisfaction-gate columns"
                );
                GRAD_ROT_WIDTH
            } else {
                d.trace_width
            };
            // The graduated width is the (avail-padded) v1 face + the rotated appendix + `7·n_sites`
            // LANE columns + any COMMIT-TEETH columns appended past the lanes. Every member shares the
            // same v1 face width, and a dropped hash site removes a whole 7-column lane, so the lane
            // residue stays ≡ 0 (mod 7) for setFieldDyn's zero-site shape without any special-casing.
            // Only custom's 4 COMMIT-TEETH columns are non-lane, so they are the one thing that must
            // be taken out before the modulus — otherwise its residue is 4 and the invariant would be
            // "fixed" by fudging a face delta that does not exist.
            let lane_base = V1_WIDTH + avail_pad + APPENDIX_SPAN + commit_teeth;
            assert!(
                graduated_width >= lane_base && (graduated_width - lane_base) % 7 == 0,
                "{key}: rotated GRADUATED trace width = (avail-padded) v1 face + appendix + \
                 7·n_sites lane cols + commit teeth"
            );
            assert!(
                d.hash_sites.is_empty() && d.ranges.is_empty(),
                "{key}: graduated carriers only"
            );

            // The three appendix blocks, past the (avail-padded) v1 layout.
            let before_base = V1_WIDTH + avail_pad;
            let after_base = before_base + B_SPAN;
            let caveat_base = before_base + 2 * B_SPAN;

            // A "fresh limb" of the appendix is a column inside one of the three blocks'
            // LIMB ranges (before/after rotated limbs 0..=iroot, the caveat manifest
            // 0..MANIFEST_SIZE, or the 4-felt DFA route-commitment carrier the rc FOLD absorbs)
            // — NOT a chain-carrier column (those ride the accumulator as
            // inputs but are not absorbed data). We audit only appendix sites (digest >=
            // V1_WIDTH); the v1 descriptor's own chip lookups absorb columns < V1_WIDTH.
            let rc_lo = caveat_base + C_DFA_RC_OFF;
            let is_limb = |v: usize| -> bool {
                (before_base..=before_base + B_IROOT).contains(&v)
                    || (after_base..=after_base + B_IROOT).contains(&v)
                    || (caveat_base..caveat_base + cav::MANIFEST_SIZE).contains(&v)
                    || (rc_lo..rc_lo + DFA_RC_LEN).contains(&v)
            };
            let mut digests: Vec<usize> = Vec::new();
            let mut absorbed: Vec<usize> = Vec::new();
            for c in &d.constraints {
                if let VmConstraint2::Lookup(l) = c {
                    if l.table != crate::descriptor_ir2::TID_P2 {
                        continue;
                    }
                    // Phase B-GATE: the 17-wide tuple is `[arity, in0..in7, out0, lane1..lane7]`.
                    // out0 (the digest) is at fixed position CHIP_RATE + 1; the input vars are the
                    // bare-Var entries in `[1 ..= CHIP_RATE]` (lanes are NOT inputs).
                    use crate::descriptor_ir2::CHIP_RATE;
                    let LeanExpr::Var(digest) = l.tuple[CHIP_RATE + 1] else {
                        panic!("{key}: chip lookup out0 (col CHIP_RATE+1) must be a bare Var");
                    };
                    if digest >= V1_WIDTH {
                        digests.push(digest);
                        for e in &l.tuple[1..=CHIP_RATE] {
                            if let LeanExpr::Var(v) = e {
                                if is_limb(*v) {
                                    absorbed.push(*v);
                                }
                            }
                        }
                    }
                }
            }

            // Expected fresh absorption: before-block limbs 0..=iroot, after-block limbs,
            // then the caveat manifest 0..MANIFEST_SIZE — all relative to their bases.
            let mut expected_absorbed: Vec<usize> = Vec::new();
            expected_absorbed.extend((0..=B_IROOT).map(|i| before_base + i));
            expected_absorbed.extend((0..=B_IROOT).map(|i| after_base + i));
            expected_absorbed.extend((0..cav::MANIFEST_SIZE).map(|i| caveat_base + i));
            // ⚑ THE rc FOLD, measured on the committed bytes: the four DFA route-commitment
            // columns are ABSORBED, in order, right after the manifest. Until 2026-07-31 they were
            // absorbed by nothing — which is exactly why the `withDfaRcPins` pins on them bound
            // nothing and `dropUnforcedPins` deleted all 144 of them, taking the `CarrierWitness::
            // Dsl` fold arm down with them. If this line is ever deleted to "fix" a regen, the
            // pins go back to publishing a prover-chosen felt.
            expected_absorbed.extend((0..DFA_RC_LEN).map(|i| rc_lo + i));
            assert_eq!(
                absorbed, expected_absorbed,
                "{key}: appendix must absorb the BEFORE block, the AFTER block, the \
                 29-felt caveat manifest, then the 4-felt DFA route-commitment carrier, each \
                 limb exactly once in absorption order"
            );

            // Expected digest carriers: before chain → before state_commit; after chain →
            // after state_commit; caveat chain → manifest commit → rc carrier → CAVEAT COMMIT.
            let mut expected_digests: Vec<usize> = Vec::new();
            expected_digests.extend((0..B_NUM_CHAIN).map(|k| before_base + B_CHAIN_BASE + k));
            expected_digests.push(before_base + B_STATE_COMMIT);
            expected_digests.extend((0..B_NUM_CHAIN).map(|k| after_base + B_CHAIN_BASE + k));
            expected_digests.push(after_base + B_STATE_COMMIT);
            // Caveat region: carriers/commit are BLOCK-RELATIVE here (the cav::* constants are
            // absolute within the standalone caveat probe at base cav::BASE).
            let cav_chain_rel = cav::CHAIN_BASE - cav::BASE; // 29
            expected_digests.extend((0..cav::NUM_CHAIN).map(|k| caveat_base + cav_chain_rel + k));
            expected_digests.push(caveat_base + C_MANIFEST_COMMIT);
            expected_digests.push(caveat_base + C_RC_CARRIER);
            expected_digests.push(caveat_base + C_COMMIT);
            assert_eq!(
                digests, expected_digests,
                "{key}: before chain→state_commit, after chain→state_commit, \
                 caveat chain→manifest commit→rc carrier→CAVEAT_COMMIT"
            );

            // The four rotated commit pins always sit at the v1 prefix count
            // (`V1_PI_COUNT ..= V1_PI_COUNT + 3`), bound to: first-row before state_commit,
            // last-row after state_commit, last-row after committed_height, last-row caveat
            // commit. (The pins do NOT ride `public_input_count - 4`: note-spend appends a
            // FIFTH nullifier pin past them, so the commit-pin base is the FIXED v1 prefix.)
            //
            // ⚑ IMPORTED, NOT RE-TYPED. This was a local `const V1_PI_COUNT: usize = 42` shadowing
            // the real one, and the comment above it said `34` — a third number again, left over
            // from before Phase C. Two literals and a prose number for one fact is how the
            // 2026-08-07 seven-slot compaction (`docs/PI-DISPOSITION.md` §6) found this: the
            // shadow does not move when the layout does, so the test would have gone on measuring
            // a window nothing puts pins in and passing vacuously.
            let is_heap_write = key == "heapWriteVmDescriptor2R24";
            use crate::effect_vm::trace_rotated::V1_PI_COUNT;
            let pi_base = if is_heap_write {
                d.public_input_count - 4
            } else {
                V1_PI_COUNT
            };
            let mut pins: Vec<(usize, usize)> = Vec::new(); // (col, pi_index)
            for c in &d.constraints {
                if let VmConstraint2::Base(VmConstraint::PiBinding { col, pi_index, .. }) = c {
                    // only the rotated appendix pins (>= the v1 prefix); the four commit pins.
                    if (pi_base..pi_base + 4).contains(pi_index) {
                        pins.push((*col, *pi_index));
                    }
                }
            }
            pins.sort_by_key(|(_, pi)| *pi);
            assert_eq!(
                pins,
                vec![
                    (before_base + B_STATE_COMMIT, pi_base),
                    (after_base + B_STATE_COMMIT, pi_base + 1),
                    (after_base + B_COMMITTED_HEIGHT, pi_base + 2),
                    (caveat_base + C_COMMIT, pi_base + 3),
                ],
                "{key}: four appended PI pins (rotated OLD/NEW commit · height · caveat commit)"
            );

            // THE C4 LAST-FLIP-GATE: the rotated NOTE-SPEND carries a FIFTH appended PI pin
            // (`EffectVmEmitRotationV3.noteSpendV3`) welding the spend row's folded nullifier
            // (`param::NULLIFIER = param0`, col `PARAM_BASE + 0`) to rotated PI slot 38 on the
            // FIRST row — the rotated analog of the v1 hand-AIR D5 cross-binding (offset 198),
            // so a note-spending turn can rotate (`verify_full_turn` step 8 reads PI[46]). Every
            // OTHER cohort member has EXACTLY the four commit pins and 38 PIs.
            use crate::effect_vm::columns::{PARAM_BASE, param};
            let nullifier_pins: Vec<(usize, usize)> = d
                .constraints
                .iter()
                .filter_map(|c| match c {
                    VmConstraint2::Base(VmConstraint::PiBinding { col, pi_index, .. })
                        if *pi_index >= pi_base + 4 =>
                    {
                        Some((*col, *pi_index))
                    }
                    _ => None,
                })
                .collect();
            // THE UNIFORM DSL rc-EMIT (`withDfaRcPins`): every rotated COHORT member (+ the
            // fee-in-proof transfer) publishes the 4-felt `Witnessed{Dfa}` route-commitment
            // carrier (caveat-region offsets 39..=42) as its LAST 4 member PIs. Strip + assert
            // the quad here so the per-effect branches below keep their pre-rc expectations;
            // fail-closed on membership (a cohort member MISSING the rc pins, or a tail member
            // GROWING them, both fail).
            let rc_col = caveat_base + crate::effect_vm::trace_rotated::C_DFA_RC_OFF;
            let (rc_pins, nullifier_pins): (Vec<(usize, usize)>, Vec<(usize, usize)>) =
                nullifier_pins
                    .into_iter()
                    .partition(|(col, _)| (rc_col..rc_col + 4).contains(col));
            // NOT rc-wrapped: heapWrite (v3RegistryHeap tail, no v1 prefix), the dedicated
            // supply-mint (tail `withSelectorGate sel::MINT mintV3` over the BARE body), and the three
            // STAGED capacity-satisfaction welds (escrow/discharge/vault — no live routing). Everything
            // else here is the rc-wrapped cohort (+ transferFee).
            let rc_exempt = is_heap_write
                || key == "supplyMintVmDescriptor2R24"
                || key == "settleEscrowSatVmDescriptor2R24"
                || key == "dischargeSatVmDescriptor2R24"
                || key == "vaultSatVmDescriptor2R24";
            // ⚑ 2026-07-31 — THE rc PINS ARE BACK, AND THIS TIME THEY BIND. Between the
            // convergence re-emit and the rc FOLD (both on 2026-07-31) they were ABSENT and this
            // block asserted their absence, because `withDfaRcPins` appends ONLY `.piBinding`s and
            // the rc carrier columns (caveat-region offsets 39..=42) were read by NO gate, lookup,
            // hash site or range tooth: each pin was `local[c] == pi[k]` with the prover choosing
            // both sides, so `dropUnforcedPins` deleted all four from every rc-wrapped member — and
            // took `ivc_turn_chain::dsl_rc_claim_pi_lo`, which locates the fold's rc slot BY the
            // pin, down with them.
            //
            // The repair was NOT an exemption from the subtraction and NOT teaching the fold to
            // accept an unpinned slot: `EffectVmEmitRotationV3.caveatV3SitesAt` now ABSORBS the
            // carrier into the PUBLISHED caveat commitment (`caveatCommitRc`), so those four
            // columns are read by chip lookups, they are in `UnforcedPiPins.forcedCols`, and the
            // SAME unchanged subtraction keeps the pins. `circuit/tests/dsl_rc_emit.rs` measures
            // both poles on the committed bytes, including the adversary that moves the carrier
            // AND all four PIs together.
            //
            // So the two-sided assertion is restored: present iff the member is rc-wrapped. If it
            // ever goes red with `rc_pins` EMPTY again, do not re-assert the absence — check first
            // whether the caveat fold still reaches the carrier (the `absorbed` walk in
            // `v3_staged_registry_parses_and_covers` above is where that is measured).
            let has_rc: bool = !rc_pins.is_empty();
            assert_eq!(
                has_rc, !rc_exempt,
                "{key}: the dsl rc pins are present iff the member is the rc-wrapped cohort \
                 (rc_exempt={rc_exempt}); found {rc_pins:?}"
            );
            if has_rc {
                let mut got = rc_pins.clone();
                got.sort_by_key(|(_, pi)| *pi);
                let lo = got[0].1;
                assert_eq!(
                    got,
                    (0..4).map(|k| (rc_col + k, lo + k)).collect::<Vec<_>>(),
                    "{key}: the four rc pins must bind columns {rc_col}..{}+4 to CONTIGUOUS tail \
                     PI slots — that contiguity is exactly what \
                     `ivc_turn_chain::carrier_claim_pins_admitted` requires of the fold's claim \
                     slice",
                    rc_col
                );
            }
            // The member's PRE-rc PI count — what every per-effect branch below pins. The rc tail
            // SLOTS are still allocated (`piCount` is invariant under the subtraction); only their
            // pins are gone.
            let base_pi_count = d.public_input_count - if rc_exempt { 0 } else { 4 };
            // THE RECORD-FORCING PIN (the deployment-soundness close, `EffectVmEmitRotationV3
            // .rotateV3WithRecordPin`): cellSeal/cellUnseal/cellDestroy AND receiptArchive force the
            // AFTER block's lifecycle limb (col `after_base + B_LIFECYCLE`) — the deployed apply moves
            // the cell lifecycle (Sealed/Live/Destroyed/Archived); setPermissions/setVK AND the
            // refusal audit write force the AFTER record-digest / authority-digest limb (col
            // `after_base + B_AUTHORITY_DIGEST`) — the refusal audit lands in `fields_root`, which the
            // r23 authority digest folds. Each carries a FIFTH last-row PI pin to slot 38, so the
            // committed write is FORCED.
            use crate::effect_vm::trace_rotated::{B_AUTHORITY_DIGEST, B_LIFECYCLE};
            let record_digest_pin_member = matches!(
                key,
                "setPermsVmDescriptor2R24"
                    | "setVKVmDescriptor2R24"
                    | "refusalVmDescriptor2R24"
                    // makeSovereign keeps the record pin on `B_RECORD_DIGEST` as belt-and-suspenders
                    // for the opaque authority residue (Lean `makeSovereignV3`, the mode gate is the
                    // primary soundness; PI 38 welds the AFTER authority-digest limb).
                    | "makeSovereignVmDescriptor2R24"
            );
            let lifecycle_record_pin_member = record_digest_pin_member
                || matches!(
                    key,
                    "cellSealVmDescriptor2R24"
                        | "cellUnsealVmDescriptor2R24"
                        | "cellDestroyVmDescriptor2R24"
                        | "receiptArchiveVmDescriptor2R24"
                );
            // The createCell / factory / spawn ACCOUNTS-SET grow-gate family: the fifth pin welds
            // the new-cell key (param0) to PI[46], and the two cells_root map-ops force the
            // accounts set-insert on limb 0 (`EffectVmEmitRotationV3.{createCellV3,factoryV3,
            // spawnV3}`).
            let new_cell_key_pin_member = matches!(
                key,
                "createCellVmDescriptor2R24" | "factoryVmDescriptor2R24" | "spawnVmDescriptor2R24"
            );
            if key == "noteSpendVmDescriptor2R24" {
                assert_eq!(
                    base_pi_count, 47,
                    "noteSpend: rotated ROT_PI_COUNT-PI + the appended nullifier slot"
                );
                assert_eq!(
                    nullifier_pins,
                    vec![(PARAM_BASE + param::NULLIFIER, pi_base + 4)],
                    "noteSpend: the fifth pin welds the folded nullifier (param0) to PI[46]"
                );
            } else if key == "noteCreateVmDescriptor2R24" {
                // The COMMITMENTS-SET grow-gate (the `commitments_root` flag-day): the fifth pin
                // welds the published note commitment (param0) to PI[46], and the
                // `commitmentsInsertOp` map-op forces the commitment set-insert on limb 27
                // (`EffectVmEmitRotationV3.noteCreateV3`).
                assert_eq!(
                    base_pi_count, 47,
                    "noteCreate: rotated ROT_PI_COUNT-PI + the appended commitment slot"
                );
                assert_eq!(
                    nullifier_pins,
                    vec![(PARAM_BASE + param::NULLIFIER, pi_base + 4)],
                    "noteCreate: the fifth pin welds the published commitment (param0) to PI[46]"
                );
            } else if key == "factoryVmDescriptor2R24" {
                // STEP-3 factory carriers (`factoryV3Carriers = withAfterOctetPins (withAfterOctetPins
                // factoryV3 B_CHILD_VK_OCTET) B_CONTRACT_HASH_OCTET`): the new-cell-key grow-gate pin
                // (param1 CHILD_VK_DERIVED → PI[46]) PLUS the 16 committed carrier-octet pins — the
                // AFTER-block child_vk8 octet (limbs 88..=95 → PI[47..54]) then the contract_hash8
                // octet (limbs 96..=103 → PI[55..62]), last-row, the v12 big-bang exposure the
                // factory/hatchery fold tooths bind.
                use crate::effect_vm::trace_rotated::{B_CHILD_VK_OCTET, B_CONTRACT_HASH_OCTET};
                assert_eq!(
                    base_pi_count, 63,
                    "factory: rotated ROT_PI_COUNT-PI + the new-cell-key slot + the 16 carrier-octet pins"
                );
                let mut expected = vec![(PARAM_BASE + param::CHILD_VK_DERIVED, pi_base + 4)];
                for i in 0..8 {
                    expected.push((after_base + B_CHILD_VK_OCTET + i, pi_base + 5 + i));
                }
                for i in 0..8 {
                    expected.push((after_base + B_CONTRACT_HASH_OCTET + i, pi_base + 13 + i));
                }
                assert_eq!(
                    nullifier_pins, expected,
                    "factory: the grow-gate key pin (PI[46]) + the child_vk8 (PI[47..54]) + \
                     contract_hash8 (PI[55..62]) committed-octet pins"
                );
            } else if new_cell_key_pin_member {
                assert_eq!(
                    base_pi_count, 47,
                    "{key}: rotated ROT_PI_COUNT-PI + the appended new-cell-key slot"
                );
                // createCell/spawn key on param0 (the new-cell id).
                let key_col = PARAM_BASE;
                assert_eq!(
                    nullifier_pins,
                    vec![(key_col, pi_base + 4)],
                    "{key}: the fifth pin welds the new-cell key to PI[46] (the accounts-set \
                     grow-gate)"
                );
            } else if record_digest_pin_member {
                // H1: the record-digest movers (setPerms/setVK/makeSovereign/refusal) pin ALL 8 faithful
                // authority limbs (`withRecordPin8Headroom2`): limb-0 (`B_AUTHORITY_DIGEST`) → PI[46] +
                // the 7 headroom limbs (AFTER offsets 12..18) → PI[47..53], so a 31-bit-colliding
                // wide-open authority forged into ANY limb is UNSAT (the GENTIAN close for movers).
                assert_eq!(
                    base_pi_count, 54,
                    "{key}: rotated ROT_PI_COUNT-PI + the 8 authority record-pins \
                     (`ROT_PI_COUNT ..= ROT_PI_COUNT + 7`; 46..53 pre-compaction)"
                );
                let mut expected = vec![(after_base + B_AUTHORITY_DIGEST, pi_base + 4)];
                for i in 0..7 {
                    expected.push((after_base + 12 + i, pi_base + 5 + i));
                }
                assert_eq!(
                    nullifier_pins, expected,
                    "{key}: the 8 record-pins weld the AFTER authority limbs (24, 12..18) to PI[46..53]"
                );
            } else if lifecycle_record_pin_member {
                assert_eq!(
                    base_pi_count, 47,
                    "{key}: rotated ROT_PI_COUNT-PI + the appended record-forcing slot"
                );
                assert_eq!(
                    nullifier_pins,
                    vec![(after_base + B_LIFECYCLE, pi_base + 4)],
                    "{key}: the fifth pin welds the AFTER block's correctly-written lifecycle \
                     limb to PI[46] (the deployment-soundness gate)"
                );
            } else if key == "transferFeeVmDescriptor2R24" {
                // THE FEE-IN-PROOF transfer: the fifth pin welds the after-block RESERVED limb (col
                // `STATE_AFTER_BASE + state::RESERVED`, the fee carrier) to PI[46], the fee debited
                // INSIDE the proven transition (the bal-lo gate forces `after = before − amount − fee`).
                use crate::effect_vm::columns::{STATE_AFTER_BASE, state};
                assert_eq!(
                    base_pi_count, 47,
                    "transferFee: rotated ROT_PI_COUNT-PI + the appended fee slot"
                );
                assert_eq!(
                    nullifier_pins,
                    vec![(STATE_AFTER_BASE + state::RESERVED, pi_base + 4)],
                    "transferFee: the fifth pin welds the after-block RESERVED fee limb (col 89) to PI[46]"
                );
            } else if key == "setFieldDynVmDescriptor2R24" {
                // THE DYNAMIC setField fields-root weld (WAVE 3): the fifth pin welds the AFTER
                // block's committed `fields_root` sub-limb to PI[46], so a forged post-`fields_root`
                // is UNSAT in-circuit (Lean `setFieldDynForcedV3`). The column is the Lean's
                // `afterFieldsRootCol setFieldDynV1Face.traceWidth` = face + B_SPAN + B_FIELDS_ROOT.
                //
                // ⚑ NOW DERIVED, AND THE ROT HISTORY IS THE EVIDENCE FOR THE DERIVATION. This was a
                // fully hand-pinned literal and it rotted TWICE, both times by exactly `ΔB_SPAN`:
                //   439 → 451 when the revoked-root flag day grew `B_SPAN` 227 → 239 (+12)
                //   451 → 459 when the nine-lane flag day grew `B_SPAN` 239 → 247 (+8)
                // Two independent confirmations that the emitted column IS
                // `face + B_SPAN + B_FIELDS_ROOT`, so only the FACE stays a literal.
                //
                // The face is where Rust and Lean genuinely disagree, and that is why the whole
                // thing was hand-pinned before: Rust's `EFFECT_VM_WIDTH` is 188, the Lean
                // `setFieldDynV1Face.traceWidth` is 176 (= 459 − 247 − 36), a 12-column divergence
                // with no Rust-side source to derive from. Writing `V1_WIDTH + B_SPAN +
                // B_FIELDS_ROOT` would give 471 and be a FABRICATED identity — so the face is
                // named as its own constant, with the divergence recorded, and the two moving
                // terms are read from the emitted layout. A `B_SPAN` change now updates this
                // automatically; a FACE change still goes red here, which is the part that
                // genuinely needs a human.
                const SETFIELD_DYN_LEAN_V1FACE_WIDTH: usize = 176;
                const SETFIELD_DYN_AFTER_FIELDS_ROOT_COL: usize = SETFIELD_DYN_LEAN_V1FACE_WIDTH
                    + crate::effect_vm::trace_rotated::B_SPAN
                    + crate::effect_vm::trace_rotated::B_FIELDS_ROOT;
                assert_eq!(
                    base_pi_count, 47,
                    "setFieldDyn: rotated ROT_PI_COUNT-PI + the appended fields-root weld slot"
                );
                assert_eq!(
                    nullifier_pins,
                    vec![(SETFIELD_DYN_AFTER_FIELDS_ROOT_COL, pi_base + 4)],
                    "setFieldDyn: the fifth pin welds the AFTER fields_root weld col \
                     (Lean face 176 + B_SPAN + B_FIELDS_ROOT) to PI[46]"
                );
            } else if key == "mintVmDescriptor2R24" {
                // ⚑ THE SUPPLY-MINT HASH "WELD" WAS NOT A WELD, and 2026-07-31's subtraction said so.
                //
                // This branch used to assert `nullifier_pins == [(PARAM_BASE + param::MINT_HASH,
                // pi_base + 4)]` with the message "the fifth pin welds the published mint-hash
                // (param0, col 68) to PI[46] … the minted supply anchor is a committed public input,
                // NOT FREE." The last four words were exactly wrong. Col 68 appears in no gate, no
                // lookup, no transition, no hash site and no range tooth of this member, so the pin
                // was `local[68] == pi[46]` with the prover choosing both sides — and
                // `last_row_anchor_forge` MEASURED that end to end: an arbitrary mint identity
                // proved and verified at the AIR, and only the executor's reconstruction (it
                // recomputes the identity from the turn's own carrier witness) stopped it.
                // `dropUnforcedPins` removed the pin; `piCount` is untouched, so PI 46 is still
                // published, still filled by the executor, still read by the fold. What is gone is
                // the descriptor claiming the AIR ties that slot to a column.
                //
                // The base PI count therefore does NOT move: the slot survives, only its pin does
                // not. Asserting the ABSENCE is falsifiable — it goes red if a mint pin returns,
                // which is what a REAL supply-anchor weld (one whose column something else reads)
                // would look like, and at that point this should become a presence assertion again.
                assert_eq!(
                    base_pi_count, 47,
                    "mint: rotated ROT_PI_COUNT-PI + the appended mint-hash SLOT (the slot survives the \
                     unforced-pin subtraction; only its pin was dropped)"
                );
                assert_eq!(
                    nullifier_pins,
                    vec![],
                    "mint: the mint-hash slot must be UNPINNED — col {} is read by nothing, so a \
                     pin on it published a prover-chosen mint identity. If a pin is back, check \
                     whether the column became FORCED before restoring the old claim.",
                    PARAM_BASE + param::MINT_HASH
                );
            } else if key == "settleEscrowSatVmDescriptor2R24"
                || key == "dischargeSatVmDescriptor2R24"
                || key == "vaultSatVmDescriptor2R24"
            {
                // THE THREE WELDED CAPACITY-SATISFACTION descriptors (VK-EPOCH §6 BLOCKER 1 + G5
                // 18/19, STAGED): the fifth pin welds the capacity SELECTOR column (param2, col 70) to
                // PI[46] on the first row, so a verifier that knows the cell declares the capacity (the
                // deployed COVERAGE carrier `CapacityCarrier`) can FORCE the selector on; the
                // selector-gated satisfaction gates over the rotated FIELD columns then force the
                // in-AIR arm — settleEscrow's Deposited→Consumed (`SETTLE_ESCROW`), discharge's
                // cursor/total/due + the G5 free-param binds (`DISCHARGE_OBLIGATION`), vault's
                // no-dilution `Ta·m ≤ Sa·d` (`VAULT_DEPOSIT`). All three share the SAME selector pin
                // (col 70 → PI[46]) and 47 PIs; they differ only in the satisfaction-gate field columns
                // (accounted in the graduated-width check above). NO live routing — staged beside the
                // cohort; the descriptors a flippable capacity weld commits a VK for. Refinements in
                // `metatheory/Dregg2/Deos/{SettleEscrowSat,DischargeSat,VaultSat}Descriptor.lean`.
                use crate::effect_vm::columns::PARAM_BASE;
                assert_eq!(
                    base_pi_count, 47,
                    "{key}: rotated ROT_PI_COUNT-PI + the appended capacity-selector slot"
                );
                assert_eq!(
                    nullifier_pins,
                    vec![(PARAM_BASE + 2, pi_base + 4)],
                    "{key}: the fifth pin welds the capacity selector (param2, col 70) to PI[46]"
                );
            } else if is_heap_write {
                // heapWrite: the base carries no v1 PIs, so the rotated descriptor publishes
                // EXACTLY the four commit pins (indices 0..=3) — no fifth pin. The new heap_root is
                // forced by the genuine sorted-Merkle SPLICE `.write` map_op (PHASE-E) + the address
                // chip lookup that gives it the sorted KEY — not a published param.
                assert_eq!(
                    d.public_input_count, 4,
                    "heapWrite: the four rotated commit pins, no v1 PI prefix"
                );
                assert!(
                    nullifier_pins.is_empty(),
                    "heapWrite: carries no fifth pin (the splice map_op rides the map_ops table)"
                );
            } else if key == "customVmDescriptor2R24" {
                // G2 custom-leg PI exposure (`EffectVmEmitRotationV3.customPiExposure`) — the
                // PROOF-BIND FLAG-DAY ROTATION (blocker #2, 4 → 8 commitment felts): customV3
                // RESERVES 16 published slots PAST the rotated ROT_PI_COUNT-PI vector —
                // `custom_proof_commitment` limbs 0..8 at PI[46..53] and `custom_program_vk_hash`
                // limbs 0..8 at PI[`ROT_PI_COUNT + 8` ..) — so custom carries `ROT_PI_COUNT + 16`
                // PIs. (That was PI[54..61] and 62 = 46 + 16 before the 2026-08-07 seven-slot
                // compaction; `docs/PI-DISPOSITION.md` §6.)
                //
                // ⚑ 2026-07-31: FOURTEEN OF THE SIXTEEN PINS ARE GONE, and this assertion listed
                // all sixteen. It read them as "16 fold-binding pins weld …", and the word `weld`
                // was the error: a `.piBinding` is a weld only when something ELSE forces the
                // column. Nothing does here. A `proof_bind` has NO row denotation — the deployed
                // `Ir2Air::eval` `continue`s on it without emitting a bus interaction, and Lean's
                // `holdsAt` is `trivial` — so every one of the sixteen columns was prover-chosen on
                // both sides. `require_no_unbacked_proof_bind` has always said this in prose ("the
                // declaration is NOT an in-AIR check … the ONLY thing that makes the published
                // claim mean anything is the per-turn fold"); the subtraction made the descriptor
                // stop contradicting it.
                //
                // Two pins survived, and ONLY because `UnforcedPiPins.forcedCols` counts a
                // `proof_bind`'s `commit`/`vk` references — a DECLARATION, not a constraint. They
                // are as prover-chosen as the fourteen; that over-count is measured directly by
                // `circuit/tests/unforced_pi_pin_census.rs::proof_bind_is_the_only_reader_of_the_custom_exposure_columns`.
                //
                // NOTHING GOT WEAKER. `piCount` is invariant under the subtraction, so all 16 slots
                // are still published and the FOLD — which is where the binding has always lived —
                // reads exactly what it read before. What is gone is the claim.
                //
                // ⚑ 2026-08-05: ALL SIXTEEN PINS ARE BACK, AND THE OVER-COUNT IS EXACTLY WHY —
                // read that as an arithmetic consequence, not as a repair. The `ProofBind`
                // widening (schema 2 → 3) made `commit`/`vk` LANE VECTORS, so the declaration now
                // REFERENCES all sixteen exposure columns where it referenced two; `forcedCols`
                // counts references; the subtraction therefore keeps sixteen. ⚠ NOT ONE OF THEM
                // BECAME FORCED. A `proof_bind` still has no row denotation, `Ir2Air::eval` still
                // `continue`s on it, `holdsAt` is still `trivial`, and all sixteen columns are
                // still prover-chosen on both sides. The census test named above is what measures
                // that, and it is unchanged. The count moved 2 → 16 because the declaration got
                // wider, and calling any of the sixteen a weld would be the 2026-07-31 error
                // recommitted at eight times the width.
                assert_eq!(
                    base_pi_count, 62,
                    "custom: rotated ROT_PI_COUNT-PI + the 16 RESERVED custom exposure slots \
                     (`ROT_PI_COUNT ..= ROT_PI_COUNT + 15`; 46..61 pre-compaction)."
                );
                use crate::descriptor_ir2::ProofBindSpec;
                use crate::lean_descriptor_air::LeanExpr;
                let declared = d.constraints.iter().find_map(|c| match c {
                    VmConstraint2::ProofBind(ProofBindSpec { commit, vk, .. }) => {
                        Some((commit.clone(), vk.clone()))
                    }
                    _ => None,
                });
                // The surviving pins are DERIVED from the bind's own lane vectors rather than
                // transcribed: the claim is "exactly the columns the `proof_bind` names, in
                // published order", and the lanes are NOT contiguous (the wide-key layout puts
                // lanes 4..7 far above the first four), so a hand-written column list would be a
                // second copy of a layout that already moved once today.
                let expected: Vec<(usize, usize)> = {
                    let (commit, vk) = declared.clone().expect(
                        "custom: the member must carry a `proof_bind` — its lane vectors are what \
                         the surviving exposure pins are derived from",
                    );
                    let col_of = |e: &LeanExpr| match e {
                        LeanExpr::Var(c) => *c,
                        other => {
                            panic!("custom: `proof_bind` lane is not a column read: {other:?}")
                        }
                    };
                    commit
                        .iter()
                        .enumerate()
                        .map(|(i, e)| (col_of(e), pi_base + 4 + i))
                        .chain(
                            vk.iter()
                                .enumerate()
                                .map(|(i, e)| (col_of(e), pi_base + 12 + i)),
                        )
                        .collect()
                };
                assert_eq!(
                    nullifier_pins, expected,
                    "custom: EXACTLY the sixteen exposure pins survive, and they are EXACTLY the \
                     sixteen columns this member's eight-lane `proof_bind` declares — commit lanes \
                     at PI[46..53], program-VK lanes at PI[54..61]. If a pin survives whose column \
                     the bind does NOT name, something else started forcing it and that is a \
                     different claim; if one disappears, the declaration narrowed."
                );
                // …and the sixteen that survived are exactly the `proof_bind`'s own columns, which
                // is the only structural tie between the published exposure and the op the fold
                // keys on. Asserted, not assumed: it is what `custom_commit_version` classifies by.
                {
                    // ⚑ THE ANCHOR LANES, kept verbatim: lane 0 of each vector is the column the
                    // rotated layout names and `custom_commit_version` classifies by. The two facts
                    // ADDED are what the widening bought and what the narrow shape could not have
                    // said: the vectors are at the deployed eight-lane width, and their eight lanes
                    // are eight DISTINCT columns, so the bind ties an eight-felt commitment rather
                    // than one limb repeated.
                    let (commit, vk) = declared.expect(
                        "custom: the member must carry a `proof_bind` — it is the only structural \
                         tie between the published exposure and the op the fold keys on",
                    );
                    assert_eq!(
                        (commit.first(), vk.first()),
                        (
                            Some(&LeanExpr::Var(PARAM_BASE + param::CUSTOM_PROOF_COMMIT_BASE)),
                            Some(&LeanExpr::Var(PARAM_BASE + param::CUSTOM_VK_HASH_BASE))
                        ),
                        "custom: the `proof_bind`'s lane 0 must be the anchor column the rotated \
                         layout names — that correspondence is all that connects the exposure to \
                         the fold's re-proven sub-proof leaf"
                    );
                    assert_eq!(
                        (commit.len(), vk.len()),
                        (
                            crate::descriptor_ir2::PROOF_BIND_MIN_LANES,
                            crate::descriptor_ir2::PROOF_BIND_MIN_LANES
                        ),
                        "custom: both lane vectors must be at the deployed eight-felt width; a \
                         narrower bind ties a prefix of the objects it names"
                    );
                    for (what, lanes) in [("commit", &commit), ("vk", &vk)] {
                        let mut seen: Vec<&LeanExpr> = Vec::new();
                        for lane in lanes.iter() {
                            assert!(
                                !seen.contains(&lane),
                                "custom: `proof_bind`'s {what} repeats a lane — eight slots holding \
                                 fewer than eight distinct columns is a narrow bind wearing a wide \
                                 shape"
                            );
                            seen.push(lane);
                        }
                    }
                }
                // The versioned boundary classifies THIS committed member as live v3 (and the
                // retired commitment4/VK4 and commitment8/VK4 layouts as typed refusals).
                assert_eq!(
                    custom_commit_version(&d),
                    Ok(CUSTOM_COMMIT_VERSION),
                    "the committed custom member must classify as faithful carrier v3"
                );
            } else if key.starts_with("setFieldVmDescriptor2-") {
                // THE VALUE8 EPOCH: the 8 static-slot setField members publish the written slot's
                // freed completion lanes (the high bits of the 32-byte value) as PIs
                // 46..=46+SETFIELD_VALUE8_PI_LEN-1 (46..=53 at the nine-lane geometry: lanes 1..=7
                // in the contiguous window plus the ninth lane at `176 + slot`), ahead of the rc tail. Before the flip these were bare 46-PI members and the freeze
                // made an honest 32-byte write unprovable. (`setFieldDynVmDescriptor2R24` is a
                // different member and stays bare — it carries no completion weld.)
                assert_eq!(
                    base_pi_count,
                    46 + SETFIELD_VALUE8_PI_LEN,
                    "{key}: the deployed setField member carries the rotated ROT_PI_COUNT-PI + the VALUE8 \
                     completion pins"
                );
                // The extras are EXACTLY the value8 completion block: contiguous PI slots
                // 46..=53 over 8 distinct columns. (They are `.last`-row pins, unlike the
                // note-spend/record fifth pin, but this walk collects by pi_index.)
                let mut extra: Vec<(usize, usize)> = nullifier_pins.clone();
                extra.sort_by_key(|(_, pi)| *pi);
                assert_eq!(
                    extra.len(),
                    SETFIELD_VALUE8_PI_LEN,
                    "{key}: exactly the 7 VALUE8 completion pins ride past the rotated prefix"
                );
                for (k, (_, pi)) in extra.iter().enumerate() {
                    assert_eq!(
                        *pi,
                        SETFIELD_VALUE8_PI_BASE + k,
                        "{key}: the value8 block is contiguous at PIs 46..=52"
                    );
                }
                let cols: std::collections::BTreeSet<usize> =
                    extra.iter().map(|(c, _)| *c).collect();
                assert_eq!(
                    cols.len(),
                    SETFIELD_VALUE8_PI_LEN,
                    "{key}: the 7 value8 pins name 7 DISTINCT completion columns"
                );
            } else {
                assert_eq!(
                    base_pi_count, 46,
                    "{key}: non-record-pin cohort carries the rotated ROT_PI_COUNT-PI"
                );
                assert!(
                    nullifier_pins.is_empty(),
                    "{key}: only note-spend / the 7 record-pin effects carry a fifth pin"
                );
            }
        }
        assert_eq!(
            n, 60,
            "expected the 36-member rotated cohort (28 v2-graduated + 8 widened) + the 6 fan-out \
             cap-open members (delegate/introduce/grantCap/revoke/refreshDelegation/revokeCapability \
             — each *CapOpenVmDescriptor2R24) + the 2 LIVE effect-general legs \
             (transfer/attenuate *CapOpenEffVmDescriptor2R24) + the TURN-IDENTITY weld \
             (transferCapOpenTBVmDescriptor2R24, CapOpenTurnPins — the cap-open + 2 turn-identity \
             columns + 3 turn-identity PI pins welding src/actor/dst to the published turn) + the \
             FEE-IN-PROOF transfer (transferFeeVmDescriptor2R24 — the fee debited in-proof, 47 PIs) \
             + THE WRITE-BEARING TAIL (`v3RegistryHeap` 45..52): heapWriteVmDescriptor2R24 (the \
             Class-A heap-root recompute, `Rfix 56`) + the SIX write-forcing cap-open wrappers \
             (delegate/introduce/delegateAtten/revokeDelegation/revokeCapability/refreshDelegation \
             *WriteCapOpenVmDescriptor2R24 — the apex's `Rfix 1/10/11/14/55` re-pointed plus the \
             revokeCapability cap-tree REMOVE route-forge close, guarantee A: the cap-tree / \
             deleg-tree WRITE forced into the commitment) + the SPAWN cap-handoff close (the \
             authority-only spawnCapOpenVmDescriptor2R24 + the WRITE-forcing \
             spawnWriteCapOpenVmDescriptor2R24, `Rfix 19` re-pointed — the parent→child CAPABILITY \
             HANDOFF cap-tree INSERT forced ALONGSIDE the accounts grow-gate; both carry spawn's \
             extra birth new-cell-key PI so 47 PIs) + the EXERCISE cap-open close (the \
             exerciseCapOpenVmDescriptor2R24 — `Rfix 16` re-pointed; the FROZEN exercise base + the \
             EFF_EXERCISE depth-16 cap-membership crown forcing the exercise hold-gate \
             `exerciseGuard`'s `confersEdgeTo target` membership in-circuit — the LAST named cap-open \
             residual CLOSED) + the DEDICATED SUPPLY-MINT (supplyMintVmDescriptor2R24, SUPPLY-MODEL.md \
             Stage 2b — the turn-layer `Effect::Mint` on its OWN selector `sel::MINT = 14`; the SAME \
             proven credit/tick/freeze body as mintVmDescriptor2R24 save the appended selectorGate \
             operand, so it proves + self-verifies under a dedicated selector, not by riding \
             BridgeMint's). \
             The Signature-pinned capOpenAttenuateV3/transferCapOpenV3 were DELETED (Stage D). \
             + the THREE WELDED CAPACITY-SATISFACTION descriptors (VK-EPOCH §6 BLOCKER 1 + G5 18/19 \
             — the staged welded EffectVmDescriptor2s carrying the selector-gated satisfaction gates \
             over the rotated FIELD columns + the shared selector PI pin (col 70 → PI 46), 47 PIs each; \
             NO live routing, NO VK committed): settleEscrowSatVmDescriptor2R24 (tag 17, \
             Deposited→Consumed, no extra columns) + dischargeSatVmDescriptor2R24 (tag 18, the \
             cursor/total/due + G5 free-param binds) + vaultSatVmDescriptor2R24 (tag 19, the \
             no-dilution Ta·m ≤ Sa·d gates) — the descriptors a flippable capacity weld commits VKs for."
        );
    }

    /// **THE WIDE REGISTRY drift + coverage pin (STAGED-ADDITIVE slice 2).** The 57-member faithful
    /// 8-felt wide registry TSV is fingerprint-stable (the Lean `EmitWideRegistryProbe.lean` is the
    /// byte source), parses member-for-member, and is name-stable against the live 1-felt registry
    /// (the flip is a name-stable repoint). The transfer member (row 0) is pinned ABSOLUTELY —
    /// width by `WIDE_MEMBER_GEOMETRY`, PI count by the row-0 pin — replacing a relative pin against
    /// the single-line `WIDE_TRANSFER_STAGED_TSV` fork DELETED 2026-07-31.
    /// ADDITIVE: pins the wide path WITHOUT touching the live `V3_STAGED_REGISTRY_*`.
    #[test]
    fn wide_registry_parses_and_is_name_stable() {
        use crate::descriptor_ir2::parse_vm_descriptor2;

        // Every wide member parses; the wide geometry is the host + the carrier block MINUS the S2
        // and E1 dead-column kill-sets, plus 16 PIs — pinned PER MEMBER by `WIDE_MEMBER_GEOMETRY`
        // below. The keys are NAME-STABLE against the live 1-felt registry, member-for-member (the
        // flip repoint does not rename).
        let live_keys: Vec<&str> = V3_STAGED_REGISTRY_TSV
            .lines()
            .filter(|l| !l.is_empty())
            .map(|l| l.split('\t').next().expect("live key"))
            // The THREE STAGED capacity-satisfaction-weld members (VK-EPOCH §6 BLOCKER 1 + G5 18/19 —
            // settleEscrow/discharge/vault), appended LAST to the rotated registry; their WIDE+umem
            // mirrors are a separate named step (the wide cohort is the deployable host set). Excluded
            // from the member-for-member wide-cover parity until those welds land — they carry no live
            // routing, so the wide registry has 57 members to the live registry's 60.
            .filter(|k| {
                *k != "settleEscrowSatVmDescriptor2R24"
                    && *k != "dischargeSatVmDescriptor2R24"
                    && *k != "vaultSatVmDescriptor2R24"
            })
            .collect();

        // **THE PER-MEMBER WIDE GEOMETRY PIN — RE-PINNED FOR THE S2 + E1 COMPACTIONS.**
        // `(registry key, committed trace_width)` in registry order, READ OFF THE EMITTED
        // `rotation-wide-registry-staged.tsv` (the Lean `EmitWideRegistryProbe.lean` is the byte
        // source), never hand-derived.
        //
        // This USED to be a whitelist of 15 legitimate widths (2607 / 2623 / … / 3127 = the
        // pre-compaction `host + WIDE_CARRIER_APPENDIX (960)` + gentian geometry). Two flag-days
        // moved every member and neither re-pinned this tooth, so it was asserting a geometry no
        // member had any more:
        //   * the S2 FLAG-DAY REGEN (`4dd3273bd2`) dropped the dead post-S2 columns — −960 per
        //     member (transfer 2664 → 1704);
        //   * the E1 per-member dead-column compaction (`bd21266e6b`, kill-set narrowed to the
        //     pre-gentian `e1Ceiling` by `3ebf42e25f`) dropped each member's OWN kill-set
        //     (transfer 1704 → 1610 = 94 columns; see `e1_compact_generated::E1_COMPACT_TABLE`).
        //   * ⚑ THE NINE-LANE EPOCH (`NUM_PRE_LIMBS` 178 → 184, `B_SPAN` 239 → 247, the wide chain
        //     60 → 62 carriers): +44 columns on 56 of the 57 members (transfer 1610 → 1654), read
        //     back off the emitted TSV on 2026-07-31. The ONE member that did not move by +44 is
        //     `transferCapOpenTB`, at +42 — it is now byte-for-byte the width of the non-TB
        //     `transferCapOpenEff`, because `CapOpenTurnPins.effCapOpenV3TB` no longer appends the
        //     two turn-identity COLUMNS (see the note on that member in the cap-open branch of
        //     `v3_staged_registry_parses_and_covers`). The per-member shape of this pin is exactly
        //     what made that one member's divergence visible instead of averaging it away.
        //
        // It is re-pinned PER MEMBER rather than as a fresh whitelist because E1's kill-set is a
        // per-member fact: a shared width whitelist lets one member silently drift onto another
        // member's legitimate width (26 of the 57 now sit at 1601), which is exactly the
        // unintended-geometry-drift this tooth exists to catch. The pin below fails on ANY member
        // whose carrier block, refuse weld, or kill-set moved — a regen that legitimately moves a
        // member has to move its row here, deliberately and visibly. The RETIRED v1 (912-appendix)
        // widths stay structurally refused by `wide_carrier_geometry_version`.
        //
        // AND THAT IS EXACTLY WHAT HAPPENED ON 2026-07-26, one member at a time rather than all 57:
        // the `siteHeapLeaf` arity-2 leaf-vestige flag-day (Lean `a0687f268`, bytes `c5f50424a`)
        // dropped one graduated constraint from heapWrite — 7 chip-lane columns, plus an EIGHTH as
        // the now-unbound carrier column fell into the E1 kill-set (`(104,188) → (103,188)`). So
        // `heapWriteVmDescriptor2R24` moved 1963 → 1955 HERE, alone; every other row is byte-
        // unchanged, which is the discrimination a shared whitelist could not have given. Its two
        // sibling registries moved with it (narrow 1633 → 1626, umem-welded 1970 → 1962) but neither
        // is pinned by a literal: the welded member is checked as `bare + 7` by
        // `wide_umem_weld_registry_parity_and_no_narrowing`, and the narrow one rides the derived
        // `HEAP_WRITE_HOST_WIDTH` / `HEAP_WRITE_READ_BASE`.
        // ⚑ FLAG DAY 2026-07-31 (the rc FOLD), and the SPLIT in the deltas is the interesting
        // part. Every member gained +16 from the geometry (`C_SPAN` 43 → 45 for the two carriers
        // the rc extension needs, plus 2 new chip sites × 7 graduated lane columns). TWENTY
        // members gained +20: the cap-open / write / heapWrite / supplyMint rows, whose E1
        // kill-set used to swallow the four DEAD rc carrier columns. They are no longer dead — the
        // caveat fold reads them — so E1 keeps them and the member is 4 columns wider. That the
        // split falls exactly on "which members E1 had reached" is the cross-check that the fold
        // reached every member's carrier, not just the ones whose pins came back (heapWrite and
        // supplyMint are rc-EXEMPT: no pins, but the columns are live all the same).
        //
        // ⚑ FLAG DAY 2026-07-31 (the FIELDS-CANONICITY emit, `Emit/FieldsCanonicity9Emit.lean`):
        // **+112 on ALL FIFTY-SEVEN members, with a delta spread of ZERO** — and the uniformity is
        // the whole check, so it is DERIVED here rather than transcribed off the TSV:
        //
        //   APPENDIX_SPAN  539 → 651   (+CANON9_SPAN = 2 blocks × 8 slots × CANON9_PER_SLOT = 112)
        //   ROT_WIDTH      = EFFECT_VM_WIDTH + APPENDIX_SPAN                        → +112
        //   GRAD_ROT_WIDTH = ROT_WIDTH + 7·N_ROT_SITES                              → +112
        //
        // The middle step is the one that had to be checked rather than assumed: graduation
        // appends `7·N_ROT_SITES` lane columns, so a wrap that added a HASH SITE would multiply
        // its own growth by 7 and the spread would not be flat. `fieldsCanonical9At_hashSites`
        // proves it adds none (it is `traceWidth`-, `piCount`-, `tables`-, `hashSites`- and
        // `ranges`-invariant — it appends CONSTRAINTS into columns `rotateV3` had already
        // allocated), so the appendix growth passes through the graduation 1:1 and lands
        // unchanged on every member. Nothing below the region moved, so neither compaction's
        // geometry changed: S2's two carrier bands and each member's E1 kill-set are byte-
        // identical, and the region rides ABOVE both, which is why the deltas do not fan out the
        // way the rc FOLD's +16/+20 split did. Cross-check on the narrow side, where the same
        // arithmetic must hold with no compaction at all: `GRAD_ROT_WIDTH(1819) + REFUSE_AUX_SPAN
        // (45) = 1864`, the committed narrow `mint`/`revoke`/`setField-*` width (was 1752).
        // ⚑ FLAG DAY 2026-08-01 (the KEY NONET): **+22 on ALL FIFTY-SEVEN members, delta spread
        // ZERO** — and as with the fields-canonicity block above, the uniformity is the check.
        //
        // `76c3f7b9b` took the rotated pre-limb region 184 -> 187 (the owner key's ninth lane, the
        // one carrying the Ed25519 sign bit, plus the child_vk and contract_hash ninth lanes at
        // 184/185) and re-typed FIFTEEN Rust geometry pins to match — `CAP_OPEN_BASE` 1819 -> 1841,
        // `CAP_OPEN_WIDTH` 2148 -> 2170, the cap-WRITE narrow 2291 -> 2313 — but it did NOT
        // re-emit, and said so: "descriptors, registry TSVs, PROVENANCE.json and VKs are all still
        // at 184 and MUST be regenerated". They stayed at 184 for the rest of the day because the
        // emit could not run (`CapOpenEmit.lean` still forwarded carrier 61 into a lemma that had
        // moved to 62, so every emitter's import path was red). With the emit repaired, this is
        // that re-emit, and the numbers below are read off it.
        //
        // ⚑ THE NEW NUMBERS ARE RIGHT BECAUSE TWO INDEPENDENT READINGS AGREE, not because they are
        // what the emitter printed. Every failing producer test named its own width in the message,
        // and each is now the committed one: `revokeDelegationWriteCapOpen` "trace width 2190 < the
        // wide producer's 2212" -> 2212 here; `refreshDelegationWriteCapOpen` / `attenuateCapOpenEff`
        // 2197 -> 2219; `supplyMint` 1725 -> 1747; `heapWrite` "row 0 is 2153 wide" -> 2153. The
        // Rust producer was computing the 187 geometry all along; only the committed bytes were old.
        // On the narrow side the same delta lands on the constants `trace_rotated.rs` pins by
        // literal: `supplyMint` 1841 = `CAP_OPEN_BASE`, cap-open 2170 = `CAP_OPEN_WIDTH`, cap-WRITE
        // 2313 = `CAP_OPEN_WIDTH + CAP_OPEN_AFTER_SPINE_SPAN`.
        //
        // ⚠ The +22 is NOT decomposed into a formula here on purpose. Three new pre-limbs riding
        // two blocks and a 7-lane graduation is not 3, 6 or 21, and writing an arithmetic story
        // that happens to total 22 would be a guess wearing a derivation's clothes. What is
        // asserted is what was measured: a flat +22 on all 57, agreeing with an independently
        // re-typed Rust constant.
        const WIDE_MEMBER_GEOMETRY: [(&str, usize); 57] = [
            ("transferVmDescriptor2R24", 1804),
            ("burnVmDescriptor2R24", 1800),
            ("mintVmDescriptor2R24", 1795),
            ("noteSpendVmDescriptor2R24", 2086),
            ("noteCreateVmDescriptor2R24", 2086),
            ("cellSealVmDescriptor2R24", 1795),
            ("cellDestroyVmDescriptor2R24", 1795),
            ("refusalVmDescriptor2R24", 2303),
            ("setPermsVmDescriptor2R24", 1795),
            ("setVKVmDescriptor2R24", 1795),
            ("exerciseVmDescriptor2R24", 1795),
            ("pipelinedSendVmDescriptor2R24", 1795),
            ("refreshVmDescriptor2R24", 1795),
            ("incrementNonceVmDescriptor2R24", 1795),
            ("revokeVmDescriptor2R24", 1795),
            ("introduceVmDescriptor2R24", 1795),
            ("attenuateVmDescriptor2R24", 1795),
            ("revokeCapabilityVmDescriptor2R24", 1795),
            ("customVmDescriptor2R24", 1771),
            ("setFieldDynVmDescriptor2R24", 1763),
            ("grantCapVmDescriptor2R24", 1795),
            ("makeSovereignVmDescriptor2R24", 1831),
            ("createCellVmDescriptor2R24", 2086),
            ("factoryVmDescriptor2R24", 1795),
            ("spawnVmDescriptor2R24", 1795),
            ("receiptArchiveVmDescriptor2R24", 1795),
            ("cellUnsealVmDescriptor2R24", 1795),
            ("emitEventVmDescriptor2R24", 1795),
            ("setFieldVmDescriptor2-0R24", 1795),
            ("setFieldVmDescriptor2-1R24", 1795),
            ("setFieldVmDescriptor2-2R24", 1795),
            ("setFieldVmDescriptor2-3R24", 1795),
            ("setFieldVmDescriptor2-4R24", 1795),
            ("setFieldVmDescriptor2-5R24", 1795),
            ("setFieldVmDescriptor2-6R24", 1795),
            ("setFieldVmDescriptor2-7R24", 1795),
            ("delegateCapOpenVmDescriptor2R24", 2076),
            ("introduceCapOpenVmDescriptor2R24", 2076),
            ("grantCapCapOpenVmDescriptor2R24", 2076),
            ("revokeCapOpenVmDescriptor2R24", 2076),
            ("refreshDelegationCapOpenVmDescriptor2R24", 2076),
            ("revokeCapabilityCapOpenVmDescriptor2R24", 2076),
            ("transferCapOpenEffVmDescriptor2R24", 2086),
            ("attenuateCapOpenEffVmDescriptor2R24", 2219),
            ("transferFeeVmDescriptor2R24", 1763),
            ("transferCapOpenTBVmDescriptor2R24", 2086),
            ("heapWriteVmDescriptor2R24", 2153),
            ("delegateWriteCapOpenVmDescriptor2R24", 2076),
            ("introduceWriteCapOpenVmDescriptor2R24", 2076),
            ("delegateAttenWriteCapOpenVmDescriptor2R24", 2076),
            // ⚑ FLAG DAY 2026-07-28: 1878 → 2014. The two REMOVE write twins gained the TOMBSTONE
            // after-spine (Lean `CapOpenEmit.removeTombstoneConstraints`), so their NARROW host is
            // `CAP_OPEN_WIDTH + CAP_OPEN_AFTER_SPINE_SPAN` (2119 then, 2313 after the key nonet),
            // the same as the UPDATE twin. Before it, their committed AFTER cap-root group carried
            // ZERO gates.
            //
            // ⚠ The seven-column gap to the UPDATE twin is the interesting part and it SURVIVES the
            // key nonet unchanged (2212 against 2219, as it was 2190 against 2197): a tombstone has
            // no LEAF, only a constant digest, so the shared `afterSpineCols` layout leaves its 7
            // leaf-field columns unread — and the E1 dead-column scan strips exactly that run
            // (`e1_compact_generated.rs` carries the pair on both members). The narrow widths
            // coincide because the narrow member is not compacted; the wide ones do not.
            ("revokeDelegationWriteCapOpenVmDescriptor2R24", 2212),
            ("revokeCapabilityWriteCapOpenVmDescriptor2R24", 2212),
            ("refreshDelegationWriteCapOpenVmDescriptor2R24", 2219),
            ("spawnWriteCapOpenVmDescriptor2R24", 2076),
            ("spawnCapOpenVmDescriptor2R24", 2076),
            ("exerciseCapOpenVmDescriptor2R24", 2076),
            ("supplyMintVmDescriptor2R24", 1747),
        ];

        let mut n = 0usize;
        for (i, line) in WIDE_REGISTRY_STAGED_TSV.lines().enumerate() {
            if line.is_empty() {
                continue;
            }
            n += 1;
            let mut it = line.splitn(3, '\t');
            let key = it.next().expect("wide key");
            let _name = it.next().expect("wide name");
            let json = it.next().expect("wide json");
            assert_eq!(
                key, live_keys[i],
                "wide registry key {i} name-stable with the live registry"
            );
            let d = parse_vm_descriptor2(json).unwrap_or_else(|e| panic!("{key} wide parses: {e}"));
            let (pin_key, pin_width) = WIDE_MEMBER_GEOMETRY[i];
            assert_eq!(
                key, pin_key,
                "wide registry row {i} is the pinned member (a reorder / insertion moves this pin)"
            );
            assert_eq!(
                d.trace_width, pin_width,
                "{key}: wide width {} drifted off its pinned per-member geometry {pin_width}",
                d.trace_width
            );
            // Every wide member carries the 16 wide-commit PIs (the 8-felt ~124-bit before/after
            // anchors) appended PAST its host's PI vector, so `piCount = host.piCount + 16`. The
            // rotated cohort / `-eff` / cap-open / write members host the full rotated vector; the
            // turn-identity-pinned `transferCapOpenTB` hosts one more; the minimal-PI Class-A
            // `heapWrite` hosts just 4 → 20. The floor (≥ 20) is exactly the 16 anchors + heapWrite's
            // 4 host PIs — every member fits the 16 wide PIs, NO narrowing. (The rotated host was 46
            // → 62 and TB 49 → 65 before the 2026-08-07 seven-slot compaction.)
            assert!(
                d.public_input_count >= 20,
                "{key}: wide PI count {} carries the 16 wide-commit PIs",
                d.public_input_count
            );
            // ⚑ Row 0 (transfer) is the AVAIL-HARDENED, membership-teeth, gentian-refuse-welded
            // face and carries `WIDE_PI_COUNT + 2` PIs: the rotated vector + the dsl rc tail + the
            // 16 wide-commit anchors (that IS `WIDE_PI_COUNT`), plus 2 `(sender_leaf,
            // authorized_root)` membership claims.
            //
            // ⚑ This was the LITERAL `68` and it went stale on 2026-08-07, when the seven-slot PI
            // compaction took `V1_PI_COUNT` 42 → 35 (`docs/PI-DISPOSITION.md` §6). The
            // absolute-literal discipline the paragraph below argues for is aimed at a DIFFERENT
            // failure — re-deriving a member from a committed FORK OF ITSELF — and `WIDE_PI_COUNT`
            // is not that: it is the single symbolic layout source the Lean emitters and the Rust
            // generators both read, held to the Lean `pi.V1_PI_COUNT` by `pi::v3_drift_guard`. The
            // `+ 2` is this member's own membership splice and stays a literal, because it is a
            // property of THIS member and nothing else can move it.
            //
            // ⚠ This used to be a RELATIVE pin — `d.public_input_count == plain.public_input_count
            // + 2` and a five-term width equation `plain + avail_pad + 2 teeth + refuse_extent −
            // |E1 kill-set|` — computed against a committed single-row FORK of this member
            // (`WIDE_TRANSFER_STAGED_TSV` / `rotation-wide-transfer-staged.tsv`, DELETED
            // 2026-07-31). The fork was the PRE-HARDENING face: no availability shift, no gentian
            // floor refuse, and never E1-compacted, so it was a THIRD geometry that no verifier
            // resolved and nothing re-emitted. The equation therefore re-derived the deployed
            // member from a stale copy of itself, and its worked example (`1647 + 10 + 2 + 45 − 94
            // = 1610`) was 172 columns out of date at deletion. An absolute pin against a literal
            // is a gate; a relation to a fork of the same object is not.
            if i == 0 {
                let want = crate::effect_vm::trace_rotated::WIDE_PI_COUNT + 2;
                assert_eq!(
                    d.public_input_count, want,
                    "{key}: wide row 0 PI count drifted off its pin (WIDE_PI_COUNT + 2 membership \
                     claim PIs)"
                );
            }
        }
        assert_eq!(
            n,
            live_keys.len(),
            "the wide registry is a member-for-member cover of the live V3 registry (58 members)"
        );
        // 58 since initiative 10 appended the single-tick grain member (`grainTurnVmDescriptor2R24`).
        assert_eq!(n, 58, "the wide registry covers all 58 live V3 members");
    }

    /// **THE DERIVED WIDE+UMEM WELDED SET: the Lean contract holds, member for member.** The
    /// deleted `rotation-wide-umem-welded-registry-staged.tsv` used to be compared byte-for-byte
    /// against the Rust weld here. There is no file to compare against any more, so what is checked
    /// is the thing that replaced it: for all 57 keys the derivation SUCCEEDS, agrees with its
    /// Lean-emitted contract row on every quantity (name / width / PI count / constraint count /
    /// splice — enforced inside [`UMemWeldRow::check`], which runs on every construction), covers
    /// the bare wide registry exactly, and NARROWS NOTHING.
    ///
    /// ⚠ What this can no longer catch, stated plainly: a Lean emit whose welded HOST constraints
    /// differ from the bare wide member in some way the contract row does not describe. That is
    /// unreachable by construction — the emit welds onto the very member
    /// `WIDE_REGISTRY_STAGED_TSV` commits — and `scripts/emit_descriptors.py` re-derives every
    /// member from the emit's own stdout and REFUSES the emit on a mismatch, which is where an
    /// end-to-end byte comparison still happens.
    #[test]
    fn wide_umem_weld_derivation_matches_the_lean_contract() {
        use crate::descriptor_ir2::{VmConstraint2, parse_vm_descriptor2};

        let bare: std::collections::HashMap<&str, &str> = WIDE_REGISTRY_STAGED_TSV
            .lines()
            .filter(|l| !l.is_empty())
            .map(|l| {
                let mut it = l.splitn(3, '\t');
                let k = it.next().expect("bare key");
                let _n = it.next();
                let j = it.next().expect("bare json");
                (k, j)
            })
            .collect();

        let mut n = 0usize;
        for row in UMEM_WELD_TABLE {
            n += 1;
            assert!(
                row.name.ends_with(WIDE_UMEM_WELD_SUFFIX),
                "{}: welded member name carries the WIDE_UMEM_WELD_SUFFIX",
                row.key
            );
            let bare_json = bare
                .get(row.key)
                .unwrap_or_else(|| panic!("{}: welded key is a bare wide registry key", row.key));
            let bare_desc = parse_vm_descriptor2(bare_json)
                .unwrap_or_else(|e| panic!("{} bare member parses: {e}", row.key));

            // The derivation itself (its contract check runs inside).
            let welded = derive_welded_wide_member(row.key)
                .unwrap_or_else(|| panic!("{}: derivation must succeed", row.key));

            // The welded name is exactly the host's name plus the suffix — the property
            // `umem_weld_row_for_host` resolves on.
            assert_eq!(
                welded.name,
                format!("{}{WIDE_UMEM_WELD_SUFFIX}", bare_desc.name),
                "{}: the welded name is the bare name + the suffix",
                row.key
            );
            // The op is at the contract's index, at the contract's domain, over the 7 columns past
            // the host width.
            match &welded.constraints[row.splice] {
                VmConstraint2::UMemOp(spec) => {
                    assert_eq!(spec.domain, row.domain, "{}: welded domain", row.key);
                    // ⚑ DESTRUCTURE, do not CONSTRUCT. Building a `LeanExpr::Var(..)` here to
                    // compare against would be Rust-AUTHORED constraint IR, which
                    // `law1_no_new_rust_authored_constraints` counts `#[cfg(test)]` or not — and
                    // did: this assertion is the site that took the file's row 24 -> 25 in
                    // `681cd3ec8`. `matches!` reads the guard's shape instead of minting one, so
                    // the check is identical and nothing is authored. (Same discipline as
                    // `circuit/src/table_air.rs`'s tests, which say so in a comment.)
                    assert!(
                        matches!(
                            &spec.guard,
                            crate::lean_descriptor_air::LeanExpr::Var(v)
                                if *v == bare_desc.trace_width + 6
                        ),
                        "{}: the umem guard sits at host_width + 6, got {:?}",
                        row.key,
                        spec.guard
                    );
                }
                other => panic!("{}: contract splice is not a umemOp: {other:?}", row.key),
            }

            // NO-NARROWING: `piCount` unchanged, `traceWidth = host + 7`, every host constraint
            // survives in order (the weld only INSERTS).
            assert_eq!(
                welded.public_input_count, bare_desc.public_input_count,
                "{}: the weld must NOT change public_input_count (the 8-felt anchors stay put)",
                row.key
            );
            assert_eq!(
                welded.trace_width,
                bare_desc.trace_width + 7,
                "{}: the weld appends exactly the 7 umem columns",
                row.key
            );
            let survivors: Vec<_> = welded
                .constraints
                .iter()
                .enumerate()
                .filter(|(i, _)| *i != row.splice)
                .map(|(_, c)| c.clone())
                .collect();
            assert_eq!(
                survivors, bare_desc.constraints,
                "{}: the weld must leave every host constraint untouched and in order",
                row.key
            );
        }
        assert_eq!(
            n, 57,
            "the welded set is a member-for-member 57/57 cover of the bare wide registry: all 45 \
             v3RegistryCapOpenWide emit-source members + the 9 §10 WRITE-bearing cap-open tail wrappers \
             (the write twins the wire routes cap WRITE turns to, minus grantCapWriteCapOpen which has \
             no bare wide twin) + the 3 live-only wide members (transferCapOpenTB / heapWrite / \
             supplyMint)"
        );
        let keys: std::collections::BTreeSet<&str> =
            UMEM_WELD_TABLE.iter().map(|r| r.key).collect();
        assert_eq!(
            keys.len(),
            57,
            "the contract table has no duplicate keys (a duplicate would make the derivation \
             order-dependent)"
        );

        // ⚑ THE NAME IS NOT A KEY — pinned, because `umem_weld_row_for_host` would be a silent
        // mis-weld if it ever became one. `attenuateVmDescriptor2R24` and
        // `revokeCapabilityVmDescriptor2R24` share a display name AND differ in shape; the 8
        // setField twins share a name and AGREE in shape. Both facts are load-bearing: the first
        // says a name-only lookup is wrong, the second says a shape lookup is total.
        let attenuate = umem_weld_row("attenuateVmDescriptor2R24").expect("row");
        let revoke_cap = umem_weld_row("revokeCapabilityVmDescriptor2R24").expect("row");
        assert_eq!(
            attenuate.name, revoke_cap.name,
            "these two keys are expected to SHARE a welded display name"
        );
        assert_ne!(
            (attenuate.splice, attenuate.constraints),
            (revoke_cap.splice, revoke_cap.constraints),
            "…and to differ in shape, which is why the weld resolves on shape and not on name"
        );
        let mut by_shape: std::collections::BTreeMap<
            (&str, usize, usize, usize),
            std::collections::BTreeSet<usize>,
        > = std::collections::BTreeMap::new();
        for r in UMEM_WELD_TABLE {
            by_shape
                .entry((r.name, r.trace_width, r.pi_count, r.constraints))
                .or_default()
                .insert(r.splice);
        }
        let ambiguous: Vec<_> = by_shape.iter().filter(|(_, s)| s.len() > 1).collect();
        assert!(
            ambiguous.is_empty(),
            "a host SHAPE must determine the canonicity splice — these groups disagree: \
             {ambiguous:?}. `weld_umem_into_wide_descriptor` refuses on them at runtime; this says \
             so at build time."
        );
        assert_eq!(
            keys,
            bare.keys()
                .copied()
                .collect::<std::collections::BTreeSet<_>>(),
            "the contract table covers exactly the bare wide registry's keys"
        );
    }

    /// **THE VALUE8 EPOCH IS THE DEPLOYED SHAPE, IN ALL THREE LIVE REGISTRIES.** Each of the 8
    /// `setFieldVmDescriptor2-{slot}R24` members must carry the written slot's 7 completion-lane pins
    /// as PIs 46..=52 (with the 4 rc pins riding behind them), pinned at a slot-DISJOINT column set,
    /// on the 1-felt member AND on both wide members. Before the flip these members were the
    /// freeze-ALL wrap: `piCount == 50 / 66`, no completion pins, and an honest 32-byte field write
    /// (any nonzero byte outside `28..32`) could not prove at all.
    #[test]
    fn deployed_setfield_members_publish_the_value8_completion_lanes() {
        use crate::descriptor_ir2::VmConstraint2;
        use crate::lean_descriptor_air::{VmConstraint, VmRow};
        use std::collections::BTreeSet;

        // The welded set is DERIVED, not shipped, so it enters as parsed members rather than as a
        // TSV string — the same 8 setField twins, resolved through `derive_welded_wide_member`.
        let from_tsv =
            |tsv: &'static str| -> Vec<(String, crate::descriptor_ir2::EffectVmDescriptor2)> {
                tsv.lines()
                    .filter_map(|line| {
                        let mut it = line.splitn(3, '\t');
                        let key = it.next()?;
                        if !key.starts_with("setFieldVmDescriptor2-") {
                            return None;
                        }
                        let _name = it.next();
                        let json = it.next()?;
                        Some((
                            key.to_string(),
                            crate::descriptor_ir2::parse_vm_descriptor2(json)
                                .unwrap_or_else(|e| panic!("{key} parses: {e}")),
                        ))
                    })
                    .collect()
            };
        let welded_setfields: Vec<(String, crate::descriptor_ir2::EffectVmDescriptor2)> =
            welded_wide_members()
                .into_iter()
                .filter(|(k, _)| k.starts_with("setFieldVmDescriptor2-"))
                .map(|(k, d)| (k.to_string(), d))
                .collect();

        for (label, members, want_pi) in [
            // 57/73/73 → 58/74/74: the nine-lane epoch's EIGHTH value lane is an eighth PI.
            ("v3-1felt", from_tsv(V3_STAGED_REGISTRY_TSV), 58usize),
            ("wide", from_tsv(WIDE_REGISTRY_STAGED_TSV), 74),
            ("wide-umem-welded", welded_setfields.clone(), 74),
        ] {
            let mut seen = 0usize;
            let mut per_slot_cols: Vec<BTreeSet<usize>> = Vec::new();
            for (key, d) in &members {
                assert_eq!(
                    d.public_input_count, want_pi,
                    "{label}/{key}: the VALUE8 epoch publishes 8 completion PIs \
                     (46..=53) ahead of the rc tail"
                );
                let mut cols = BTreeSet::new();
                for k in 0..SETFIELD_VALUE8_PI_LEN {
                    let pi = SETFIELD_VALUE8_PI_BASE + k;
                    let col = d
                        .constraints
                        .iter()
                        .find_map(|c| match c {
                            VmConstraint2::Base(VmConstraint::PiBinding {
                                row: VmRow::Last,
                                col,
                                pi_index,
                            }) if *pi_index == pi => Some(*col),
                            _ => None,
                        })
                        .unwrap_or_else(|| {
                            panic!(
                                "{label}/{key}: PI {pi} is declared but pinned to NO last-row \
                                 column — the written slot's high bytes would be unbound"
                            )
                        });
                    assert!(
                        col < d.trace_width,
                        "{label}/{key}: PI {pi} pin column {col} past trace_width {}",
                        d.trace_width
                    );
                    cols.insert(col);
                }
                assert_eq!(
                    cols.len(),
                    SETFIELD_VALUE8_PI_LEN,
                    "{label}/{key}: 8 distinct columns"
                );
                per_slot_cols.push(cols);
                seen += 1;
            }
            assert_eq!(seen, 8, "{label}: the 8 written-slot setField members");
            // UNIQUE BINDING: slot i and slot j pin DISJOINT column sets, so a slot-i proof cannot
            // verify under descriptor-j (the census R1 "selector binding ambiguous" close).
            for i in 0..per_slot_cols.len() {
                for j in (i + 1)..per_slot_cols.len() {
                    assert!(
                        per_slot_cols[i].is_disjoint(&per_slot_cols[j]),
                        "{label}: setField slots {i}/{j} share a value8 pin column"
                    );
                }
            }
        }
    }

    /// The widened-entry codec teeth: round-trip + FAIL-CLOSED decode. A forged
    /// domain tag REFUSES; a registers-domain key outside the R=24 file REFUSES;
    /// a heap-domain key carries an arbitrary felt (the operand the u8 slot index
    /// could not express).
    #[test]
    fn rot_caveat_entry_codec_fail_closed() {
        use crate::effect_vm::RotCaveatEntry;
        use crate::effect_vm::columns::rotation::caveat as cav;
        use crate::field::BabyBear;
        // Heap-domain round-trip with a large felt key.
        let heap = RotCaveatEntry {
            type_tag: crate::effect_vm::pi::SLOT_CAVEAT_TAG_FIELD_GTE,
            domain_tag: cav::DOMAIN_HEAP,
            key: BabyBear::new(123_456_789),
            params: [
                BabyBear::new(50),
                BabyBear::ZERO,
                BabyBear::ZERO,
                BabyBear::ZERO,
            ],
        };
        let mut buf = [BabyBear::ZERO; 7];
        heap.write_to(&mut buf);
        assert_eq!(
            RotCaveatEntry::from_felts(&buf).expect("heap entry decodes"),
            heap
        );
        // Registers-domain round-trip (key inside the file).
        let slot = RotCaveatEntry {
            type_tag: crate::effect_vm::pi::SLOT_CAVEAT_TAG_MONOTONIC,
            domain_tag: cav::DOMAIN_REGISTERS,
            key: BabyBear::new(3),
            params: [BabyBear::ZERO; 4],
        };
        slot.write_to(&mut buf);
        assert_eq!(
            RotCaveatEntry::from_felts(&buf).expect("slot entry decodes"),
            slot
        );
        // A forged domain tag REFUSES (caps plane = 2 is NOT caveat-scopable).
        let mut forged = buf;
        forged[1] = BabyBear::new(2);
        assert!(
            RotCaveatEntry::from_felts(&forged).is_err(),
            "forged domain tag must refuse"
        );
        // A registers-domain key outside the R=24 file REFUSES.
        let mut oob = buf;
        oob[2] = BabyBear::new(cav::R as u32);
        assert!(
            RotCaveatEntry::from_felts(&oob).is_err(),
            "register key ≥ R must refuse"
        );
        // The zero entry is "no caveat".
        let zero = [BabyBear::ZERO; 7];
        assert_eq!(
            RotCaveatEntry::from_felts(&zero).expect("zero entry decodes"),
            RotCaveatEntry::zero()
        );
    }

    /// **THE CUSTOM PROOF-BIND CARRIER VERSION BOUNDARY (faithful flag-day v3).**
    ///
    /// A LEGACY 4-felt custom artifact — the retired eight-pin exposure (commit limbs 0..4 at
    /// cols `PARAM_BASE+4..8` → PI 46..49, then the VK block DIRECTLY after at 50..53, NO commit
    /// teeth) — is REFUSED by the versioned route with the TYPED
    /// `CustomCommitVersionError::RetiredV1`, never silently widened or zero-padded. The former v2
    /// twelve-pin low4-VK layout is also refused; the live sixteen-pin layout classifies `Ok(3)`.
    /// A pin-less descriptor and a garbled layout fail closed with their own typed variants. Also:
    /// the COMMITTED registry members (narrow + wide) classify as live v3.
    ///
    /// ⚑ 2026-07-31: the committed members are now the SUBTRACTED form — `dropUnforcedPins` deleted
    /// 14 of the 16 exposure pins because their columns were read by nothing, so the classifier was
    /// returning `UnknownLayout` on the live member. The pre-subtraction shapes are still exercised
    /// here (a retired artifact predates the subtraction and still carries its pins), and a new
    /// block below exercises the subtracted shape and its two fail-closed edges.
    #[test]
    fn custom_commit_version_boundary_refuses_legacy_four_felt() {
        use crate::descriptor_ir2::{EffectVmDescriptor2, VmConstraint2};
        use crate::effect_vm::columns::{PARAM_BASE, param};
        use crate::effect_vm::trace_rotated::{CUSTOM_COMMIT_TEETH_BASE, CUSTOM_VK_TEETH_BASE};
        use crate::lean_descriptor_air::{VmConstraint, VmRow};

        let pin = |col: usize, pi_index: usize| {
            VmConstraint2::Base(VmConstraint::PiBinding {
                row: VmRow::First,
                col,
                pi_index,
            })
        };
        let mk =
            |name: &str, constraints: Vec<VmConstraint2>, pi_count: usize| EffectVmDescriptor2 {
                name: name.to_string(),
                trace_width: CUSTOM_VK_TEETH_BASE + 4,
                public_input_count: pi_count,
                challenges: 0,
                tables: vec![],
                constraints,
                hash_sites: vec![],
                ranges: vec![],
            };

        // The RETIRED v1 exposure: commit limbs 0..4 at 46..49, VK block directly after.
        let mut legacy_pins = Vec::new();
        for k in 0..4 {
            legacy_pins.push(pin(
                PARAM_BASE + param::CUSTOM_PROOF_COMMIT_BASE + k,
                46 + k,
            ));
        }
        for k in 0..4 {
            legacy_pins.push(pin(PARAM_BASE + param::CUSTOM_VK_HASH_BASE + k, 50 + k));
        }
        let legacy = mk("custom-legacy-4felt", legacy_pins, 54);
        assert_eq!(
            custom_commit_version(&legacy),
            Err(CustomCommitVersionError::RetiredV1 {
                name: "custom-legacy-4felt".to_string(),
                commit_pi_lo: 46,
            }),
            "a legacy 4-felt custom artifact MUST be version-refused (typed), never widened"
        );
        assert!(require_custom_carrier_vk8(&legacy).is_err());
        // The typed refusal names the retirement explicitly.
        let msg = require_custom_carrier_vk8(&legacy).unwrap_err().to_string();
        assert!(
            msg.contains("RETIRED") && msg.contains("version-refused"),
            "the refusal must name the version retirement: {msg}"
        );

        // The RETIRED v2 exposure: commitment8, then only the low VK block.
        let mut v2_pins = Vec::new();
        for k in 0..4 {
            v2_pins.push(pin(
                PARAM_BASE + param::CUSTOM_PROOF_COMMIT_BASE + k,
                46 + k,
            ));
        }
        for k in 0..4 {
            v2_pins.push(pin(CUSTOM_COMMIT_TEETH_BASE + k, 50 + k));
        }
        for k in 0..4 {
            v2_pins.push(pin(PARAM_BASE + param::CUSTOM_VK_HASH_BASE + k, 54 + k));
        }
        let retired_v2 = mk("custom-retired-low4-vk", v2_pins.clone(), 58);
        assert!(matches!(
            custom_commit_version(&retired_v2),
            Err(CustomCommitVersionError::RetiredV2Low4Vk { .. })
        ));

        // The LIVE v3 exposure completes the exact canonical VK8 with four VK teeth.
        for k in 0..4 {
            v2_pins.push(pin(CUSTOM_VK_TEETH_BASE + k, 58 + k));
        }
        let live = mk("custom-live-vk8", v2_pins, 62);
        assert_eq!(custom_commit_version(&live), Ok(CUSTOM_COMMIT_VERSION));

        // No commit pin at all: not a custom-exposure member — fail closed.
        let none = mk("no-commit-pins", vec![pin(0, 3)], 10);
        assert!(matches!(
            custom_commit_version(&none),
            Err(CustomCommitVersionError::MissingCommitPins { .. })
        ));

        // ⚑ THE SUBTRACTED (post-`dropUnforcedPins`) SHAPE, which is what the deployed member is:
        // the two anchors 8 slots apart and NOTHING else pinned. It classifies v3 only when BOTH
        // surviving pieces of evidence are present — the reserved 16-slot exposure window AND a
        // `proof_bind` naming exactly those two columns.
        {
            use crate::descriptor_ir2::ProofBindSpec;
            use crate::lean_descriptor_air::LeanExpr;
            let anchors = vec![
                pin(PARAM_BASE + param::CUSTOM_PROOF_COMMIT_BASE, 46),
                pin(PARAM_BASE + param::CUSTOM_VK_HASH_BASE, 54),
            ];
            // (i) window reserved but NO proof_bind ⇒ fail closed. The bare pin pair is not enough:
            //     without the declaration nothing ties the exposure to the op the fold keys on.
            let no_decl = mk("custom-subtracted-no-proofbind", anchors.clone(), 62);
            assert!(
                matches!(
                    custom_commit_version(&no_decl),
                    Err(CustomCommitVersionError::UnknownLayout { .. })
                ),
                "two anchors alone must NOT classify as live v3"
            );
            // (ii) proof_bind present but the window is SHORT (a 12-slot v2-sized exposure) ⇒ fail
            //      closed rather than round up.
            let mut with_decl = anchors.clone();
            with_decl.push(VmConstraint2::ProofBind(ProofBindSpec {
                guard: LeanExpr::Const(1),
                // ⚑ EIGHT LANES: the four param limbs then four teeth columns, the deployed shape.
                commit: (0..4)
                    .map(|k| LeanExpr::Var(PARAM_BASE + param::CUSTOM_PROOF_COMMIT_BASE + k))
                    .chain((0..4).map(|k| LeanExpr::Var(4096 + k)))
                    .collect(),
                vk: (0..4)
                    .map(|k| LeanExpr::Var(PARAM_BASE + param::CUSTOM_VK_HASH_BASE + k))
                    .chain((0..4).map(|k| LeanExpr::Var(4100 + k)))
                    .collect(),
                // ⚑ Custom PORTS both halves — see `CommitBinding`. The program really is the
                // caller's to choose and the commitment really is derived off-row; what changed
                // on 2026-08-10 is that saying so requires NAMING the weld that binds them at the
                // fold, instead of writing `None` and emitting nothing.
                vk_pin: None,
                bound: crate::descriptor_ir2::CommitBinding::Port(
                    crate::descriptor_ir2::PortCover {
                        port: "custom-proof-commitment".to_owned(),
                        seam:
                            "dregg_circuit_prove::joint_turn_recursive::prove_custom_binding_node"
                                .to_owned(),
                    },
                ),
            }));
            let short = mk("custom-subtracted-short-window", with_decl.clone(), 58);
            assert!(
                matches!(
                    custom_commit_version(&short),
                    Err(CustomCommitVersionError::UnknownLayout { .. })
                ),
                "a 12-slot exposure window must NOT be rounded up to the live 16-slot v3"
            );
            // (iii) both ⇒ live v3.
            let subtracted = mk("custom-subtracted-live", with_decl, 62);
            assert_eq!(
                custom_commit_version(&subtracted),
                Ok(CUSTOM_COMMIT_VERSION)
            );
        }

        // Garbled: commit limbs 0..4 present but the following slots pin neither the VK block
        // nor teeth (a param column that is not the VK block) — fail closed as UnknownLayout.
        let mut garbled_pins = Vec::new();
        for k in 0..4 {
            garbled_pins.push(pin(
                PARAM_BASE + param::CUSTOM_PROOF_COMMIT_BASE + k,
                46 + k,
            ));
        }
        for k in 0..4 {
            garbled_pins.push(pin(PARAM_BASE + 2, 50 + k)); // a bogus mid-block pin
        }
        let garbled = mk("custom-garbled", garbled_pins, 54);
        assert!(matches!(
            custom_commit_version(&garbled),
            Err(CustomCommitVersionError::UnknownLayout { .. })
        ));

        // The COMMITTED members classify as live v3 — narrow (v3rot registry) and wide.
        // Both registries are `key\tname\tjson` (3 fields — see V3_STAGED_REGISTRY_TSV docs).
        let narrow_json = V3_STAGED_REGISTRY_TSV
            .lines()
            .find_map(|line| {
                let mut it = line.splitn(3, '\t');
                if it.next() == Some("customVmDescriptor2R24") {
                    let _name = it.next();
                    it.next()
                } else {
                    None
                }
            })
            .expect("custom member IS in the v3 staged registry");
        let narrow = parse_vm_descriptor2(narrow_json).expect("narrow custom parses");
        assert_eq!(custom_commit_version(&narrow), Ok(CUSTOM_COMMIT_VERSION));

        let wide_json = WIDE_REGISTRY_STAGED_TSV
            .lines()
            .find_map(|line| {
                let mut it = line.splitn(3, '\t');
                if it.next() == Some("customVmDescriptor2R24") {
                    let _name = it.next();
                    it.next()
                } else {
                    None
                }
            })
            .expect("custom member IS in the wide staged registry");
        let wide = parse_vm_descriptor2(wide_json).expect("wide custom parses");
        assert_eq!(custom_commit_version(&wide), Ok(CUSTOM_COMMIT_VERSION));
    }

    /// **THE MEASUREMENT [`require_no_unbacked_proof_bind`] IS KEYED ON.** Sweep every member of
    /// all three deployed staged registries and count its `DescriptorIR2.ProofBind` declarations.
    /// EXACTLY ONE member per registry declares one, and it is `customVmDescriptor2R24` — so
    /// "declares a proof-binding" IS the custom-member identity, structurally, with no name list
    /// to drift. Every other member passes the guard (they have no claim for a fold to back), and
    /// the custom member is REFUSED with a typed error naming the missing carrier witness.
    ///
    /// This is the tooth that would go red if a future member started declaring a proof-binding
    /// without its fold arm — the guard would then be over-firing on it, and that must be a
    /// decision, not a silent widening.
    #[test]
    fn registry_proof_bind_declarations_are_exactly_the_custom_member() {
        use crate::descriptor_ir2::parse_vm_descriptor2;

        let parse_tsv = |label: &str,
                         tsv: &'static str|
         -> Vec<(String, crate::descriptor_ir2::EffectVmDescriptor2)> {
            tsv.lines()
                .filter(|l| !l.trim().is_empty())
                .map(|line| {
                    let mut it = line.splitn(3, '\t');
                    let key = it.next().expect("registry line has a key").to_string();
                    let _name = it.next();
                    let json = it.next().expect("registry line has a descriptor json");
                    let d = parse_vm_descriptor2(json)
                        .unwrap_or_else(|e| panic!("{label}/{key} must parse: {e}"));
                    (key, d)
                })
                .collect()
        };
        // The welded set is DERIVED (`derive_welded_wide_member`), not a committed TSV.
        let welded: Vec<(String, crate::descriptor_ir2::EffectVmDescriptor2)> =
            welded_wide_members()
                .into_iter()
                .map(|(k, d)| (k.to_string(), d))
                .collect();

        for (label, members_vec) in [
            ("v3-staged", parse_tsv("v3-staged", V3_STAGED_REGISTRY_TSV)),
            (
                "wide-staged",
                parse_tsv("wide-staged", WIDE_REGISTRY_STAGED_TSV),
            ),
            ("wide-umem-welded", welded.clone()),
        ] {
            let mut declaring: Vec<(String, String, usize)> = Vec::new();
            let mut members = 0usize;
            for (key, d) in &members_vec {
                let key = key.clone();
                let d = d.clone();
                members += 1;
                let n = proof_bind_declarations(&d);
                if n > 0 {
                    declaring.push((key, d.name.clone(), n));
                }
                // The guard's two poles, member by member: a proof-bind member is REFUSED
                // without a witness; every other member passes.
                assert_eq!(
                    require_no_unbacked_proof_bind(&d).is_err(),
                    n > 0,
                    "{label}/{}: the no-witness guard must fire on EXACTLY the proof-bind \
                     declarers",
                    d.name
                );
            }
            assert!(
                members >= 57,
                "{label}: registry looks truncated ({members})"
            );
            assert_eq!(
                declaring.len(),
                1,
                "{label}: exactly one member may declare a proof-binding, found {declaring:?}"
            );
            let (key, name, n) = &declaring[0];
            assert_eq!(key, "customVmDescriptor2R24", "{label}: {name}");
            assert_eq!(*n, 1, "{label}: the custom member declares exactly one");

            // The typed refusal names the arm and the remedy — it is actionable, not a bare bool.
            let custom = members_vec
                .iter()
                .find(|(k, _)| k == "customVmDescriptor2R24")
                .map(|(_, d)| d.clone())
                .expect("the custom member is in every deployed set");
            let msg = require_no_unbacked_proof_bind(&custom)
                .unwrap_err()
                .to_string();
            assert!(
                msg.contains("NO carrier witness")
                    && msg.contains("CarrierWitness")
                    && msg.contains("fail-closed"),
                "{label}: the refusal must name the missing witness and the remedy: {msg}"
            );
        }
    }
}
