//! Per-cell DESCRIPTOR PARTICIPANTS: the rotated whole-turn leg the recursion core folds,
//! the generalized carrier-witness socket, and host-side admission.
//!
//! What lives here:
//!
//! - [`DescriptorParticipant`] / [`RotatedParticipantLeg`] — one cell's whole-turn ROTATED
//!   multi-table `Ir2BatchProof` over its R=24 cohort descriptor, plus the 38-PI vector it
//!   attests. The whole-chain recursion core ([`crate::ivc_turn_chain`]) mints its in-circuit
//!   leaf from this leg via `prove_descriptor_leaf_rotated_with_config`.
//! - [`CarrierWitness`] and the per-carrier witness bundles — the prover-side re-provable
//!   sub-proof inputs the chain prover folds against a leg's claimed carrier tuple (the
//!   fail-closed socket; see the enum docs).
//! - [`verify_descriptor_participant`] — host admission: the rotated proof re-verifies
//!   SELECTOR-BOUND against its carried descriptor before any fold. An admission discipline,
//!   not the soundness boundary (the leaf is re-verified in-circuit at the wrap).
//! - [`JointAggError`] — the shared error type of the binding-node fold-wires and leaf
//!   adapters ([`crate::joint_turn_recursive`], the `*_leaf_adapter` modules).
//!
//! HISTORY (E9, 2026-07-18): this module previously also hosted `JointTurnAggregationAir` —
//! a hand-written Rust uni-STARK AIR binding N per-cell proofs' shared turn id and folding a
//! `bundle_digest` — plus its Silver host path (`check_descriptor_joint_preconditions`) and
//! the Gold recursive fold's binding trace. DELETED as dead scaffolding: the `hash_4_to_1`
//! digest fold ran host-side only (the published `bundle_digest` was a FREE WITNESS in-AIR),
//! the `cell_commit` column was read by zero constraints, nothing tied binding rows to the
//! folded leaves in-circuit, and the layer had zero production callers. The deployed
//! cross-cell object is the Lean-emitted bilateral aggregation
//! (`turn-prover/src/aggregate_bilateral_prover.rs`, `EffectVmEmitBilateralAgg.lean`); the abstract
//! hyperedge/CG-2 spec is `Dregg2.Spec.JointViaHyper`.

use dregg_circuit::field::BabyBear;

// ============================================================================
// DESCRIPTOR-BACKED PARTICIPANT — the per-cell leaf the whole-chain recursion core folds.
// ============================================================================
//
// The per-cell admission is the verified-by-construction ROTATED multi-table IR-v2 leaf: a
// descriptor participant carries an `Ir2BatchProof` over its rotated R=24 cohort descriptor,
// verified SELECTOR-BOUND through the descriptor verifier (the Lean `selectorGate s` tooth
// makes a sound proof verify under EXACTLY ONE selector — the differential harness's
// `descriptor_proof_binds_to_its_selector`).

/// A single cell's whole-turn ROTATED-DESCRIPTOR proof. The leaf the recursion path folds is
/// the ROTATED multi-table `Ir2BatchProof` (the [`RotatedParticipantLeg`]), MANDATORY — the
/// participant carries exactly one rotated leg. Host admission
/// ([`verify_descriptor_participant`]) and the chain-root projections read the rotated leg's
/// PI vector (the rotated 38-PI vector carries the v1 prefix `[0..34)` unchanged —
/// `trace_rotated.rs:233` — plus the rotated commit pins at PI 34/35).
///
/// This whole descriptor-participant surface is `recursion`-gated: it feeds the whole-chain
/// recursion core ([`crate::ivc_turn_chain`]), which compiles only under `recursion`.
pub struct DescriptorParticipant {
    /// THE ROTATED LEG (Bucket-F mandatory leaf). The recursion core
    /// ([`crate::ivc_turn_chain::prove_chain_core_rotated`]) mints the in-circuit leaf from
    /// this rotated multi-table `Ir2BatchProof` via
    /// [`crate::ivc_turn_chain::prove_descriptor_leaf_rotated_with_config`]. All PI projections
    /// read its `public_inputs` prefix. `serde`-free (proofs are not serialized on this struct).
    pub rotated: RotatedParticipantLeg,
}

/// **The smallest PI vector that can CARRY the 16-felt wide anchor tail** — the rotated prefix
/// (`ROT_PI_COUNT` = 39) plus the 8-felt BEFORE and 8-felt AFTER commits. A leg at or above this
/// publishes the ~124-bit anchors at `[n-16 .. n)`; a leg below it structurally cannot, whatever
/// else is in its vector. It is the guard on
/// [`RotatedParticipantLeg::wide_old_root8`] / [`RotatedParticipantLeg::wide_new_root8`], and it is
/// deliberately NOT `WIDE_PI_COUNT` — see those accessors' docs.
pub const ROTATED_WIDE_ANCHORED_PI_MIN: usize =
    dregg_circuit::effect_vm::trace_rotated::ROT_PI_COUNT + 16;

/// The rotated per-cell leg a [`DescriptorParticipant`] carries at/after C4: the rotated
/// multi-table `Ir2BatchProof` (minted under the leaf-wrap config — log_blowup 6), its
/// descriptor (needed to rebuild the AIR set for the in-circuit verifier), and the 38-PI
/// vector it attests (the v1 prefix `[0..34)` + the 4 appended rotated commit/height/caveat
/// pins). The chain roots are read from this PI vector's ROTATED commit positions (PI 34/35).
pub struct RotatedParticipantLeg {
    /// The rotated multi-table batch proof, minted under
    /// [`crate::ivc_turn_chain::ir2_leaf_wrap_config`].
    pub proof: dregg_circuit::descriptor_ir2::Ir2BatchProof<
        crate::plonky3_recursion_impl::recursive::DreggRecursionConfig,
    >,
    /// The rotated descriptor this proof satisfies (rebuilds the `Ir2Air` set).
    pub descriptor: dregg_circuit::descriptor_ir2::EffectVmDescriptor2,
    /// The 38-PI vector (`ROT_PI_COUNT`) the proof attests.
    pub public_inputs: Vec<BabyBear>,
    /// **PROVER-SIDE-ONLY carrier sub-proof re-provable witness** (the generalized carrier
    /// witness SOCKET — Step-2 of the uniform carrier build). For a turn whose deployed leg
    /// publishes a claimed carrier authority tuple, this carries the prover-side inputs needed to
    /// RE-PROVE that carrier's sub-proof as a recursion-foldable leaf so the chain prover
    /// ([`crate::ivc_turn_chain::prove_chain_core_rotated`]) can fold it against the leg inside
    /// the recursion tree a PURE LIGHT CLIENT verifies. Today ONLY the
    /// [`CarrierWitness::Custom`] arm is deployed-wired; the six other carriers are STAGED
    /// sockets whose fold arms are explicitly FAIL-CLOSED (the chain prover REFUSES a leg
    /// carrying one until that carrier's wave lands its arm — it never silently proves).
    ///
    /// `None` for a turn with no carrier witness — the re-exec rung (a re-executing validator
    /// checks the carrier claim off-AIR; the light-client fold does not witness it). **The custom
    /// member is the ONE exception and `None` is REFUSED for it** (`require_no_unbacked_proof_bind`
    /// in the fold's no-carrier arm): the deployed AIR does not constrain the proof-bind columns
    /// at all, so there is no off-AIR claim left for a re-executor to check — detaching the
    /// witness deletes the enforcement instead of deferring it. This is
    /// prover-side witness data ONLY — it is NEVER serialized onto the on-wire artifact a light
    /// client verifies (the wire `dregg_turn::CustomProgramProof` keeps only finished bytes + PIs);
    /// the `Clone`/postcard round-trip below clones it directly (the proof is the heavy part).
    pub carrier_witness: Option<CarrierWitness>,
}

/// **THE GENERALIZED CARRIER WITNESS SOCKET** — one enum, one variant per carrier of the
/// universal-fold family, each holding the prover-side re-provable bundle its leaf adapter
/// consumes. [`RotatedParticipantLeg::carrier_witness`] carries `Option<CarrierWitness>`;
/// [`crate::ivc_turn_chain::prove_chain_core_rotated`] matches on it to pick the per-turn fold
/// branch.
///
/// FAIL-CLOSED DISCIPLINE (the fail-open law's socket half):
/// * `None` = the RE-EXEC RUNG: the turn folds as a plain segment leaf; the carrier claim is
///   checked by a re-executing validator, never fabricated for the light client. NOT available to
///   a leg whose descriptor declares a `DescriptorIR2.ProofBind` (the custom member): that arm is
///   fail-closed too (`require_no_unbacked_proof_bind`), because a proof-bind claim has no in-AIR
///   residue for a re-executor to check — the fold's connect is its whole enforcement.
/// * [`CarrierWitness::Custom`] = the ONE deployed arm (buff-in-production): the leg's claimed
///   `custom_proof_commitment` is bound to the re-proven sub-proof inside the fold.
/// * The six other variants are STAGED: the socket exists so each carrier wave lands its fold
///   arm without another restructure, but until that arm lands the chain prover REFUSES a leg
///   carrying the witness (see `prove_chain_core_rotated`'s unfilled-carrier arms). An unfilled
///   carrier witness NEVER silently proves — either it's `None` (re-exec) or its wave's arm
///   exists.
#[derive(Clone)]
pub enum CarrierWitness {
    /// The deployed custom-binding thread (Fork X, buff-in-production) — see
    /// [`CustomWitnessBundle`]. THE FIRST VARIANT: nothing regresses; the custom fold arm in
    /// `prove_chain_core_rotated` consumes exactly this.
    Custom(CustomWitnessBundle),
    /// FOLD-WIRED direct-IR2 custom relation.  Unlike [`Self::Custom`], this
    /// carries an already-authored `EffectVmDescriptor2` + base trace and never
    /// lowers or re-authors a Rust `CellProgram`.  The chain re-proves that exact
    /// descriptor under the recursion config and routes it through the same
    /// state/app-root binding node.
    CustomIr2(CustomIr2WitnessBundle),
    /// FOLD-WIRED (the 7th, LAST carrier): the bridge carrier's re-provable witness — the
    /// REAL foreign note-spend witness (per the carrier-deployment spec: folding the
    /// binding-only `bridge_action_witness` (DELETED 2026-08-07) was NOT the sound deployed path — a prover-chosen
    /// tuple; the G2 backing is the re-proven note-spend STARK,
    /// `note_spend_leaf_adapter::prove_note_spend_leaf_with_claim`). The fold arm admits a leg
    /// only when its descriptor pins the felt mint-hash claim slot (`BRIDGE_MINT_HASH_PI` = 46,
    /// the FIRST-row `prmCol 0` pin — the STEP-3/4 regen tie); otherwise it refuses
    /// (fail-closed).
    Bridge(BridgeWitnessBundle),
    /// FOLD-WIRED (v12): the sovereign carrier's authority-tuple witness (P1 fills the
    /// KEY_COMMIT teeth from `before_cell.public_key()`). The fold arm admits a leg only when
    /// its descriptor pins the teeth claim slots (`SOVEREIGN_KEY_COMMIT_PI_LO` — the big-bang
    /// regen tie); otherwise it refuses (fail-closed).
    Sovereign(SovereignWitnessBundle),
    /// FOLD-WIRED (v12): the factory carrier's creation-backing witness (`factory_vk`,
    /// `child_vk`, derivation digest). The fold arm binds the leg's `child_vk8` octet claim
    /// (PI 47..54, `factoryV3Carriers`) to the re-proven backing leaf; a leg whose descriptor
    /// lacks the STEP-3 octet pins is refused (fail-closed, the big-bang regen tie).
    Factory(FactoryWitnessBundle),
    /// FOLD-WIRED (v12): the hatchery carrier's contract-attestation witness
    /// (`contract_hash`, `invariant_digest`; the invariant half rides factory's leg). The
    /// fold arm binds the leg's `contract_hash8` octet claim (PI 55..62, `factoryV3Carriers`)
    /// to the re-proven attestation leaf; pin-less legs are refused (fail-closed).
    Hatchery(HatcheryWitnessBundle),
    /// FOLD-WIRED (v12): the membership carrier's sender-membership witness (`sender_leaf`,
    /// `authorized_root`). The fold arm binds the leg's claim slots
    /// (`MEMBERSHIP_CLAIM_PI_LO`) to the re-proven membership leaf; pin-less legs are refused
    /// (fail-closed, the big-bang regen tie).
    Membership(MembershipWitnessBundle),
    /// FOLD-WIRED (the 6th carrier): the DSL/Dfa carrier's re-provable predicate program
    /// witness (structurally the custom shape — the dsl adapter REUSES the custom leaf
    /// machinery). The fold arm derives the rc claim slots per member from the leg's
    /// committed descriptor (`ivc_turn_chain::dsl_rc_claim_pi_lo` — the `withDfaRcPins`
    /// cohort-wide emit), REFUSES a pin-less descriptor AND the zero rc sentinel (a no-Dfa
    /// turn never folds a vacuous claim), and binds the re-proven DSL transition leaf to the
    /// published route-commitment.
    Dsl(DslWitnessBundle),
    /// FOLD-WIRED (the 8th carrier): the DECO/zkTLS + Stripe money-in carrier's re-provable
    /// payment-commitment witness — the felt-domain `PaymentFacts` the DECO leaf recomputes
    /// the identity from (per `docs/deos/DECO-CARRIER-PLAN.md` Option B: the in-AIR leaf
    /// verifies only the Poseidon2 commitment binding `PaymentFacts → payment_hash`;
    /// ed25519/HMAC/SHA-256 stay OFF-AIR, executor-checked, as named §8 carriers — exactly
    /// what `Deco.lean::deco_binds_payment` proves and exactly bridge's ed25519 posture). The
    /// fold arm admits a leg only when its deployed `stripeMint` descriptor pins the felt
    /// payment-identity claim slot (`DECO_PAYMENT_HASH_PI`, FIRST-row `param0` — the big-bang
    /// regen tie); otherwise it refuses (fail-closed).
    Deco(DecoWitnessBundle),
}

impl CarrierWitness {
    /// The carrier's stable lowercase name (error messages / logging).
    pub fn carrier_name(&self) -> &'static str {
        match self {
            CarrierWitness::Custom(_) => "custom",
            CarrierWitness::CustomIr2(_) => "custom-ir2",
            CarrierWitness::Bridge(_) => "bridge",
            CarrierWitness::Sovereign(_) => "sovereign",
            CarrierWitness::Factory(_) => "factory",
            CarrierWitness::Hatchery(_) => "hatchery",
            CarrierWitness::Membership(_) => "membership",
            CarrierWitness::Dsl(_) => "dsl",
            CarrierWitness::Deco(_) => "deco",
        }
    }

    /// The custom bundle, iff this is the [`CarrierWitness::Custom`] variant (the migration
    /// accessor for pre-socket call sites).
    pub fn as_custom(&self) -> Option<&CustomWitnessBundle> {
        match self {
            CarrierWitness::Custom(b) => Some(b),
            _ => None,
        }
    }
}

impl From<CustomWitnessBundle> for CarrierWitness {
    fn from(bundle: CustomWitnessBundle) -> Self {
        CarrierWitness::Custom(bundle)
    }
}

impl From<CustomIr2WitnessBundle> for CarrierWitness {
    fn from(bundle: CustomIr2WitnessBundle) -> Self {
        CarrierWitness::CustomIr2(bundle)
    }
}

/// A PRE-BUILT Lean-emitted descriptor + its retained base trace, an ALTERNATIVE sub-proof source
/// for a state-binding [`CustomWitnessBundle`]. When present, the fold's state-node arm mints the
/// custom leaf via [`crate::custom_leaf_adapter::prove_custom_leaf_descriptor_with_state_commitment`]
/// (proving the PROVEN Lean AIR directly) instead of lowering the bundle's Rust `CellProgram` —
/// the seam the automatafl STEP cutover rides (the deployed proof proves through
/// `automataflStepDescN {n}`, not the hand-authored Rust AIR). The exposed claim and the fold
/// contract are byte-identical to the `CellProgram` state leaf, so the state-binding node is
/// unchanged. `public_inputs` (on the bundle) is the SINGLE PI source for both the commitment and
/// the state prefix, so a descriptor source cannot disagree with the leg's claimed commitment.
#[derive(Clone, Debug)]
pub struct DescriptorStateLeafSource {
    /// The decoded Lean descriptor the sub-proof re-proves (its `public_input_count` must equal
    /// the bundle's `public_inputs.len()`).
    pub descriptor: dregg_circuit::descriptor_ir2::EffectVmDescriptor2,
    /// The trusted-Rust-generated base trace (rows of `descriptor.trace_width`) satisfying it.
    pub base_trace: Vec<Vec<BabyBear>>,
    /// **THE BOARD-WINDOW OPT-IN (the two-leg fold).** `None` = the 24-lane state leaf + state
    /// node (byte-identical to before). `Some(binding)` = the leaf ALSO re-exposes the IN/OUT
    /// state windows the descriptor's PIs carry
    /// ([`crate::custom_leaf_adapter::prove_custom_leaf_descriptor_with_board_window`]) and the
    /// per-turn node carries them up
    /// ([`crate::joint_turn_recursive::prove_custom_binding_node_state_and_board_segmented`]), so
    /// the merge can `connect` `left.OUT == right.IN` at every aggregation node. Without it the
    /// per-turn node drops the application PIs and adjacent turns' states are unrelated numbers.
    /// MANDATORY when present: the board-window node REQUIRES the wide claim, so a forger cannot
    /// dodge the seam by minting the narrow leaf.
    pub board_window: Option<dregg_circuit::effect_vm::custom_state_binding::BoardWindowBinding>,
}

/// The prover-side re-provable witness for a `Custom` turn's external sub-proof — exactly the four
/// arguments [`crate::custom_leaf_adapter::prove_custom_leaf_with_commitment`] consumes to re-prove
/// the `CellProgram` as a recursion-foldable IR-v2 leaf with an in-circuit-computed PI commitment.
/// Retained on [`RotatedParticipantLeg::custom_witness`] so the deployed chain prover can mint the
/// custom sub-proof leaf and fold it in with the dual-claim binding node. NEVER sent to the light
/// client.
#[derive(Clone)]
pub struct CustomWitnessBundle {
    /// The custom-effect `CellProgram` the sub-proof attests (re-proven, not the bespoke STARK).
    pub program: dregg_circuit::dsl::circuit::CellProgram,
    /// The named trace-column witness the program proves over.
    pub witness_values: std::collections::HashMap<String, Vec<BabyBear>>,
    /// The number of trace rows.
    pub num_rows: usize,
    /// The custom program's public inputs (the values the in-circuit PI commitment is taken over —
    /// equal, by construction, to the leg's claimed `custom_proof_commitment` preimage).
    pub public_inputs: Vec<BabyBear>,
    /// **THE APP-ROOT WELD DECLARATION (the deployed keystone opt-in).** `None` = the state-node
    /// path (byte-identical to before: the fold binds `[commitment ‖ old8 ‖ new8]`, so `R` — a
    /// published app root in the sub-proof PIs — rides only as an opaque commitment preimage).
    /// `Some(binding)` = the APP-ROOT node path: the leg additionally exposes its committed field
    /// value for key `binding.field_key`, and the fold `connect`s the sub-proof's published root
    /// `R` (at `binding.app_root_pi_offset`, width `binding.app_root_len`) to it — so a sub-proof
    /// whose `R` disagrees with the cell's real stored field has NO satisfying partner (UNSAT).
    /// MANDATORY when present: the app-root node REQUIRES the wide field-exposure claim (no
    /// conditional connect — a forger cannot dodge by minting the narrow state leaf). Requires the
    /// leg's wide descriptor to publish the field octet as a PI (`generate_rotated_custom_wide`'s
    /// field-K exposure / Lean `customFieldKExposure`).
    pub app_root_binding: Option<dregg_circuit::effect_vm::custom_state_binding::AppRootBinding>,
    /// **THE DIRECT-IR2 STATE-LEAF OPT-IN (the automatafl STEP cutover).** `None` = the leaf is
    /// minted by lowering `program` (the deployed default). `Some(src)` = the state-node arm mints
    /// the leaf from the PROVEN Lean descriptor `src.descriptor` + `src.base_trace` directly
    /// (`prove_custom_leaf_descriptor_with_state_commitment`), so the fold proves the Lean-authored
    /// AIR rather than a re-authored Rust `CellProgram`. Only consulted on the state path
    /// (`app_root_binding == None`); the exposed claim is byte-identical, so the state-binding node
    /// is unaffected. `program`/`witness_values`/`num_rows` are retained but unused for the leaf.
    pub descriptor_state_leaf: Option<DescriptorStateLeafSource>,
}

/// Prover-side retention for a Lean-emitted/direct IR2 custom relation.
///
/// The normal custom bundle retains a `CellProgram` and named witness map, then
/// lowers that program to IR2 inside the fold.  This bundle starts at the IR2
/// source of truth: descriptor + exact base trace + PIs.  It is prover-side only
/// and is never serialized into the light-client artifact.
#[derive(Clone, Debug)]
pub struct CustomIr2VkRecipe {
    program_bytes: Vec<u8>,
    air_fingerprint: [u8; 32],
    verifier_fingerprint_canonical: [u8; 32],
    proving_system_canonical: Vec<u8>,
}

impl CustomIr2VkRecipe {
    /// Build the canonical-v2 recipe used by the custom registry for a
    /// `VerifierFingerprint::SourceHash` verifier.
    pub fn source_hash(
        program_bytes: Vec<u8>,
        air_fingerprint: [u8; 32],
        verifier_source_hash: [u8; 32],
        proving_system_canonical: Vec<u8>,
    ) -> Self {
        let mut verifier = blake3::Hasher::new_derive_key("dregg-verifier-fingerprint-v1");
        verifier.update(&[0]);
        verifier.update(&verifier_source_hash);
        Self {
            program_bytes,
            air_fingerprint,
            verifier_fingerprint_canonical: *verifier.finalize().as_bytes(),
            proving_system_canonical,
        }
    }

    /// Parse the recipe's exact program bytes and require byte-authored IR2
    /// semantics to equal the descriptor that the recursion leaf re-proves.
    ///
    /// New IR2 programs use the strict typed descriptor codec; older registry
    /// entries used UTF-8 JSON.  The typed decoder is attempted first and is
    /// itself canonical/trailing-byte strict.  JSON remains a compatibility
    /// fallback, never an alternate meaning: either decoding path must produce
    /// the exact descriptor passed to the recursion leaf.
    pub fn require_exact_descriptor(
        &self,
        descriptor: &dregg_circuit::descriptor_ir2::EffectVmDescriptor2,
    ) -> Result<(), String> {
        let recipe_descriptor =
            match dregg_circuit::descriptor_ir2_canonical::decode_canonical_effect_vm_descriptor2(
                &self.program_bytes,
            ) {
                Ok(descriptor) => descriptor,
                Err(typed_error) => {
                    let json = std::str::from_utf8(&self.program_bytes).map_err(|json_error| {
                        format!(
                            "direct-IR2 canonical program bytes decode as neither the strict typed \
                             descriptor ({typed_error}) nor legacy UTF-8 JSON ({json_error})"
                        )
                    })?;
                    dregg_circuit::descriptor_ir2::parse_vm_descriptor2(json).map_err(
                        |json_error| {
                            format!(
                                "direct-IR2 canonical program bytes decode as neither the strict \
                                 typed descriptor ({typed_error}) nor legacy JSON ({json_error})"
                            )
                        },
                    )?
                }
            };
        if &recipe_descriptor != descriptor {
            return Err(
                "direct-IR2 descriptor differs from canonical-v2 program bytes".to_string(),
            );
        }
        Ok(())
    }

    /// Canonical `dregg-vk-v2` registry identity, byte-identical to
    /// `dregg_cell::vk_v2::canonical_vk_v2` for the retained recipe.
    pub fn canonical_vk_hash(&self) -> [u8; 32] {
        let mut h = blake3::Hasher::new_derive_key("dregg-vk-v2");
        h.update(&(self.program_bytes.len() as u64).to_le_bytes());
        h.update(&self.program_bytes);
        h.update(&self.air_fingerprint);
        h.update(&self.verifier_fingerprint_canonical);
        h.update(&(self.proving_system_canonical.len() as u64).to_le_bytes());
        h.update(&self.proving_system_canonical);
        *h.finalize().as_bytes()
    }

    /// Faithful 8-felt projection used by `Effect::Custom` and the eventual
    /// full-width leg-to-leaf correlation node.
    pub fn canonical_vk_felts(&self) -> [BabyBear; 8] {
        dregg_circuit::effect_vm::bytes32_to_8_limbs(&self.canonical_vk_hash())
    }
}

#[derive(Clone)]
pub struct CustomIr2WitnessBundle {
    /// Exact emitted descriptor the executor's custom VK identifies.
    pub descriptor: dregg_circuit::descriptor_ir2::EffectVmDescriptor2,
    /// Base rows for the exact descriptor; chip tables are derived by the
    /// general IR2 prover under the recursion config.
    pub base_trace: Vec<Vec<BabyBear>>,
    /// Canonical descriptor public inputs.  Must start `[old8 || new8]`.
    pub public_inputs: Vec<BabyBear>,
    /// Exact canonical-v2 registry recipe.  The direct recursion leaf parses
    /// these bytes back to `descriptor` before proving and exposes the full
    /// faithful 8-felt VK identity under its recursion root anchor.
    pub vk_recipe: CustomIr2VkRecipe,
    /// Mandatory app-root weld.  Direct IR2 is introduced for a sovereign
    /// decision relation, so silently degrading it to the state-only node is
    /// not an available construction.
    pub app_root_binding: dregg_circuit::effect_vm::custom_state_binding::AppRootBinding,
    /// Optional native-eight post-state fields-map weld.  When present, the
    /// direct relation's published root is connected lane-for-lane to the
    /// Lean-pinned Custom wide leg publication before the segment can fold.
    pub post_fields_root_binding:
        Option<dregg_circuit::effect_vm::custom_state_binding::PostFieldsRootBinding>,
}

/// FOLD-WIRED (the 7th carrier) bridge-carrier bundle — the prover-side inputs
/// [`crate::note_spend_leaf_adapter::prove_note_spend_leaf_with_claim`] consumes: the REAL
/// foreign note-spend witness (spending key, 28-limb commitment preimage, Merkle path) — the
/// G2 backing the carrier-deployment spec mandates. Folding the binding-only
/// `bridge_action_witness` was REFUSED as the backing and is now DELETED (a prover-chosen tuple, no membership / no
/// key knowledge — the vacuous connect the fail-open law forbids); this bundle re-proves the
/// REAL spend STARK, whose leaf exposes the FELT-domain mint identity
/// (`note_spend_mint_hash_felt`, in-AIR-recomputed at claim lane 6) the deployed leg's
/// mint-hash PI (46, `mintV3BridgeHash`) connects to.
#[derive(Clone)]
pub struct BridgeWitnessBundle {
    /// The REAL note-spend witness (the SAME `NoteSpendingWitness` the off-AIR
    /// `verify_note_spend_dsl_full` path proves).
    pub note_spend: dregg_circuit::note_spending_witness::NoteSpendingWitness,
    /// The 7-slot claim tuple `[nullifier, merkle_root, value_lo, asset_type,
    /// destination_federation, value_hi, mint_hash]` (for an honest bundle,
    /// [`crate::note_spend_leaf_adapter::note_spend_leaf_public_inputs`]).
    pub public_inputs: Vec<BabyBear>,
}

impl BridgeWitnessBundle {
    /// Project the honest bundle from the typed note-spend witness (PIs derived from the
    /// witness itself — including the in-AIR-recomputable felt mint identity at lane 6 — so
    /// claim == execution by construction).
    pub fn from_note_spend_witness(
        note_spend: &dregg_circuit::note_spending_witness::NoteSpendingWitness,
    ) -> Self {
        Self {
            public_inputs: crate::note_spend_leaf_adapter::note_spend_leaf_public_inputs(
                note_spend,
            ),
            note_spend: note_spend.clone(),
        }
    }

    /// **THE PRODUCTION PROJECTION (fail-closed off-wire)** — the bridge twin of
    /// [`SovereignWitnessBundle::from_retained_authority`]. The turn-build path RETAINS the
    /// note-spend witness (the same material the source-federation spend proof was minted
    /// from); a wire-rehydrated turn retains nothing (`None`) — the re-exec rung,
    /// FAIL-CLOSED rather than fabricated.
    pub fn from_retained_bridge(
        retained: Option<&dregg_circuit::note_spending_witness::NoteSpendingWitness>,
    ) -> Option<Self> {
        retained.map(Self::from_note_spend_witness)
    }
}

/// FOLD-WIRED (the 8th carrier) DECO-carrier bundle — the prover-side inputs
/// [`crate::deco_leaf_adapter::prove_deco_leaf_with_claim`] consumes: the felt-domain
/// `PaymentFacts` (`amountCents, currency, recipient, paymentIntentId`) + the transcript-
/// commitment opening `salt`. The DECO commitment leaf recomputes the felt payment identity
/// (`deco_payment_hash_felt`) IN-AIR from these and exposes it at claim lane
/// [`crate::deco_leaf_adapter::DECO_LEAF_PAYMENT_HASH_PI`]; the deployed `stripeMint` leg's
/// `payment_hash` PI (`DECO_PAYMENT_HASH_PI`) connects to it. The heavy TLS crypto
/// (ed25519/HMAC/SHA-256/parse) stays OFF-AIR, executor-checked — the named §8 carriers
/// (`DECO-CARRIER-PLAN.md` §5). The executor projects a `StripePaymentAttestation` onto the
/// felt witness via `dregg_circuit::dsl::deco_payment::stripe_payment_hash_felt`'s encoders.
#[derive(Clone)]
pub struct DecoWitnessBundle {
    /// The felt-domain payment witness the DECO commitment leaf proves over.
    pub witness: crate::deco_leaf_adapter::DecoLeafWitness,
    /// The `DECO_CLAIM_LEN`-slot claim tuple (for an honest bundle,
    /// [`crate::deco_leaf_adapter::deco_leaf_public_inputs`]).
    pub public_inputs: Vec<BabyBear>,
}

impl DecoWitnessBundle {
    /// Project the honest bundle from the typed felt payment witness (PIs derived from the
    /// witness itself — including the in-AIR-recomputable felt payment identity — so
    /// claim == execution by construction).
    pub fn from_leaf_witness(witness: &crate::deco_leaf_adapter::DecoLeafWitness) -> Self {
        Self {
            public_inputs: crate::deco_leaf_adapter::deco_leaf_public_inputs(witness),
            witness: *witness,
        }
    }

    /// **THE PRODUCTION PROJECTION (fail-closed off-wire)** — the DECO twin of
    /// [`BridgeWitnessBundle::from_retained_bridge`]. The turn-build path RETAINS the felt
    /// payment witness (projected from the `VerifiedPayment` the Stripe webhook verify
    /// produced, `stripe_mirror.rs`); a wire-rehydrated turn retains nothing (`None`) — the
    /// re-exec rung, FAIL-CLOSED rather than fabricated.
    pub fn from_retained_deco(
        retained: Option<&crate::deco_leaf_adapter::DecoLeafWitness>,
    ) -> Option<Self> {
        retained.map(Self::from_leaf_witness)
    }
}

/// STAGED sovereign-carrier bundle — the prover-side inputs
/// [`crate::sovereign_leaf_adapter::prove_sovereign_leaf_with_key_claim`] consumes (the 21-slot
/// authority tuple `(key_commit, sequence, old, new)`; P1 fills `key_commit` from
/// `before_cell.public_key()`). Fold arm FAIL-CLOSED until the sovereign wave lands it.
#[derive(Clone)]
pub struct SovereignWitnessBundle {
    /// The typed sovereign authority-tuple witness.
    pub authority: crate::sovereign_leaf_adapter::SovereignAuthorityWitness,
    /// The 21-slot bound tuple PIs (for an honest bundle, `authority.public_inputs()`).
    pub public_inputs: Vec<BabyBear>,
}

impl SovereignWitnessBundle {
    /// Project the honest bundle from the typed authority witness (PIs derived, claim ==
    /// execution by construction).
    pub fn from_authority_witness(
        authority: &crate::sovereign_leaf_adapter::SovereignAuthorityWitness,
    ) -> Self {
        Self {
            public_inputs: authority.public_inputs(),
            authority: authority.clone(),
        }
    }

    /// **THE PRODUCTION PROJECTION (fail-closed off-wire)** — the sovereign twin of
    /// [`CustomWitnessBundle::from_bound_custom_proof`]. The turn-build path RETAINS the
    /// authority tuple (`key_commit` from `before_cell.public_key()`, sequence, old/new
    /// anchors); a wire-rehydrated turn retains nothing (`None`) — the re-exec rung,
    /// FAIL-CLOSED rather than fabricated.
    pub fn from_retained_authority(
        retained: Option<&crate::sovereign_leaf_adapter::SovereignAuthorityWitness>,
    ) -> Option<Self> {
        retained.map(Self::from_authority_witness)
    }
}

/// STAGED factory-carrier bundle — the prover-side inputs
/// [`crate::factory_leaf_adapter::prove_factory_leaf_with_child_vk_claim`] consumes (the 24-slot
/// backing tuple `(factory_vk, child_vk, derivation_digest)`). ⚑ Anti-vacuity: the factory third
/// edge must gate against the FAITHFUL 8-felt committed child_vk, never the 31-bit col-69 fold.
/// Fold arm FAIL-CLOSED until the factory wave lands it.
#[derive(Clone)]
pub struct FactoryWitnessBundle {
    /// The typed factory creation-backing witness.
    pub backing: crate::factory_leaf_adapter::FactoryBackingWitness,
    /// The 24-slot bound tuple PIs (for an honest bundle, `backing.public_inputs()`).
    pub public_inputs: Vec<BabyBear>,
}

impl FactoryWitnessBundle {
    /// Project the honest bundle from the typed backing witness (PIs derived, claim ==
    /// execution by construction).
    pub fn from_backing_witness(
        backing: &crate::factory_leaf_adapter::FactoryBackingWitness,
    ) -> Self {
        Self {
            public_inputs: backing.public_inputs(),
            backing: backing.clone(),
        }
    }

    /// **THE PRODUCTION PROJECTION (fail-closed off-wire)** — the factory twin of
    /// [`CustomWitnessBundle::from_bound_custom_proof`]. The turn-build path RETAINS the
    /// validated creation-backing witness (the `(factory_vk, child_vk, derivation_digest)`
    /// tuple `FactoryRegistry::validate_and_record` binds); a turn REHYDRATED from the
    /// on-wire artifact retains nothing (`None`) — such a turn takes the re-exec rung,
    /// FAIL-CLOSED rather than fabricated (the fold never invents a backing tuple the
    /// executor did not validate).
    pub fn from_retained_backing(
        retained: Option<&crate::factory_leaf_adapter::FactoryBackingWitness>,
    ) -> Option<Self> {
        retained.map(Self::from_backing_witness)
    }
}

/// STAGED hatchery-carrier bundle — the prover-side inputs
/// [`crate::hatchery_leaf_adapter::prove_hatchery_leaf_with_contract_claim`] consumes (the
/// 16-slot attestation tuple `(contract_hash, invariant_digest)`; the invariant half rides
/// factory's CreateCellFromFactory leg). Fold arm FAIL-CLOSED until the hatchery wave lands it.
#[derive(Clone)]
pub struct HatcheryWitnessBundle {
    /// The typed hatchery contract-attestation witness.
    pub attestation: crate::hatchery_leaf_adapter::HatcheryAttestationWitness,
    /// The 16-slot bound tuple PIs (for an honest bundle, `attestation.public_inputs()`).
    pub public_inputs: Vec<BabyBear>,
}

impl HatcheryWitnessBundle {
    /// Project the honest bundle from the typed attestation witness (PIs derived, claim ==
    /// execution by construction).
    pub fn from_attestation_witness(
        attestation: &crate::hatchery_leaf_adapter::HatcheryAttestationWitness,
    ) -> Self {
        Self {
            public_inputs: attestation.public_inputs(),
            attestation: attestation.clone(),
        }
    }

    /// **THE PRODUCTION PROJECTION (fail-closed off-wire)** — the hatchery twin of
    /// [`CustomWitnessBundle::from_bound_custom_proof`]. The hatchery-mint path RETAINS the
    /// `HpresProof::Attested` contract attestation (`contract_hash` + the invariant digest
    /// riding factory's leg); a wire-rehydrated turn retains nothing (`None`) — the re-exec
    /// rung, FAIL-CLOSED rather than fabricated.
    pub fn from_retained_attestation(
        retained: Option<&crate::hatchery_leaf_adapter::HatcheryAttestationWitness>,
    ) -> Option<Self> {
        retained.map(Self::from_attestation_witness)
    }
}

/// STAGED membership-carrier bundle — the prover-side inputs
/// [`crate::membership_leaf_adapter::prove_membership_leaf_with_claim`] consumes (the 2-slot
/// `(sender_leaf, authorized_root)` tuple; the Merkle path stays off-AIR, a named seam). Fold
/// arm FAIL-CLOSED until the membership wave lands it.
#[derive(Clone)]
pub struct MembershipWitnessBundle {
    /// The typed sender-membership witness.
    pub membership: crate::membership_leaf_adapter::SenderMembershipWitness,
    /// The 2-slot bound tuple PIs (for an honest bundle, `membership.public_inputs()`).
    pub public_inputs: Vec<BabyBear>,
}

impl MembershipWitnessBundle {
    /// Project the honest bundle from the typed membership witness (PIs derived, claim ==
    /// execution by construction).
    pub fn from_membership_witness(
        membership: &crate::membership_leaf_adapter::SenderMembershipWitness,
    ) -> Self {
        Self {
            public_inputs: membership.public_inputs(),
            membership: *membership,
        }
    }

    /// **THE PRODUCTION PROJECTION (fail-closed off-wire)** — the membership twin of
    /// [`CustomWitnessBundle::from_bound_custom_proof`]. The turn-build path RETAINS the
    /// `(sender_leaf, authorized_root)` tuple its caveat check verified; a wire-rehydrated
    /// turn retains nothing (`None`) — the re-exec rung, FAIL-CLOSED rather than fabricated.
    pub fn from_retained_membership(
        retained: Option<&crate::membership_leaf_adapter::SenderMembershipWitness>,
    ) -> Option<Self> {
        retained.map(Self::from_membership_witness)
    }
}

/// FOLD-WIRED DSL/Dfa-carrier bundle — structurally the CUSTOM shape (the dsl adapter
/// [`crate::dsl_leaf_adapter::prove_dsl_leaf_with_commitment`] REUSES
/// `prove_custom_leaf_with_commitment`): the re-provable predicate-transition `CellProgram` +
/// trace witness + PIs. For an honest bundle
/// `custom_proof_pi_commitment(public_inputs)` equals the leg's published route-commitment
/// (the `dfa_route_commitment` rc PIs) — the fold's `connect` requires it.
#[derive(Clone, Debug)]
pub struct DslWitnessBundle {
    /// The Dfa predicate-transition `CellProgram` the sub-proof attests.
    pub program: dregg_circuit::dsl::circuit::CellProgram,
    /// The named trace-column witness the program proves over.
    pub witness_values: std::collections::HashMap<String, Vec<BabyBear>>,
    /// The number of trace rows.
    pub num_rows: usize,
    /// The DSL program's public inputs (the in-circuit PI-commitment preimage).
    pub public_inputs: Vec<BabyBear>,
}

impl DslWitnessBundle {
    /// Project the re-provable DSL bundle from a retained [`crate::custom_proof_bind::BoundCustomProof`]
    /// (the dsl twin of [`CustomWitnessBundle::from_bound_custom_proof`]). Returns `None` when the
    /// bound proof was reconstructed from the on-wire artifact (no retained witness) — the
    /// re-exec-only rung, FAIL-CLOSED rather than fabricated.
    pub fn from_bound_custom_proof(
        bound: &crate::custom_proof_bind::BoundCustomProof,
    ) -> Option<Self> {
        Some(Self {
            program: bound.program.clone(),
            witness_values: bound.witness_values.clone()?,
            num_rows: bound.num_rows?,
            public_inputs: bound.public_inputs.clone(),
        })
    }

    /// **THE PRODUCTION PROJECTION (fail-closed off-wire)** — the dsl twin of
    /// `SovereignWitnessBundle::from_retained_authority`. The turn-build path RETAINS the
    /// Dfa predicate-transition material (program + trace witness + the `DfaProofWire`
    /// public inputs) at the site that PROVED the wire
    /// (`dregg_turn::executor::membership_verifier::prove_dfa_transition` holds exactly
    /// this); a wire-rehydrated turn retains nothing — the `DfaProofWire` carries only
    /// `(public_inputs, stark)` bytes, never the trace witness — so it projects `None`:
    /// the re-exec rung, FAIL-CLOSED rather than fabricated.
    pub fn from_retained_dsl(retained: Option<&DslWitnessBundle>) -> Option<Self> {
        retained.cloned()
    }
}

impl Clone for RotatedParticipantLeg {
    /// `Ir2BatchProof` (the p3 `BatchProof`) is `Serialize`/`Deserialize` but NOT
    /// `Clone`, so the leg cannot `#[derive(Clone)]`. Round-trip the proof through
    /// postcard to clone it (cheap relative to proving); the descriptor + PI vector
    /// clone directly. A downstream snapshot consumer (`app-framework`'s STARK-gated
    /// rehydration) needs an owned copy for its tamper-rejection teeth.
    fn clone(&self) -> Self {
        let proof_bytes =
            postcard::to_allocvec(&self.proof).expect("Ir2BatchProof serializes for clone");
        let proof =
            postcard::from_bytes(&proof_bytes).expect("Ir2BatchProof round-trips for clone");
        Self {
            proof,
            descriptor: self.descriptor.clone(),
            public_inputs: self.public_inputs.clone(),
            carrier_witness: self.carrier_witness.clone(),
        }
    }
}

impl RotatedParticipantLeg {
    /// Attach the prover-side custom sub-proof witness (the deployed custom-binding thread).
    /// Builder-style; returns `self` with [`RotatedParticipantLeg::carrier_witness`] set to the
    /// [`CarrierWitness::Custom`] variant. The chain prover reads it to mint the custom
    /// sub-proof leaf + segmented binding node for this turn.
    pub fn with_custom_witness(mut self, bundle: CustomWitnessBundle) -> Self {
        self.carrier_witness = Some(CarrierWitness::Custom(bundle));
        self
    }

    /// Attach a carrier witness of any variant (builder-style). ALL SEVEN carriers are
    /// deployed-wired (custom / factory / hatchery / sovereign / membership / dsl / bridge);
    /// a leg whose descriptor does not pin the carrier's claim slots is REFUSED by the fold
    /// arm's admission (fail-closed).
    pub fn with_carrier_witness(mut self, witness: CarrierWitness) -> Self {
        self.carrier_witness = Some(witness);
        self
    }

    /// The custom witness bundle, iff [`Self::carrier_witness`] carries the
    /// [`CarrierWitness::Custom`] variant — the migration accessor for pre-socket call sites
    /// (`leg.custom_witness` the field became `leg.custom_witness()` the projection).
    pub fn custom_witness(&self) -> Option<&CustomWitnessBundle> {
        self.carrier_witness
            .as_ref()
            .and_then(CarrierWitness::as_custom)
    }
}

impl CustomWitnessBundle {
    /// Build the prover-side re-provable bundle from a [`crate::custom_proof_bind::BoundCustomProof`]
    /// whose `witness_values` / `num_rows` are populated (the prover-side-only retained trace
    /// witness; a bundle reconstructed from the wire has `None` and cannot be folded).
    ///
    /// This is the RETENTION SEAM that graduates the custom binding from RE-EXEC-ONLY to REAL-FOLDED:
    /// the turn-build path proves the custom sub-proof (yielding a `BoundCustomProof`), and this
    /// projects its retained witness into the bundle the production custom-wide minter attaches to the
    /// leg — so the deployed chain prover folds the sub-proof into the recursion tree a PURE LIGHT
    /// CLIENT verifies.
    ///
    /// Returns `None` when the bound proof was reconstructed from the on-wire
    /// [`dregg_turn::CustomProgramProof`] (no retained witness): such a proof carries the off-AIR
    /// verify but cannot be folded — exactly the re-exec-only rung, fail-closed rather than fabricated.
    pub fn from_bound_custom_proof(
        bound: &crate::custom_proof_bind::BoundCustomProof,
    ) -> Option<Self> {
        Some(Self {
            program: bound.program.clone(),
            witness_values: bound.witness_values.clone()?,
            num_rows: bound.num_rows?,
            public_inputs: bound.public_inputs.clone(),
            app_root_binding: None,
            descriptor_state_leaf: None,
        })
    }

    /// Declare the app-root weld for this custom turn (the deployed keystone opt-in). Chaining
    /// `.with_app_root_binding(b)` routes the turn through
    /// [`crate::joint_turn_recursive::prove_custom_binding_node_app_root_segmented`] instead of the
    /// state node — the leg exposes `field[b.field_key]` and the fold forces the sub-proof's
    /// published root `R` to equal it. See the field docs on [`Self::app_root_binding`].
    pub fn with_app_root_binding(
        mut self,
        binding: dregg_circuit::effect_vm::custom_state_binding::AppRootBinding,
    ) -> Self {
        self.app_root_binding = Some(binding);
        self
    }
}

// NOTE (Bucket-F / PATH-PRESERVE Phase 5a): the rotated-leg MINTING recipe
// (`mint_rotated_participant_leg`) lives in `dregg-turn`
// (`turn/src/rotation_witness.rs`), NOT here. It drives `rotation_witness::produce`
// over `dregg_cell::Cell`s, and `dregg-circuit` cannot depend on `dregg-cell` /
// `dregg-turn` (both depend on `dregg-circuit` — a cycle). The circuit crate owns
// the LEAF DATA STRUCTURE (`RotatedParticipantLeg` / `DescriptorParticipant`), the
// host-admission verifier (`verify_descriptor_participant`), and the in-circuit
// leaf-wrap (`ivc_turn_chain::prove_descriptor_leaf_rotated_with_config`); the
// `Cell`→witness→leg minting is downstream in `dregg-turn`. The recursion consumers
// (lightclient / wasm / `circuit/tests/proof_economics.rs`) import the mint from
// `dregg_turn_prover::rotation_witness::mint_rotated_participant_leg`.

impl RotatedParticipantLeg {
    /// **THE ROTATED+UMEM WELDED LEG MINT (STAGED, VK-RISK-FREE) — the IVC half of the flag-day
    /// weld.** Like the plain rotated-leg mint (`dregg_turn::rotation_witness::
    /// mint_rotated_participant_leg`), but the leg's
    /// descriptor is the WELDED rotated+umem form
    /// ([`dregg_circuit::effect_vm_descriptors::weld_umem_into_rotated_descriptor`]): the rotated
    /// cohort proof PLUS the universal-memory reconciliation leg (the cohort `umemOp` over 7
    /// appended columns + the REAL [`UMemBoundaryWitness`]), proved in ONE leaf under the leaf-wrap
    /// config. The carried 46-PI vector is UNCHANGED (the weld adds no PIs), so
    /// [`old_root`](Self::old_root) / [`new_root`](Self::new_root) — the temporal binding the IVC
    /// chain fold reads — keep working over the welded leg. This is what resolves the seam the
    /// 0-PI cohort form could not: the umem leg now rides a descriptor that carries the IVC's
    /// `old_root`/`new_root` accessors.
    ///
    /// `umem_rows` are the single-domain width-7 cohort rows (`key · present · value ·
    /// prev_present · prev_value · prev_serial · guard`, the
    /// `dregg_turn::umem::UmemCohortProvingInputs::rows`); `umem_boundary` is that leg's REAL
    /// boundary; `domain` is its cohort domain (heap 1 / caps 2 / nullifiers 3). The downstream
    /// `dregg_turn` wrapper derives all three from the cell transition. STAGED: a welded descriptor
    /// BESIDE the deployed rotated registry; no VK bump, nothing on the live wire.
    #[allow(clippy::too_many_arguments)]
    pub fn mint_welded_from_block_witnesses(
        initial_state: &dregg_circuit::effect_vm::CellState,
        effects: &[dregg_circuit::effect_vm::Effect],
        before: &dregg_circuit::effect_vm::trace_rotated::RotatedBlockWitness,
        after: &dregg_circuit::effect_vm::trace_rotated::RotatedBlockWitness,
        umem_rows: &[Vec<BabyBear>],
        umem_boundary: &dregg_circuit::descriptor_ir2::UMemBoundaryWitness,
        domain: u32,
    ) -> Result<RotatedParticipantLeg, String> {
        use crate::ivc_turn_chain::ir2_leaf_wrap_config;
        use dregg_circuit::descriptor_ir2::{
            MemBoundaryWitness, parse_vm_descriptor2, prove_vm_descriptor2_for_config,
            verify_vm_descriptor2_with_config,
        };
        use dregg_circuit::effect_vm::trace_rotated::{
            empty_caveat_manifest, rotated_descriptor_name_for_effect, transfer_caveat_manifest,
        };
        use dregg_circuit::effect_vm_descriptors::{
            V3_STAGED_REGISTRY_TSV, weld_umem_into_rotated_descriptor,
            weld_umem_into_rotated_descriptor_cohort,
        };

        let lead = effects
            .first()
            .ok_or_else(|| "mint_welded: empty effect slice".to_string())?;
        let r24_name = rotated_descriptor_name_for_effect(lead)
            .ok_or_else(|| format!("mint_welded: effect {lead:?} is not a rotated R=24 member"))?;
        for e in &effects[1..] {
            if rotated_descriptor_name_for_effect(e) != Some(r24_name) {
                return Err("mint_welded: heterogeneous multi-effect turn (one welded leg)".into());
            }
        }
        let json = V3_STAGED_REGISTRY_TSV
            .lines()
            .find_map(|line| {
                let mut it = line.splitn(3, '\t');
                if it.next() == Some(r24_name) {
                    let _display = it.next();
                    it.next()
                } else {
                    None
                }
            })
            .ok_or_else(|| format!("mint_welded: '{r24_name}' not in V3_STAGED_REGISTRY_TSV"))?;
        let rotated_desc = parse_vm_descriptor2(json)
            .map_err(|e| format!("mint_welded: descriptor '{r24_name}' parse failed: {e}"))?;

        // WELD: the universal-memory leg INTO the rotated descriptor (keeps the 46 rotated PIs).
        // A single-domain leg that reconciles AT MOST ONE `(domain,key)` cell (the common case —
        // a `Transfer`'s lone Balance touch) routes through the COHORT single-row boundary AIR
        // (width 9 vs 38): the inter-row `Nodup` comparator is vacuous for one row and dropped, and
        // that lighter boundary instance is re-paid up the whole IVC aggregation tree. A
        // multi-address leg keeps the general boundary. The choice rides the descriptor (the table-7
        // sem), which is carried with the leg, so the verifier rebuilds the SAME AIR set.
        let single_row = umem_boundary.addrs.len() <= 1;
        let welded = if single_row {
            weld_umem_into_rotated_descriptor_cohort(&rotated_desc, domain)
        } else {
            weld_umem_into_rotated_descriptor(&rotated_desc, domain)
        };
        let base = rotated_desc.trace_width;

        let caveat = match effects {
            [dregg_circuit::effect_vm::Effect::Transfer { .. }] => transfer_caveat_manifest(),
            _ => empty_caveat_manifest(),
        };
        // The trace SHAPE follows the COMMITTED descriptor: a hardened `…-v1-avail` transfer/burn
        // member (the GAP #4 availability weld) demands the avail-padded geometry.
        let (rot_trace, dpis) =
            dregg_circuit::effect_vm::trace_rotated::generate_rotated_effect_vm_trace_avail(
                dregg_circuit::effect_vm::trace_rotated::avail_pad_for_descriptor_name(
                    &rotated_desc.name,
                ),
                initial_state,
                effects,
                before,
                after,
                &caveat,
            )
            .map_err(|e| format!("mint_welded: rotated trace generation failed: {e}"))?;

        // Assemble the welded base trace: inject the REAL umem rows (guard col 6 == 1) into the
        // appended 7 columns of the first rows (the umem-op gathering reads operands row-local).
        let real_umem_rows: Vec<&Vec<BabyBear>> = umem_rows
            .iter()
            .filter(|r| r.get(6).copied() == Some(BabyBear::ONE))
            .collect();
        if real_umem_rows.len() > rot_trace.len() {
            return Err(format!(
                "mint_welded: {} umem ops exceed rotated trace height {}",
                real_umem_rows.len(),
                rot_trace.len()
            ));
        }
        let mut welded_trace: Vec<Vec<BabyBear>> = Vec::with_capacity(rot_trace.len());
        for (ri, row) in rot_trace.iter().enumerate() {
            let mut wr = row.clone();
            wr.resize(base + 7, BabyBear::ZERO);
            if let Some(umem_row) = real_umem_rows.get(ri) {
                for (i, &v) in umem_row.iter().enumerate().take(7) {
                    wr[base + i] = v;
                }
            }
            welded_trace.push(wr);
        }

        let wrap_config = ir2_leaf_wrap_config();
        let proof = prove_vm_descriptor2_for_config(
            &welded,
            &welded_trace,
            &dpis,
            &MemBoundaryWitness::default(),
            &[],
            umem_boundary,
            &wrap_config,
        )
        .map_err(|e| format!("mint_welded: IR-v2 welded batch prove failed: {e}"))?;
        verify_vm_descriptor2_with_config(&welded, &proof, &dpis, &wrap_config)
            .map_err(|e| format!("mint_welded: minted welded proof self-verify failed: {e}"))?;

        Ok(RotatedParticipantLeg {
            proof,
            descriptor: welded,
            public_inputs: dpis,
            carrier_witness: None,
        })
    }
    /// **THE WIDE WELDED ROTATED+UMEM LEG (STAGED, VK-RISK-FREE) — the IVC half of the genuine flip
    /// precursor.** The WIDE (8-felt / ~124-bit faithful commit) twin of
    /// [`mint_welded_from_block_witnesses`](Self::mint_welded_from_block_witnesses): mints ONE leaf
    /// that proves BOTH the WIDE rotated cohort proof (the wide PI vector whose LAST 16 PIs are the
    /// 8-felt before/after commit anchors) AND the universal-memory reconciliation leg. It welds the
    /// umem leg onto the WIDE descriptor ([`weld_umem_into_wide_descriptor`]) — purely additive, so
    /// the 16 wide commit PIs ride through INTACT, keeping the ~124-bit commitment (no narrowing) —
    /// and the leg still carries the single-felt rotated `old_root`/`new_root` (PI 34/35) the IVC
    /// chain fold's temporal tooth binds, PLUS the 8-felt [`wide_old_root8`](Self::wide_old_root8) /
    /// [`wide_new_root8`](Self::wide_new_root8) the ~124-bit binding reads.
    ///
    /// SCOPE: the FULL single-domain wide cohort — any effect whose WIDE producer is SAT on the bare
    /// wide sovereign path (`generate_rotated_effect_vm_descriptor_and_trace_wide`, the SAME family
    /// dispatch the live SDK wide prover runs): the value/field families (transfer / burn / bridgeMint
    /// / setField / setFieldDyn) ride the heap domain; the grow-gate (note) + record-pin / lifecycle
    /// families ride when the caller threads their context. `before_nullifiers` is the note-spend
    /// grow-gate's BEFORE nullifier set; `refusal_fields` the refusal `fields_root` write witness;
    /// `cap_write` the cap-tree write witness (the cap-open weld) for the nonce-FREEZE cap-WRITE family
    /// (attenuate / revokeCapability — whose AFTER cap-root is an in-circuit cap-tree `map_op` write —
    /// and grantCap, the authority-only frozen base); all `None` for the value/field leads. A cap-WRITE
    /// lead carrying a map_op but no `cap_write` witness — or a heterogeneous / non-cohort slice — fails
    /// closed at the dispatcher (the cap-open weld never fabricates a post-cap-root). STAGED: a welded
    /// WIDE descriptor BESIDE the deployed wide registry; no VK bump, nothing on the wire.
    #[allow(clippy::too_many_arguments)]
    pub fn mint_welded_wide_from_block_witnesses(
        initial_state: &dregg_circuit::effect_vm::CellState,
        effects: &[dregg_circuit::effect_vm::Effect],
        before: &dregg_circuit::effect_vm::trace_rotated::RotatedBlockWitness,
        after: &dregg_circuit::effect_vm::trace_rotated::RotatedBlockWitness,
        umem_rows: &[Vec<BabyBear>],
        umem_boundary: &dregg_circuit::descriptor_ir2::UMemBoundaryWitness,
        domain: u32,
        before_nullifiers: Option<&[BabyBear]>,
        refusal_fields: Option<(
            &[dregg_circuit::openable_fields_root::ExactFieldsLeaf],
            [u8; 32],
        )>,
        cap_write: Option<&dregg_circuit::effect_vm::trace_rotated::CapWriteWideWitness>,
    ) -> Result<RotatedParticipantLeg, String> {
        use crate::ivc_turn_chain::ir2_leaf_wrap_config;
        use dregg_circuit::descriptor_ir2::{
            prove_vm_descriptor2_for_config, verify_vm_descriptor2_with_config,
        };
        use dregg_circuit::effect_vm::trace_rotated::{
            empty_caveat_manifest, generate_rotated_effect_vm_descriptor_and_trace_wide,
            transfer_caveat_manifest,
        };
        use dregg_circuit::effect_vm_descriptors::weld_umem_into_wide_descriptor;

        if effects.is_empty() {
            return Err("mint_welded_wide: empty effect slice".to_string());
        }

        // The shared full-cohort wide producer route (the live SDK wide prover's dispatch, lifted into
        // `dregg-circuit`): resolves the WIDE descriptor + lays the per-family trace / PI vector /
        // grow-gate `map_heaps` / (setFieldDyn-only) mem-boundary. Replaces the Transfer-only
        // transfer-shape leg this staged wide IVC leg used to be scoped to.
        let caveat = match effects {
            [dregg_circuit::effect_vm::Effect::Transfer { .. }] => transfer_caveat_manifest(),
            _ => empty_caveat_manifest(),
        };
        let (wide_desc, wide_trace, dpis, map_heaps, mem_boundary) =
            generate_rotated_effect_vm_descriptor_and_trace_wide(
                initial_state,
                effects,
                before,
                after,
                &caveat,
                before_nullifiers,
                refusal_fields,
                cap_write,
                // No BEFORE cell on this pure-circuit route — zero-pair membership-teeth sentinel.
                None,
            )
            .map_err(|e| format!("mint_welded_wide: wide producer dispatch failed: {e}"))?;

        // WELD: the universal-memory leg INTO the WIDE descriptor (keeps the 16 wide commit PIs).
        let welded = weld_umem_into_wide_descriptor(&wide_desc, domain);
        let base = wide_desc.trace_width;

        // Assemble the welded base trace: inject the REAL umem rows (guard col 6 == 1) into the
        // appended 7 columns of the first rows (the umem-op gathering reads operands row-local).
        let real_umem_rows: Vec<&Vec<BabyBear>> = umem_rows
            .iter()
            .filter(|r| r.get(6).copied() == Some(BabyBear::ONE))
            .collect();
        if real_umem_rows.len() > wide_trace.len() {
            return Err(format!(
                "mint_welded_wide: {} umem ops exceed wide trace height {}",
                real_umem_rows.len(),
                wide_trace.len()
            ));
        }
        let mut welded_trace: Vec<Vec<BabyBear>> = Vec::with_capacity(wide_trace.len());
        for (ri, row) in wide_trace.iter().enumerate() {
            let mut wr = row.clone();
            wr.resize(base + 7, BabyBear::ZERO);
            if let Some(umem_row) = real_umem_rows.get(ri) {
                for (i, &v) in umem_row.iter().enumerate().take(7) {
                    wr[base + i] = v;
                }
            }
            welded_trace.push(wr);
        }

        let wrap_config = ir2_leaf_wrap_config();
        let proof = prove_vm_descriptor2_for_config(
            &welded,
            &welded_trace,
            &dpis,
            &mem_boundary,
            &map_heaps,
            umem_boundary,
            &wrap_config,
        )
        .map_err(|e| format!("mint_welded_wide: IR-v2 welded wide batch prove failed: {e}"))?;
        verify_vm_descriptor2_with_config(&welded, &proof, &dpis, &wrap_config).map_err(|e| {
            format!("mint_welded_wide: minted welded wide proof self-verify failed: {e}")
        })?;

        Ok(RotatedParticipantLeg {
            proof,
            descriptor: welded,
            public_inputs: dpis,
            carrier_witness: None,
        })
    }

    /// **THE WIDE WELDED ROTATED+UMEM MULTI-DOMAIN LEG (STAGED, VK-RISK-FREE) — the last family
    /// tail.** The two-domain twin of
    /// [`mint_welded_wide_from_block_witnesses`](Self::mint_welded_wide_from_block_witnesses): mints
    /// ONE leaf proving BOTH the WIDE rotated cohort proof (the wide PI vector whose LAST 16 PIs are
    /// the 8-felt before/after commit anchors) AND the MULTI-DOMAIN universal-memory reconciliation
    /// leg (one guarded `umemOp` per touched domain). It welds the multi-domain umem leg onto the WIDE
    /// descriptor ([`weld_umem_multidomain_into_wide_descriptor`]) — purely additive, so the 16 wide
    /// commit PIs ride through INTACT (no narrowing) — and the leg carries `wide_old_root8`/
    /// `wide_new_root8` the ~124-bit binding reads.
    ///
    /// SCOPE: the NOTE/BRIDGE economic verbs (`NoteSpend` / `BridgeMint`) whose state touch spans TWO
    /// domains in one effect — a `nullifiers` freshness insert + a `heap` balance credit. `umem_rows`
    /// are the multi-domain cohort rows (width `6 + domains.len()`, the
    /// `dregg_turn::umem::UmemCohortMultiProvingInputs::rows`); `umem_boundary` is that leg's REAL
    /// boundary (touched addresses across BOTH domains); `domains` the per-op domain set in COLUMN
    /// order. `before_nullifiers` is the note-spend grow-gate's BEFORE nullifier set (`None` for
    /// BridgeMint, which rides the transfer-shape wide producer). The cross-DOMAIN economic invariant
    /// (credit == spent/minted value) rides the effect's rotated AIR, NOT the memory reconciliation —
    /// the same division as the narrow multi-domain cohort. A heterogeneous / non-cohort slice fails
    /// closed at the dispatcher. STAGED: a welded WIDE descriptor BESIDE the deployed wide registry; no
    /// VK bump, nothing on the wire.
    #[allow(clippy::too_many_arguments)]
    pub fn mint_welded_wide_multidomain_from_block_witnesses(
        initial_state: &dregg_circuit::effect_vm::CellState,
        effects: &[dregg_circuit::effect_vm::Effect],
        before: &dregg_circuit::effect_vm::trace_rotated::RotatedBlockWitness,
        after: &dregg_circuit::effect_vm::trace_rotated::RotatedBlockWitness,
        umem_rows: &[Vec<BabyBear>],
        umem_boundary: &dregg_circuit::descriptor_ir2::UMemBoundaryWitness,
        domains: &[u32],
        before_nullifiers: Option<&[BabyBear]>,
    ) -> Result<RotatedParticipantLeg, String> {
        use crate::ivc_turn_chain::ir2_leaf_wrap_config;
        use dregg_circuit::descriptor_ir2::{
            prove_vm_descriptor2_for_config, verify_vm_descriptor2_with_config,
        };
        use dregg_circuit::effect_vm::trace_rotated::{
            empty_caveat_manifest, generate_rotated_effect_vm_descriptor_and_trace_wide,
            transfer_caveat_manifest,
        };
        use dregg_circuit::effect_vm_descriptors::weld_umem_multidomain_into_wide_descriptor;

        if effects.is_empty() {
            return Err("mint_welded_wide_multidomain: empty effect slice".to_string());
        }
        if domains.len() < 2 {
            return Err(format!(
                "mint_welded_wide_multidomain: the multi-domain weld needs >= 2 domains, got {} (a \
                 single-domain leg uses mint_welded_wide_from_block_witnesses)",
                domains.len()
            ));
        }

        // The shared full-cohort wide producer route — resolves the WIDE descriptor + lays the
        // per-family trace / PI vector / grow-gate `map_heaps`. NoteSpend threads `before_nullifiers`
        // (the grow-gate accumulator); BridgeMint rides the transfer-shape producer (None). No
        // cap-write witness on the economic-verb path.
        let caveat = match effects {
            [dregg_circuit::effect_vm::Effect::Transfer { .. }] => transfer_caveat_manifest(),
            _ => empty_caveat_manifest(),
        };
        let (wide_desc, wide_trace, dpis, map_heaps, mem_boundary) =
            generate_rotated_effect_vm_descriptor_and_trace_wide(
                initial_state,
                effects,
                before,
                after,
                &caveat,
                before_nullifiers,
                None,
                None,
                // No BEFORE cell on this pure-circuit route — zero-pair membership-teeth sentinel.
                None,
            )
            .map_err(|e| {
                format!("mint_welded_wide_multidomain: wide producer dispatch failed: {e}")
            })?;

        // WELD: the MULTI-DOMAIN universal-memory leg INTO the WIDE descriptor (keeps the 16 wide
        // commit PIs).
        let welded = weld_umem_multidomain_into_wide_descriptor(&wide_desc, domains);
        let base = wide_desc.trace_width;
        let umem_cols = 6 + domains.len();

        // Assemble the welded base trace: inject the REAL umem rows (a row is REAL if ANY per-domain
        // guard col `6 .. 6 + domains.len()` is 1) into the appended `6 + domains.len()` columns of
        // the first rows (the umem-op gathering reads operands row-local; each row fires the ONE
        // umemOp whose guard it sets).
        let real_umem_rows: Vec<&Vec<BabyBear>> = umem_rows
            .iter()
            .filter(|r| (6..umem_cols).any(|c| r.get(c).copied() == Some(BabyBear::ONE)))
            .collect();
        if real_umem_rows.len() > wide_trace.len() {
            return Err(format!(
                "mint_welded_wide_multidomain: {} umem ops exceed wide trace height {}",
                real_umem_rows.len(),
                wide_trace.len()
            ));
        }
        let mut welded_trace: Vec<Vec<BabyBear>> = Vec::with_capacity(wide_trace.len());
        for (ri, row) in wide_trace.iter().enumerate() {
            let mut wr = row.clone();
            wr.resize(base + umem_cols, BabyBear::ZERO);
            if let Some(umem_row) = real_umem_rows.get(ri) {
                for (i, &v) in umem_row.iter().enumerate().take(umem_cols) {
                    wr[base + i] = v;
                }
            }
            welded_trace.push(wr);
        }

        let wrap_config = ir2_leaf_wrap_config();
        let proof = prove_vm_descriptor2_for_config(
            &welded,
            &welded_trace,
            &dpis,
            &mem_boundary,
            &map_heaps,
            umem_boundary,
            &wrap_config,
        )
        .map_err(|e| {
            format!("mint_welded_wide_multidomain: IR-v2 welded wide batch prove failed: {e}")
        })?;
        verify_vm_descriptor2_with_config(&welded, &proof, &dpis, &wrap_config).map_err(|e| {
            format!(
                "mint_welded_wide_multidomain: minted welded wide proof self-verify failed: {e}"
            )
        })?;

        Ok(RotatedParticipantLeg {
            proof,
            descriptor: welded,
            public_inputs: dpis,
            carrier_witness: None,
        })
    }

    /// **THE PRODUCTION CUSTOM-WIDE LEG MINT — graduates the custom binding from RE-EXEC-ONLY to
    /// REAL-FOLDED.** Mint the `customVmDescriptor2R24` WIDE leg for an [`Effect::Custom`] turn AND
    /// ATTACH the prover-side re-provable [`CustomWitnessBundle`], so the deployed chain prover
    /// ([`crate::ivc_turn_chain::prove_chain_core_rotated`]) takes the custom-binding fold branch:
    /// it mints the DUAL-EXPOSE leg leaf (segment ++ the claimed `custom_proof_commitment` at PI
    /// 46..49) and folds it against the RE-PROVEN custom sub-proof leaf through
    /// [`crate::joint_turn_recursive::prove_custom_binding_node_segmented`], `connect`ing the leg's
    /// claimed commitment to the sub-proof's GENUINE in-circuit commitment INSIDE the recursion tree
    /// a PURE LIGHT CLIENT folds. A forged claim no verifying sub-proof of the bundle's PIs backs is
    /// UNSAT ⇒ no root ⇒ the light client never receives a verifying artifact.
    ///
    /// This is the PRODUCTION twin of the test-only `with_custom_witness` wiring: the leg's claimed
    /// commitment rides the `effects` (the `Effect::Custom.proof_commitment`, set at turn-build to
    /// `BoundCustomProof::proof_commitment()`), and `bundle` is the retained re-provable witness
    /// (build it via [`CustomWitnessBundle::from_bound_custom_proof`] over the SAME bound proof). The
    /// downstream `dregg_turn_prover::rotation_witness::mint_custom_wide_rotated_participant_leg` wrapper
    /// feeds this the `Cell`-derived block witnesses.
    ///
    /// Fails closed if the lead effect is not [`Effect::Custom`] (the wide producer rejects a
    /// non-Custom lead on the custom-row geometry) or if the minted leg does not publish the
    /// commitment slice at PI 46..49 (a malformed custom leg the binding node could not bind).
    pub fn mint_custom_wide_from_block_witnesses(
        initial_state: &dregg_circuit::effect_vm::CellState,
        effects: &[dregg_circuit::effect_vm::Effect],
        before: &dregg_circuit::effect_vm::trace_rotated::RotatedBlockWitness,
        after: &dregg_circuit::effect_vm::trace_rotated::RotatedBlockWitness,
        bundle: impl Into<CarrierWitness>,
    ) -> Result<RotatedParticipantLeg, String> {
        use crate::ivc_turn_chain::ir2_leaf_wrap_config;
        use crate::joint_turn_recursive::{CUSTOM_COMMIT_LEN, CUSTOM_COMMIT_PI_LO};
        use dregg_circuit::descriptor_ir2::{
            UMemBoundaryWitness, prove_vm_descriptor2_for_config, verify_vm_descriptor2_with_config,
        };
        use dregg_circuit::effect_vm::Effect;
        use dregg_circuit::effect_vm::trace_rotated::{
            empty_caveat_manifest, generate_rotated_effect_vm_descriptor_and_trace_wide,
        };
        let commit_pi_hi = CUSTOM_COMMIT_PI_LO + CUSTOM_COMMIT_LEN;

        if !matches!(effects.first(), Some(Effect::Custom { .. })) {
            return Err(format!(
                "mint_custom_wide: lead effect must be Effect::Custom (got {:?})",
                effects.first()
            ));
        }

        let (desc, trace, dpis, map_heaps, mb) =
            generate_rotated_effect_vm_descriptor_and_trace_wide(
                initial_state,
                effects,
                before,
                after,
                &empty_caveat_manifest(),
                None,
                None,
                None,
                // Custom lead — the committed custom row carries no membership-teeth tail
                // (its COMMIT teeth are laid by `generate_rotated_custom_wide` itself).
                None,
            )
            .map_err(|e| format!("mint_custom_wide: wide custom dispatch failed: {e}"))?;

        // THE PROOF-BIND COMMITMENT VERSION BOUNDARY (flag-day v2): refuse minting against a
        // registry descriptor still carrying the RETIRED 4-felt exposure (typed, never widened).
        dregg_circuit::effect_vm_descriptors::require_custom_carrier_vk8(&desc)
            .map_err(|e| format!("mint_custom_wide: commitment version boundary: {e}"))?;

        if dpis.len() < commit_pi_hi {
            return Err(format!(
                "mint_custom_wide: custom leg PI vector must carry the 8-felt commitment slice \
                 at {CUSTOM_COMMIT_PI_LO}..{commit_pi_hi} (got {})",
                dpis.len()
            ));
        }

        let config = ir2_leaf_wrap_config();
        let proof = prove_vm_descriptor2_for_config(
            &desc,
            &trace,
            &dpis,
            &mb,
            &map_heaps,
            &UMemBoundaryWitness::default(),
            &config,
        )
        .map_err(|e| format!("mint_custom_wide: IR-v2 wide custom batch prove failed: {e}"))?;
        verify_vm_descriptor2_with_config(&desc, &proof, &dpis, &config).map_err(|e| {
            format!("mint_custom_wide: minted wide custom proof self-verify failed: {e}")
        })?;

        Ok(RotatedParticipantLeg {
            proof,
            descriptor: desc,
            public_inputs: dpis,
            carrier_witness: Some(bundle.into()),
        })
    }

    /// The rotated OLD-state commitment (PI 34 — the row-0 before-block `state_commit`).
    pub fn old_root(&self) -> BabyBear {
        self.public_inputs[dregg_circuit::effect_vm::trace_rotated::V1_PI_COUNT]
    }

    /// **THE WIDE 8-FELT OLD-state commitment** (the BEFORE 8-felt commit at the leg's
    /// PIs `[n-16 .. n-8)` — the ~124-bit faithful anchor a WIDE / wide-welded leg publishes).
    /// `None` for a leg whose PI vector is too short to carry the wide tail (a narrow leg).
    ///
    /// ⚑ **THE GUARD WAS `n < 16` AND THE DOC ABOVE WAS FALSE.** Every narrow leg in the corpus
    /// carries far more than 16 PIs (the rotated prefix is 46, the deployed narrow transfer 50), so
    /// this returned `Some(...)` for ALL of them — a slice of ordinary rotated PIs, handed back as a
    /// ~124-bit faithful anchor. It is the SAME discriminator `leg_is_wide_anchored` already used
    /// (`len >= WIDE_PI_COUNT`), which is why the FOLD was never fooled: `turn_anchors8` asks that
    /// predicate first and broadcasts the 1-felt rotated root for a narrow leg. Everything that
    /// called these accessors DIRECTLY was. Measured 2026-07-29 on
    /// `ivc_turn_chain_rotated_umem_welded`, whose three tests chained a narrow welded leg on
    /// `wide_old_root8()[0] == 0` (PI 34, not an anchor) against `wide_new_root8()[0]` (PI 42).
    /// Refusing is the only honest answer: a narrow leg has no 8-felt anchor to return.
    ///
    /// ⚠ THE THRESHOLD IS `ROT_PI_COUNT + 16` (55), NOT `WIDE_PI_COUNT` (59). 55 is exactly the
    /// shape these accessors read — the rotated prefix plus the 16-felt anchor tail — and 20 of the
    /// committed wide members sit at 55/56/58 because they carry NO `DFA_RC_LEN` rc block (every
    /// cap-open member, `supplyMint`, `transferCapOpenTB`). `WIDE_PI_COUNT` would refuse all of
    /// them while they genuinely publish the anchors. Every narrow leg (rotated 39, grow-gate 40,
    /// cap-open-tb narrow 42, custom 43, the deployed narrow transfer 43) is still below it.
    /// (Those numbers were 62/63/65 and 46/47/49/50 until the 2026-08-07 seven-slot PI
    /// compaction took `V1_PI_COUNT` 42 → 35; every one of them moved by −7 together, which is
    /// why the comparison still holds.)
    /// `leg_is_wide_anchored` keys the FOLD on `WIDE_PI_COUNT`, so those 20 members are treated as
    /// narrow THERE and get their 1-felt root broadcast — a separate disagreement, named here and
    /// not silently resolved by moving this number to match it.
    pub fn wide_old_root8(&self) -> Option<[BabyBear; 8]> {
        let n = self.public_inputs.len();
        if n < ROTATED_WIDE_ANCHORED_PI_MIN {
            return None;
        }
        self.public_inputs[n - 16..n - 8].try_into().ok()
    }

    /// **THE WIDE 8-FELT NEW-state commitment** (the AFTER 8-felt commit at the leg's
    /// PIs `[n-8 .. n)` — the ~124-bit faithful anchor). `None` for a narrow leg.
    pub fn wide_new_root8(&self) -> Option<[BabyBear; 8]> {
        let n = self.public_inputs.len();
        if n < ROTATED_WIDE_ANCHORED_PI_MIN {
            return None;
        }
        self.public_inputs[n - 8..n].try_into().ok()
    }
    /// The rotated NEW-state commitment (PI 35 — the last-row after-block `state_commit`).
    /// This is the next finalized turn's required `old_root` (the temporal binding).
    pub fn new_root(&self) -> BabyBear {
        self.public_inputs[dregg_circuit::effect_vm::trace_rotated::V1_PI_COUNT + 1]
    }
}

impl DescriptorParticipant {
    /// Construct a participant from its mandatory ROTATED leg (Bucket-F: the rotated leaf is the
    /// sole leg the recursion core folds).
    pub fn rotated(rotated: RotatedParticipantLeg) -> Self {
        Self { rotated }
    }
}

/// Verify one descriptor participant's ROTATED per-cell proof standalone (host admission), then
/// resolve which cohort the leg attests. The rotated `Ir2BatchProof` is verified against its
/// carried `EffectVmDescriptor2` via [`dregg_circuit::descriptor_ir2::verify_vm_descriptor2`] (the
/// rotated analogue of the v1 `verify_vm_descriptor` selector-bind); the descriptor's `name`
/// is then mapped back to its effect selector through the staged R=24 registry. Returns the
/// bound selector. This is the Bucket-F replacement for the v1 `EffectVmP3Proof` selector-bind:
/// host admission no longer reads a v1 leg.
///
/// Soundness note: as in the v1 path, this host gate is an ADMISSION discipline, not the
/// soundness boundary — the rotated leaf is RE-VERIFIED in-circuit at the wrap
/// ([`crate::ivc_turn_chain::prove_descriptor_leaf_rotated_with_config`]). A leg whose proof
/// does not verify against its descriptor, or whose descriptor is not a registry member, is
/// rejected here.
pub fn verify_descriptor_participant(p: &DescriptorParticipant) -> Result<usize, String> {
    use crate::ivc_turn_chain::ir2_leaf_wrap_config;
    use dregg_circuit::descriptor_ir2::verify_vm_descriptor2_with_config;

    let leg = &p.rotated;
    // (1) The rotated proof must verify against its carried descriptor over the carried PI
    //     vector (full standalone re-verify of the IR-v2 multi-table batch). The leg's proof is
    //     minted under the leaf-wrap config (recursion-config TYPE, `ir2_config`'s FRI knobs —
    //     `dregg_turn_prover::rotation_witness::mint_rotated_participant_leg`), so it must be verified under THAT
    //     config, not the default `ir2_config()` (which is the `DreggStarkConfig` type).
    verify_vm_descriptor2_with_config(
        &leg.descriptor,
        &leg.proof,
        &leg.public_inputs,
        &ir2_leaf_wrap_config(),
    )
    .map_err(|e| {
        format!("rotated descriptor participant proof failed standalone verification: {e}")
    })?;
    // (2) Map the descriptor's wire name back to its effect selector through the staged
    //     R=24 registry (the cohort the leg is bound to).
    rotated_descriptor_selector(&leg.descriptor.name).ok_or_else(|| {
        format!(
            "rotated descriptor participant carries descriptor '{}' which is not a known \
             R=24 cohort member",
            leg.descriptor.name
        )
    })
}

/// Map a rotated descriptor's wire name (e.g. `"transferVmDescriptor2R24"`) back to the effect
/// selector whose cohort it proves. Scans the `CUTOVER_READY_SELECTORS` and matches each
/// selector's rotated descriptor name against `name`. Returns `None` for a name no graduated
/// selector resolves to (a non-cohort or unknown descriptor).
///
/// **The two-name subtlety (Bucket-F fix).** The registry TSV row is
/// `WIRE-name \t DISPLAY-name \t json`, and the parsed descriptor's `.name` is the *DISPLAY*
/// name (the json's internal `"name"` field, e.g. `"dregg-effectvm-transfer-v1-rot24-v3-staged"`),
/// NOT the wire name [`rotated_descriptor_name`] returns (`"transferVmDescriptor2R24"`). So this
/// maps a selector → its wire name → the TSV row → that row's DISPLAY name, and compares THAT to
/// the leg's `desc.name`. (The earlier version compared the wire name directly to `desc.name` and
/// therefore rejected every valid rotated leg.)
///
/// **The map reads the WIDE registry** — the registry participant legs are actually minted from
/// (`dregg_turn_prover::rotation_witness::mint_rotated_participant_leg` dispatches the WIDE producer, and
/// the node retention path encodes/decodes wide). It previously read the bare 1-felt
/// `V3_STAGED_REGISTRY_TSV`, which happened to work only because 52 of the 57 shared members carry
/// byte-identical DISPLAY names in both registries — the 5 heap-open/fields-open flip members
/// (`createCell`/`heapWrite`/`noteCreate`/`noteSpend`/`refusal`) have DIFFERENT wide display names,
/// so their (wide-minted) legs were silently inadmissible through this gate.
fn rotated_descriptor_selector(name: &str) -> Option<usize> {
    use dregg_circuit::effect_vm::columns::sel;
    use dregg_circuit::effect_vm::trace_rotated::{
        rotated_descriptor_name, rotated_set_field_descriptor_name,
    };
    use dregg_circuit::effect_vm_descriptors::WIDE_REGISTRY_STAGED_TSV;
    // The DISPLAY name (field 1) of the registry row keyed by a WIRE name: the json-internal
    // `name` the parsed descriptor carries.
    let display_of = |wire: &str| {
        WIDE_REGISTRY_STAGED_TSV.lines().find_map(|line| {
            let mut it = line.splitn(3, '\t');
            if it.next() == Some(wire) {
                it.next()
            } else {
                None
            }
        })
    };
    for &s in dregg_circuit::proof_forest::CUTOVER_READY_SELECTORS {
        // SetField is keyed PER SLOT (`setFieldVmDescriptor2-{k}R24`, the names the wide producer
        // resolves through `rotated_set_field_descriptor_name`); the selector has no single wire
        // name, so its rows are found slot by slot.
        if s == sel::SET_FIELD {
            if (0u32..8).any(|k| display_of(rotated_set_field_descriptor_name(k)) == Some(name)) {
                return Some(s);
            }
            continue;
        }
        let wire = match rotated_descriptor_name(s) {
            Some(w) => w,
            None => continue,
        };
        if display_of(wire) == Some(name) {
            return Some(s);
        }
    }
    None
}

#[cfg(test)]
mod set_field_selector_tests {
    use super::rotated_descriptor_selector;
    use dregg_circuit::effect_vm::columns::sel;
    use dregg_circuit::effect_vm::trace_rotated::rotated_set_field_descriptor_name;
    use dregg_circuit::effect_vm_descriptors::WIDE_REGISTRY_STAGED_TSV;

    /// Every per-slot setField member's display name resolves to SET_FIELD, and nothing else does.
    #[test]
    fn every_setfield_slot_member_resolves_to_set_field() {
        for k in 0u32..8 {
            let wire = rotated_set_field_descriptor_name(k);
            let display = WIDE_REGISTRY_STAGED_TSV
                .lines()
                .find_map(|line| {
                    let mut it = line.splitn(3, '\t');
                    (it.next() == Some(wire)).then(|| it.next()).flatten()
                })
                .unwrap_or_else(|| panic!("{wire} is in the WIDE registry"));
            assert_eq!(
                rotated_descriptor_selector(display),
                Some(sel::SET_FIELD),
                "{wire}"
            );
        }
        assert_eq!(rotated_descriptor_selector("not-a-member"), None);
    }
}

// ============================================================================
// Errors
// ============================================================================

/// Why an in-circuit binding-node aggregation (or a leaf-adapter mint) failed — the shared
/// error type of [`crate::joint_turn_recursive`]'s `prove_*_binding_node*` fold-wires and the
/// `*_leaf_adapter` modules. (The joint-turn-fold-specific variants died with the joint layer —
/// E9, see the module header.)
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum JointAggError {
    /// The aggregation STARK proof failed to verify (or a combine/expose precondition failed).
    AggregationProofInvalid {
        /// The verification error.
        reason: String,
    },
}

impl core::fmt::Display for JointAggError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            JointAggError::AggregationProofInvalid { reason } => {
                write!(f, "aggregation proof invalid: {reason}")
            }
        }
    }
}

impl std::error::Error for JointAggError {}
