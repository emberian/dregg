//! Cross-cell joint-turn aggregation: ONE proof binding N per-cell whole-turn
//! proofs of a SINGLE shared turn (the Silver -> Gold step).
//!
//! ## What this is, and how it differs from `proof_forest`
//!
//! [`proof_forest`](dregg_circuit::proof_forest) links per-step proofs *sequentially*
//! inside one cell (`prev.NEW_COMMIT == next.OLD_COMMIT`). That is the
//! happened-before chain *within* a cell's history. It explicitly does **not**
//! do cross-cell binding (its own docs: "no cross-cell `Σδ = 0` family
//! binding").
//!
//! This module does the **orthogonal** thing the metatheory calls the
//! *hyperedge* / `SharedTurnId` pullback (`Dregg2.Spec.JointViaHyper`,
//! `Dregg2.Hyperedge`): take 2+ per-cell whole-turn proofs that all claim to be
//! participants of the **same** turn, and produce ONE aggregated proof that
//! verifies them together **and** binds their shared turn identity (CG-2 of the
//! hyperedge: every leg agrees on `tid`). Per-cell soundness alone cannot supply
//! this — two individually-valid proofs from *different* turns must be rejected.
//! That rejection is exactly the cross-cell binding's load-bearing content.
//!
//! ## The aggregation AIR
//!
//! [`JointTurnAggregationAir`] is a uni-STARK AIR over a width-4 trace, one row
//! per participating cell:
//!
//! - col 0: `shared_turn_id`  — the turn identity this cell's proof attests
//!   (the `TURN_HASH` public input, projected to one felt). The wide-pullback
//!   apex: **every row must carry the same value** (CG-2).
//! - col 1: `cell_commit`     — this cell's post-state commitment (`NEW_COMMIT`
//!   position 0), the per-cell content folded into the bundle digest.
//! - col 2: `acc_in`          — commitment hash-chain state before this row.
//! - col 3: `acc_out = hash_4_to_1([acc_in, shared_turn_id, cell_commit, idx])`
//!   — the running bundle digest.
//!
//! Public inputs `[shared_turn_id, initial_acc(=0), final_acc]`.
//!
//! Constraints:
//!   1. (CG-2, the cross-cell binding) **every** row's `shared_turn_id` equals
//!      the published `shared_turn_id` public input.  ← rejects mismatched turns
//!   2. first row `acc_in == initial_acc (== 0)`.
//!   3. last row `acc_out == final_acc`.
//!   4. chain continuity `acc_out[i] == acc_in[i+1]`.
//!
//! Constraint 1 is the tooth: a bundle whose cells disagree on the turn id (or
//! disagree with the published id) is UNSAT, even when every per-cell proof is
//! individually valid. That is precisely "validity != joint membership" — the
//! `SharedTurnId` pullback enforced at the apex.
//!
//! ## The recursive (Gold) binding
//!
//! [`JointTurnAggregationAir`] binds the shared-turn-id agreement (CG-2) + the commitment
//! digest over the N descriptor participants. Under the `recursion` feature it is wrapped in
//! ONE recursive in-circuit STARK layer via the emberian `plonky3-recursion` fork (driven by
//! [`crate::joint_turn_recursive`]), so the verifier checks a single succinct recursive proof
//! instead of re-running the aggregation prover. Each per-cell leaf is the ROTATED multi-table
//! `Ir2BatchProof` ([`DescriptorParticipant`]), verified in-circuit at the wrap.

use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_baby_bear::BabyBear as P3BabyBear;
use p3_field::PrimeCharacteristicRing;
use p3_matrix::dense::RowMajorMatrix;

use dregg_circuit::effect_vm::pi;
use dregg_circuit::field::BabyBear;
use dregg_circuit::plonky3_prover::to_p3;
use dregg_circuit::poseidon2::hash_4_to_1;

// ============================================================================
// DESCRIPTOR-BACKED PARTICIPANT — the per-cell leaf the recursion/aggregation cores fold.
// ============================================================================
//
// The joint-turn consumer's per-cell admission is the verified-by-construction ROTATED
// multi-table IR-v2 leaf: a descriptor participant carries an `Ir2BatchProof` over its
// rotated R=24 cohort descriptor, verified SELECTOR-BOUND through the descriptor verifier
// (the Lean `selectorGate s` tooth makes a sound proof verify under EXACTLY ONE selector —
// the differential harness's `descriptor_proof_binds_to_its_selector`). The CG-2
// shared-turn-id binding and the bundle-digest aggregation read PI projections off the
// rotated leg's prefix, so the cross-cell tooth holds identically.

/// A single cell's whole-turn ROTATED-DESCRIPTOR proof as a joint-turn participant. The leaf the
/// recursion path folds is the ROTATED multi-table `Ir2BatchProof` (the [`RotatedParticipantLeg`]),
/// MANDATORY — the participant carries exactly one rotated leg. Host admission
/// ([`verify_descriptor_participant`]) and the PI projections the aggregator reads
/// ([`pi::TURN_HASH_BASE`], [`pi::NEW_COMMIT_BASE`]) read the rotated leg's PI prefix (the
/// rotated 38-PI vector carries the v1 prefix `[0..34)` unchanged — `trace_rotated.rs:233`).
///
/// This whole descriptor-participant surface is `recursion`-gated: it feeds the recursion/aggregation
/// cores ([`crate::ivc_turn_chain`] / [`crate::joint_turn_recursive`]), which compile only under
/// `recursion`.
pub struct DescriptorParticipant {
    /// THE ROTATED LEG (Bucket-F mandatory leaf). The recursion cores
    /// ([`crate::ivc_turn_chain::prove_chain_core_rotated`] /
    /// [`crate::joint_turn_recursive::prove_joint_core_rotated`]) mint the in-circuit leaf from
    /// this rotated multi-table `Ir2BatchProof` via
    /// [`crate::ivc_turn_chain::prove_descriptor_leaf_rotated_with_config`]. All PI projections
    /// read its `public_inputs` prefix. `serde`-free (proofs are not serialized on this struct).
    pub rotated: RotatedParticipantLeg,
}

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
    /// checks the carrier claim off-AIR; the light-client fold does not witness it). This is
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
///   checked by a re-executing validator, never fabricated for the light client.
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
    /// FOLD-WIRED (the 7th, LAST carrier): the bridge carrier's re-provable witness — the
    /// REAL foreign note-spend witness (per the carrier-deployment spec: folding the
    /// binding-only `bridge_action_air` alone is NOT the sound deployed path — a prover-chosen
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
}

/// FOLD-WIRED (the 7th carrier) bridge-carrier bundle — the prover-side inputs
/// [`crate::note_spend_leaf_adapter::prove_note_spend_leaf_with_claim`] consumes: the REAL
/// foreign note-spend witness (spending key, 28-limb commitment preimage, Merkle path) — the
/// G2 backing the carrier-deployment spec mandates. Folding the binding-only
/// `bridge_action_air` was REFUSED as the backing (a prover-chosen tuple, no membership / no
/// key knowledge — the vacuous connect the fail-open law forbids); this bundle re-proves the
/// REAL spend STARK, whose leaf exposes the FELT-domain mint identity
/// (`note_spend_mint_hash_felt`, in-AIR-recomputed at claim lane 6) the deployed leg's
/// mint-hash PI (46, `mintV3BridgeHash`) connects to.
#[derive(Clone)]
pub struct BridgeWitnessBundle {
    /// The REAL note-spend witness (the SAME `NoteSpendingWitness` the off-AIR
    /// `verify_note_spend_dsl_full` path proves).
    pub note_spend: dregg_circuit::note_spending_air::NoteSpendingWitness,
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
        note_spend: &dregg_circuit::note_spending_air::NoteSpendingWitness,
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
        retained: Option<&dregg_circuit::note_spending_air::NoteSpendingWitness>,
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
    /// minted by [`crate::custom_proof_bind::prove_custom_program`] (which retains the trace witness).
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
        })
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
// `dregg_turn::rotation_witness::mint_rotated_participant_leg`.

impl RotatedParticipantLeg {
    /// Build a [`RotatedParticipantLeg`] from already-produced rotated block witnesses
    /// (the `before`/`after` `(pre_limbs, iroot)` pairs `rotation_witness::produce` yields)
    /// — the PURE-CIRCUIT core of the rotated-leg mint, with NO `dregg-cell` / `dregg-turn`
    /// dependency. The downstream `dregg_turn::rotation_witness::mint_rotated_participant_leg`
    /// wrapper feeds this the `Cell`-derived witnesses.
    ///
    /// `turn_id`, when `Some`, overrides the `TURN_HASH` slot of the carried PI prefix (the
    /// joint aggregator's shared-turn-id projection) — pass it for joint-turn participants that
    /// must agree on a shared id; `None` lets the carried hash stand (whole-chain turns).
    ///
    /// Fails closed if the turn's effect is not a single rotated R=24 cohort member (the
    /// generator rejects a non-cohort / empty / heterogeneous slice).
    pub fn mint_from_block_witnesses(
        initial_state: &dregg_circuit::effect_vm::CellState,
        effects: &[dregg_circuit::effect_vm::Effect],
        before: &dregg_circuit::effect_vm::trace_rotated::RotatedBlockWitness,
        after: &dregg_circuit::effect_vm::trace_rotated::RotatedBlockWitness,
        turn_id: Option<BabyBear>,
    ) -> Result<RotatedParticipantLeg, String> {
        use crate::ivc_turn_chain::ir2_leaf_wrap_config;
        use dregg_circuit::descriptor_ir2::{
            UMemBoundaryWitness, prove_vm_descriptor2_for_config, verify_vm_descriptor2_with_config,
        };
        use dregg_circuit::effect_vm::trace_rotated::{
            empty_caveat_manifest, generate_rotated_effect_vm_descriptor_and_trace_wide,
            transfer_caveat_manifest,
        };

        // H0 DEPLOYED-WIDE FLIP: the deployed-default leaf is now the WIDE (8-felt / ~124-bit
        // faithful commit) form. Previously this minted the narrow `*R24` descriptor (PI 46) whose
        // sole state anchor was the single rotated commit felt (PI 42/43, ~31-bit-birthday under a
        // whole-history fold). It now mints the wide twin via the SAME full-cohort dispatch the live
        // SDK wide prover runs (`generate_rotated_effect_vm_descriptor_and_trace_wide`): a 62-PI
        // vector whose last 16 PIs are the genuine 8-felt before/after commit anchors. The
        // aggregation reads them through [`crate::ivc_turn_chain::turn_anchors8`] /
        // [`leg_is_wide_anchored`] (now PI-length-keyed), so the whole-history genesis/final/continuity
        // all bind the ~124-bit anchor.
        //
        // The value/field/create cohort rides the bare wide producer with NO special witnesses
        // (`None` for the note-spend grow-gate nullifiers / refusal fields / cap-write tree). An
        // effect that needs one of those (note-spend / refusal / the cap-WRITE attenuate family) is
        // NOT served by this simple recipe — it routes through the dedicated wide minters
        // (`mint_welded_wide_*` / `mint_custom_wide_*`); here it fails closed at the wide dispatcher
        // rather than minting a 1-felt-anchored leg.
        if effects.is_empty() {
            return Err("mint_rotated_participant_leg: empty effect slice".to_string());
        }
        let caveat = match effects {
            [dregg_circuit::effect_vm::Effect::Transfer { .. }] => transfer_caveat_manifest(),
            _ => empty_caveat_manifest(),
        };
        let (wide_desc, wide_trace, mut dpis, map_heaps, mem_boundary) =
            generate_rotated_effect_vm_descriptor_and_trace_wide(
                initial_state,
                effects,
                before,
                after,
                &caveat,
                None,
                None,
                None,
                // Pure-circuit core: no BEFORE cell in hand — the committed transfer row's
                // membership-teeth tail fills the ZERO pair (the no-caveat sentinel). The
                // `dregg_turn` recipe wrapper threads the cell-derived pair.
                None,
            )
            .map_err(|e| {
                format!("mint_rotated_participant_leg: wide producer dispatch failed: {e}")
            })?;

        // Optional shared-turn-id override (joint participants). The EffectVm AIRs do not
        // constrain TURN_HASH (it is an executor-trusted shared PI), so overriding the carried
        // prefix slot and proving against the edited PI yields a still-valid proof binding the
        // chosen id.
        if let Some(tid) = turn_id {
            dpis[pi::TURN_HASH_BASE] = tid;
        }

        let wrap_config = ir2_leaf_wrap_config();
        let umem_boundary = UMemBoundaryWitness::default();
        let proof = prove_vm_descriptor2_for_config(
            &wide_desc,
            &wide_trace,
            &dpis,
            &mem_boundary,
            &map_heaps,
            &umem_boundary,
            &wrap_config,
        )
        .map_err(|e| format!("mint_rotated_participant_leg: wide IR-v2 batch prove failed: {e}"))?;
        verify_vm_descriptor2_with_config(&wide_desc, &proof, &dpis, &wrap_config).map_err(
            |e| format!("mint_rotated_participant_leg: minted wide proof self-verify failed: {e}"),
        )?;

        Ok(RotatedParticipantLeg {
            proof,
            descriptor: wide_desc,
            public_inputs: dpis,
            carrier_witness: None,
        })
    }

    /// **THE ROTATED+UMEM WELDED LEG MINT (STAGED, VK-RISK-FREE) — the IVC half of the flag-day
    /// weld.** Like [`mint_from_block_witnesses`](Self::mint_from_block_witnesses), but the leg's
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
        turn_id: Option<BabyBear>,
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
            empty_caveat_manifest, generate_rotated_effect_vm_trace,
            rotated_descriptor_name_for_effect, transfer_caveat_manifest,
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
        let (rot_trace, mut dpis) =
            generate_rotated_effect_vm_trace(initial_state, effects, before, after, &caveat)
                .map_err(|e| format!("mint_welded: rotated trace generation failed: {e}"))?;
        if let Some(tid) = turn_id {
            dpis[pi::TURN_HASH_BASE] = tid;
        }

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
        turn_id: Option<BabyBear>,
        umem_rows: &[Vec<BabyBear>],
        umem_boundary: &dregg_circuit::descriptor_ir2::UMemBoundaryWitness,
        domain: u32,
        before_nullifiers: Option<&[BabyBear]>,
        refusal_fields: Option<(&[dregg_circuit::heap_root::HeapLeaf], BabyBear)>,
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
        let (wide_desc, wide_trace, mut dpis, map_heaps, mem_boundary) =
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

        if let Some(tid) = turn_id {
            dpis[pi::TURN_HASH_BASE] = tid;
        }

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
        turn_id: Option<BabyBear>,
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
        let (wide_desc, wide_trace, mut dpis, map_heaps, mem_boundary) =
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

        if let Some(tid) = turn_id {
            dpis[pi::TURN_HASH_BASE] = tid;
        }

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
    /// downstream `dregg_turn::rotation_witness::mint_custom_wide_rotated_participant_leg` wrapper
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
        turn_id: Option<BabyBear>,
        bundle: CustomWitnessBundle,
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

        let (desc, trace, mut dpis, map_heaps, mb) =
            generate_rotated_effect_vm_descriptor_and_trace_wide(
                initial_state,
                effects,
                before,
                after,
                &empty_caveat_manifest(),
                None,
                None,
                None,
                // Custom lead — the committed custom row carries no membership-teeth tail.
                None,
            )
            .map_err(|e| format!("mint_custom_wide: wide custom dispatch failed: {e}"))?;

        if dpis.len() < commit_pi_hi {
            return Err(format!(
                "mint_custom_wide: custom leg PI vector must carry the commitment slice at \
                 {CUSTOM_COMMIT_PI_LO}..{commit_pi_hi} (got {})",
                dpis.len()
            ));
        }

        if let Some(tid) = turn_id {
            dpis[pi::TURN_HASH_BASE] = tid;
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
            carrier_witness: Some(CarrierWitness::Custom(bundle)),
        })
    }

    /// The rotated OLD-state commitment (PI 34 — the row-0 before-block `state_commit`).
    pub fn old_root(&self) -> BabyBear {
        self.public_inputs[dregg_circuit::effect_vm::trace_rotated::V1_PI_COUNT]
    }

    /// **THE WIDE 8-FELT OLD-state commitment** (the BEFORE 8-felt commit at the leg's
    /// PIs `[n-16 .. n-8)` — the ~124-bit faithful anchor a WIDE / wide-welded leg publishes).
    /// `None` for a leg whose PI vector is too short to carry the wide tail (a narrow leg).
    pub fn wide_old_root8(&self) -> Option<[BabyBear; 8]> {
        let n = self.public_inputs.len();
        if n < 16 {
            return None;
        }
        self.public_inputs[n - 16..n - 8].try_into().ok()
    }

    /// **THE WIDE 8-FELT NEW-state commitment** (the AFTER 8-felt commit at the leg's
    /// PIs `[n-8 .. n)` — the ~124-bit faithful anchor). `None` for a narrow leg.
    pub fn wide_new_root8(&self) -> Option<[BabyBear; 8]> {
        let n = self.public_inputs.len();
        if n < 16 {
            return None;
        }
        self.public_inputs[n - 8..n].try_into().ok()
    }
    /// The rotated NEW-state commitment (PI 35 — the last-row after-block `state_commit`).
    /// This is the next finalized turn's required `old_root` (the temporal binding).
    pub fn new_root(&self) -> BabyBear {
        self.public_inputs[dregg_circuit::effect_vm::trace_rotated::V1_PI_COUNT + 1]
    }
    /// The shared turn identity (the v1 `TURN_HASH` slot, carried in the rotated prefix).
    pub fn shared_turn_id(&self) -> BabyBear {
        self.public_inputs[pi::TURN_HASH_BASE]
    }
    /// This cell's post-state commitment (`NEW_COMMIT` position 0 — the v1-prefix carrier,
    /// distinct from `new_root()` which is the rotated v9 commitment at PI 35). The joint
    /// bundle-digest content reads this v1-prefix slot to stay byte-identical with the Silver
    /// path's projection.
    pub fn cell_commit(&self) -> BabyBear {
        self.public_inputs[pi::NEW_COMMIT_BASE]
    }
}

impl DescriptorParticipant {
    /// The shared turn identity this participant claims (`TURN_HASH` position 0 of the rotated
    /// leg's carried prefix).
    pub fn shared_turn_id(&self) -> BabyBear {
        self.rotated.shared_turn_id()
    }

    /// This cell's post-state commitment (`NEW_COMMIT` position 0 of the rotated leg's prefix).
    pub fn cell_commit(&self) -> BabyBear {
        self.rotated.cell_commit()
    }

    /// Construct a participant from its mandatory ROTATED leg (Bucket-F: the rotated leaf is the
    /// sole leg the recursion cores fold).
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
    //     `RotatedParticipantLeg::mint_from_block_witnesses`), so it must be verified under THAT
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
/// **The two-name subtlety (Bucket-F fix).** The staged registry TSV row is
/// `WIRE-name \t DISPLAY-name \t json`, and the parsed descriptor's `.name` is the *DISPLAY*
/// name (the json's internal `"name"` field, e.g. `"dregg-effectvm-transfer-v1-rot24-v3-staged"`),
/// NOT the wire name [`rotated_descriptor_name`] returns (`"transferVmDescriptor2R24"`). So this
/// maps a selector → its wire name → the TSV row → that row's DISPLAY name, and compares THAT to
/// the leg's `desc.name`. (The earlier version compared the wire name directly to `desc.name` and
/// therefore rejected every valid rotated leg.)
fn rotated_descriptor_selector(name: &str) -> Option<usize> {
    use dregg_circuit::effect_vm::trace_rotated::rotated_descriptor_name;
    use dregg_circuit::effect_vm_descriptors::V3_STAGED_REGISTRY_TSV;
    for &s in dregg_circuit::proof_forest::CUTOVER_READY_SELECTORS {
        let wire = match rotated_descriptor_name(s) {
            Some(w) => w,
            None => continue,
        };
        // Find the registry row keyed by this selector's WIRE name; its DISPLAY name (field 1) is
        // the json-internal `name` the parsed descriptor carries.
        let display = V3_STAGED_REGISTRY_TSV.lines().find_map(|line| {
            let mut it = line.splitn(3, '\t');
            if it.next() == Some(wire) {
                it.next() // the DISPLAY name (== desc.name)
            } else {
                None
            }
        });
        if display == Some(name) {
            return Some(s);
        }
    }
    None
}

/// CG-2 host check + per-cell descriptor soundness over descriptor participants. Verifies
/// (1) `>= 2` participants, (2) each per-cell ROTATED proof verifies standalone +
/// selector-binds through [`verify_descriptor_participant`], (3) all participants agree on the
/// shared turn id. Returns the agreed shared turn id. (The aggregation trace/proof is produced
/// from the same PI projections the recursive binding leaf folds.)
pub fn check_descriptor_joint_preconditions(
    participants: &[DescriptorParticipant],
) -> Result<BabyBear, JointAggError> {
    if participants.len() < 2 {
        return Err(JointAggError::TooFewParticipants {
            count: participants.len(),
        });
    }
    for (i, p) in participants.iter().enumerate() {
        verify_descriptor_participant(p).map_err(|e| JointAggError::ParticipantProofInvalid {
            index: i,
            reason: e,
        })?;
    }
    let shared_tid = participants[0].shared_turn_id();
    for (i, p) in participants.iter().enumerate() {
        if p.shared_turn_id() != shared_tid {
            return Err(JointAggError::SharedTurnIdMismatch {
                index: i,
                expected: shared_tid.0,
                found: p.shared_turn_id().0,
            });
        }
    }
    Ok(shared_tid)
}

// ============================================================================
// JointTurnAggregationAir
// ============================================================================

/// AIR binding the shared-turn-id agreement (CG-2) across N per-cell proofs and
/// folding their commitments into a single bundle digest.
///
/// Width 4: `[shared_turn_id, cell_commit, acc_in, acc_out]`.
/// Public inputs: `[shared_turn_id, initial_acc, final_acc]`.
pub struct JointTurnAggregationAir;

impl<F: PrimeCharacteristicRing + Sync> BaseAir<F> for JointTurnAggregationAir {
    fn width(&self) -> usize {
        4
    }

    fn num_public_values(&self) -> usize {
        3 // [shared_turn_id, initial_acc, final_acc]
    }

    fn main_next_row_columns(&self) -> Vec<usize> {
        (0..4).collect()
    }
}

impl<AB: AirBuilder> Air<AB> for JointTurnAggregationAir {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let local = main.current_slice();
        let next = main.next_slice();

        let row_tid: AB::Expr = local[0].into();
        let acc_in: AB::Expr = local[2].into();
        let acc_out: AB::Expr = local[3].into();
        let next_acc_in: AB::Expr = next[2].into();

        let public_values = builder.public_values();
        let pub_tid: AB::Expr = public_values[0].into();
        let initial_acc: AB::Expr = public_values[1].into();
        let final_acc: AB::Expr = public_values[2].into();

        // Constraint 1 (CG-2, THE cross-cell binding): EVERY row's shared_turn_id
        // equals the published shared turn id. A bundle whose any cell disagrees
        // on the turn id is UNSAT, regardless of per-cell validity. This is the
        // `SharedTurnId` pullback / hyperedge apex agreement.
        builder.assert_zero(row_tid - pub_tid);

        // Constraint 2: first row accumulator is the initial value.
        builder
            .when_first_row()
            .assert_zero(acc_in.clone() - initial_acc);

        // Constraint 3: last row accumulator_out is the final digest.
        builder
            .when_last_row()
            .assert_zero(acc_out.clone() - final_acc);

        // Constraint 4: chain continuity (acc_out[i] == acc_in[i+1]).
        builder.when_transition().assert_zero(acc_out - next_acc_in);
    }
}

// ============================================================================
// Trace generation
// ============================================================================

/// The pair-level core of the joint binding trace: one row per
/// `(shared_turn_id, cell_commit)` pair. The descriptor-participant Gold path
/// ([`recursion_binding_trace_descriptor_rotated`]) builds it from each rotated leg's
/// PI projections.
fn generate_joint_trace_pairs_unchecked(
    pairs: &[(BabyBear, BabyBear)],
    published_tid: BabyBear,
) -> (Vec<[BabyBear; 4]>, Vec<BabyBear>) {
    let n = pairs.len();
    let padded_len = n.next_power_of_two().max(2);
    let mut trace: Vec<[BabyBear; 4]> = Vec::with_capacity(padded_len);
    let mut accumulator = BabyBear::ZERO;

    for (i, &(tid, commit)) in pairs.iter().enumerate() {
        let idx = BabyBear::new(i as u32);
        let acc_out = hash_4_to_1(&[accumulator, tid, commit, idx]);
        trace.push([tid, commit, accumulator, acc_out]);
        accumulator = acc_out;
    }

    // Pad to power of two. Padding rows carry the published turn id (so
    // constraint 1 still holds on them) with zero commitment, continuing the
    // chain.
    for i in n..padded_len {
        let idx = BabyBear::new(i as u32);
        let acc_out = hash_4_to_1(&[accumulator, published_tid, BabyBear::ZERO, idx]);
        trace.push([published_tid, BabyBear::ZERO, accumulator, acc_out]);
        accumulator = acc_out;
    }

    let final_acc = trace.last().unwrap()[3];
    let pis = vec![published_tid, BabyBear::ZERO, final_acc];
    (trace, pis)
}

fn trace_to_matrix(trace: &[[BabyBear; 4]]) -> RowMajorMatrix<P3BabyBear> {
    let values: Vec<P3BabyBear> = trace
        .iter()
        .flat_map(|row| row.iter().map(|&v| to_p3(v)))
        .collect();
    RowMajorMatrix::new(values, 4)
}

// ============================================================================
// Shared seams reused by the Gold (recursive) path.
// ============================================================================

/// Build the [`JointTurnAggregationAir`] binding trace + public inputs for the Gold recursive path's
/// DESCRIPTOR-backed per-cell ROTATED proofs. Same host-side CG-2 rejection (a disagreeing turn
/// id errors here), same trace recipe — reads each cell's ROTATED post-state commitment
/// (PI 35, `new_root()`) as the bundle-digest content and the rotated leg's `shared_turn_id`
/// (carried in the rotated prefix). Used by
/// [`crate::joint_turn_recursive::prove_joint_core_rotated`].
///
/// (Bucket-F: the v1 `recursion_binding_trace_descriptor` — which read the v1-prefix
/// `cell_commit` — was deleted with the v1 joint core; the rotated commitment is the chain root
/// the in-circuit fold binds.)
pub fn recursion_binding_trace_descriptor_rotated(
    participants: &[&DescriptorParticipant],
) -> Result<(RowMajorMatrix<P3BabyBear>, Vec<BabyBear>), JointAggError> {
    if participants.len() < 2 {
        return Err(JointAggError::TooFewParticipants {
            count: participants.len(),
        });
    }
    let legs: Vec<&RotatedParticipantLeg> = participants.iter().map(|p| &p.rotated).collect();
    let shared_tid = legs[0].shared_turn_id();
    for (i, leg) in legs.iter().enumerate() {
        if leg.shared_turn_id() != shared_tid {
            return Err(JointAggError::SharedTurnIdMismatch {
                index: i,
                expected: shared_tid.0,
                found: leg.shared_turn_id().0,
            });
        }
    }
    let pairs: Vec<(BabyBear, BabyBear)> = legs
        .iter()
        .map(|leg| (leg.shared_turn_id(), leg.new_root()))
        .collect();
    let (trace, pis) = generate_joint_trace_pairs_unchecked(&pairs, shared_tid);
    Ok((trace_to_matrix(&trace), pis))
}

// ============================================================================
// Errors
// ============================================================================

/// Why a joint-turn aggregation failed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum JointAggError {
    /// Fewer than 2 participants — a joint turn needs at least 2 cells.
    TooFewParticipants {
        /// How many were supplied.
        count: usize,
    },
    /// A participant's PI vector is too short to carry the turn-id / commit
    /// projections.
    MalformedPublicInputs {
        /// The malformed participant.
        index: usize,
        /// Its PI length.
        len: usize,
    },
    /// **The load-bearing rejection.** Participant `index` claims a different
    /// shared turn id than the others — it is NOT a participant of this joint
    /// turn. Per-cell validity does not make it one.
    SharedTurnIdMismatch {
        /// The disagreeing participant.
        index: usize,
        /// The turn id the bundle agreed on (felt as u32).
        expected: u32,
        /// The turn id this participant carried (felt as u32).
        found: u32,
    },
    /// A participant's per-cell proof failed to verify against its public
    /// inputs.
    ParticipantProofInvalid {
        /// The participant whose proof failed.
        index: usize,
        /// The underlying verification error.
        reason: String,
    },
    /// The aggregation STARK proof failed to verify.
    AggregationProofInvalid {
        /// The verification error.
        reason: String,
    },
    /// **The VK pin refused the root** (Gold recursive path): the root proof's
    /// verifier-key fingerprint does not match the caller's trust anchor — a
    /// proof of a DIFFERENT circuit (the from-scratch-prover route).
    VkFingerprintMismatch {
        /// The anchor fingerprint the caller expected (hex).
        expected: String,
        /// The fingerprint the presented root actually has (hex).
        found: String,
    },
    /// **The claimed joint publics are unattested** (Gold recursive path): the
    /// carried `shared_turn_id`/`bundle_digest` failed to verify as the public
    /// inputs of the carried binding proof — a relabeled public claim.
    ClaimedPublicsUnattested {
        /// The underlying verification error.
        reason: String,
    },
}

impl core::fmt::Display for JointAggError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            JointAggError::TooFewParticipants { count } => {
                write!(f, "joint turn needs >= 2 participants, got {count}")
            }
            JointAggError::MalformedPublicInputs { index, len } => {
                write!(f, "participant {index} PI malformed: len {len}")
            }
            JointAggError::SharedTurnIdMismatch {
                index,
                expected,
                found,
            } => write!(
                f,
                "participant {index} shared turn id {found} != bundle turn id {expected} \
                 (not a participant of this joint turn)"
            ),
            JointAggError::ParticipantProofInvalid { index, reason } => {
                write!(f, "participant {index} proof invalid: {reason}")
            }
            JointAggError::AggregationProofInvalid { reason } => {
                write!(f, "aggregation proof invalid: {reason}")
            }
            JointAggError::VkFingerprintMismatch { expected, found } => write!(
                f,
                "joint root verifier-key fingerprint {found} != trust anchor {expected} \
                 (a proof of a different circuit — refused)"
            ),
            JointAggError::ClaimedPublicsUnattested { reason } => write!(
                f,
                "claimed joint publics are not attested by the carried binding proof \
                 (relabeled shared_turn_id/bundle_digest): {reason}"
            ),
        }
    }
}

impl std::error::Error for JointAggError {}
