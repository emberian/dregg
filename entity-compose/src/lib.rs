//! # entity-compose — the HOARDLIGHT substrate, wired end to end, game-free
//!
//! This crate stands up a real **ENTITY** and lands a real **composition turn**, composing
//! four already-built, already-committed pieces that had never been wired together before:
//!
//! 1. **A param-carrying entity** — a [`dregg_cell::Cell`] whose *wide extended plane*
//!    (`set_field_ext` at key `>= 16` → the committed `fields_map`) carries a bounded typed
//!    param vector. The params are genuinely IN the cell's state: they move its v9 chip
//!    commitment (the value the Door welds).
//! 2. **`dregg-param-compose`** — the GENERAL Custom-VK AIR proving
//!    `outcome = Σ_linear coeff·P[role].params[i] + Σ_knots coeff·P[a].params[i]·P[b].params[j]`
//!    over N typed subjects composed by a versioned, publicly-committed ruleset.
//!    **SAY THE SUBSTRATE OUT LOUD: that AIR is LEAN-AUTHORED**
//!    (`metatheory/Dregg2/Circuit/Emit/ParamComposeEmit.lean`, byte-pinned by an `emitVmJson2`
//!    `#guard`, with the SAT ⟹ law bridge in `ParamComposeRefine.lean`). This crate resolves the
//!    emitted descriptor and FILLS ITS COLUMNS
//!    ([`dregg_param_compose::witness`]); it authors no constraint and carries no acceptance
//!    predicate. A shape Lean has not pinned is BLOCKED, not faked
//!    ([`dregg_param_compose::model::ComposeError::NoLeanDescriptor`]) — there is no Rust-AIR
//!    fallback.
//! 3. **The Door** (`dregg_turn::action::Effect::Custom`) — a custom proof reaches
//!    `TurnExecutor::execute`, which verifies the VK, the registry dispatch, and the STATE
//!    WELD (`pis[0..8] == the cell's stored commitment`, `pis[8..16] == the claimed new`).
//! 4. **The cell** — the outcome is committed to the entity's cell, welded to its real
//!    pre/post state.
//!
//! ## The generic vocabulary is the point
//!
//! Everything here speaks in `subjects`, `params`, `roles`, `knots`, `ruleset`, `outcome` —
//! never a creature, a stat, or a rule. HOARDLIGHT's living world is ONE ruleset root + its
//! content (params) over this substrate, exactly as a new `dregg-param-compose` game is a new
//! ruleset root and not an AIR edit. Nothing in this crate is dragon-specific.
//!
//! ## What composes end to end (HONEST SCOPE)
//!
//! **What composes, driven through the real executor** (`tests/end_to_end.rs`):
//! a real entity's params determine its v9 commitment; a composition READ from those params
//! proves under the ruleset; the turn carrying it passes the Door and the state weld against
//! the entity's REAL commitment; a proof about a DIFFERENT entity (different params → different
//! commitment) is refused by the weld; a composition the ruleset does not license has no
//! satisfying witness. The realistic composition rides the LEAN-AUTHORED 770-column leaf
//! (`tests/budget.rs`), and the composition leaf really proves + binds its commitment
//! (`tests/leaf_prove.rs`, `#[ignore]`, minutes).
//!
//! ## The outcome→cell-field weld — CLOSED by ADOPTING the deployed app-root atom
//!
//! The state weld binds the *whole cell* transition (`old8`/`new8`), but by itself it does not
//! force the post cell's stored outcome field to equal the sub-proof's published
//! `outcome_commitment` public input — a host could write outcome `X` into the cell while the
//! sub-proof commits outcome `Y`, and the state weld alone would not notice ("the host wrote
//! both"). That residual is closed by the SAME in-circuit tie the multiway-tug win-proof
//! deployed on Friday: the **app-root weld**
//! (`dregg_circuit::effect_vm::custom_state_binding::AppRootBinding` + the deployed fold node
//! `dregg_circuit_prove::joint_turn_recursive::prove_custom_binding_node_app_root_segmented`).
//!
//! **Say the substrate out loud:** this is NOT hand-written Rust AIR and NOT new Lean AIR. The
//! tie is a *fold `connect`* inside the recursion tree a pure light client folds (its in-circuit
//! keystone descends from Lean `CustomBindingFromFold`). Rust here does only two ABI things, no
//! constraint authoring: (1) it RELOCATES the 8-felt `outcome_commitment` out of the wide plane
//! and into the entity cell's **native `fields[0..8]` octet** — the octet the wide Custom leg
//! exposes and the `new8` commitment absorbs at lane-0 (`field_limbs9(fields[i])[0]`), the SAME
//! lane the deployed weld reads; and (2) it DECLARES the binding
//! ([`LandedComposition::app_root_binding`]) so the outcome PI at
//! [`pi::outcome_commitment_base`] is tied, lane-by-lane, to that committed octet. The wide
//! plane cannot be reached by the atom (`field_key` indexes only the native octet), which is
//! why the outcome moved into `fields[0..8]`.
//!
//! With the binding declared and the fold routed through the app-root node, a composed entity
//! whose PUBLISHED outcome does not equal its COMMITTED octet has NO satisfying fold (UNSAT, no
//! root, the light client never receives a verifying artifact) — driven, honest-accepts /
//! forged-refuses, in `dregg-braid-hook`'s weld canary. [`LandedComposition::app_root_binding`]
//! is the declaration a game/offering hands to the deployed chain prover;
//! [`LandedComposition::harness_verify_outcome_welded`] reads back the committed octet as a fast
//! shadow of the equality the fold now enforces for real.

use dregg_cell::commitment::{
    self, V9RotationContext, bytes32_to_felt8, compute_canonical_state_commitment_v9_8,
};
use dregg_cell::{Cell, CellId, CellMode, Ledger};
use dregg_circuit::descriptor_ir2::EffectVmDescriptor2;
use dregg_circuit::effect_vm::custom_state_binding::AppRootBinding;
use dregg_circuit::effect_vm::field_limbs9;
use dregg_circuit::field::BabyBear;
use dregg_param_compose::lean_descriptor::{lean_descriptor_for, lean_descriptor_json};
use dregg_param_compose::model::{ComposeError, Composition, Ruleset, Subject};
use dregg_param_compose::pi;
use dregg_param_compose::shape::ComposeShape;
use dregg_param_compose::witness::{ComposeWitness, compose_trace_accepts, compose_witness};

pub use dregg_param_compose::model::{Knot, LinearTerm};
pub use dregg_param_compose::{ComposeShape as Shape, Composition as Comp};

/// Wide-plane base key for an entity's projection (`identity` at `base`, `role` at `base+1`,
/// `params[i]` at `base+2+i`). Keys `>= 16` land in the committed `fields_map`, so the
/// projection is part of the cell's state commitment. Chosen at 16, the first wide key.
pub const PROJECTION_WIDE_BASE: u64 = 16;

/// Native-field slot base for the published `outcome_commitment` (8 felts → native
/// `fields[0..8]`, one felt per slot). This is the octet the deployed **app-root weld** reaches:
/// the wide Custom leg exposes `fields[0..8]` and the `new8` commitment absorbs each slot's
/// lane-0, so the outcome committed here is welded, lane-by-lane, to the sub-proof's published
/// outcome PI. The outcome deliberately rides the NATIVE octet (not the wide `fields_map` where
/// the params live) because the weld's `field_key` indexes only `fields[0..8]`.
pub const OUTCOME_NATIVE_BASE: usize = 0;

/// The app-root weld operates over the whole 8-felt `outcome_commitment` octet.
pub const OUTCOME_OCTET_LEN: usize = 8;

/// Encode a single BabyBear as a 32-byte `FieldElement` (the low 4 bytes carry the felt; the
/// rest are zero) — used where a felt rides the WIDE plane (e.g. an entity param).
pub fn felt_to_fe(f: BabyBear) -> [u8; 32] {
    let mut out = [0u8; 32];
    out[..4].copy_from_slice(&f.0.to_le_bytes());
    out
}

/// Encode a single BabyBear into a native `fields[i]` slot such that
/// `field_limbs9(&fe)[0] == f` — i.e. the felt lands in the lane-0 position the wide Custom leg
/// exposes and the `new8` commitment absorbs. `field_limbs9` reads lane-0 from the big-endian
/// low 4 bytes `[28..32]`, so the felt is written there; every other byte is zero.
pub fn outcome_native_fe(f: BabyBear) -> [u8; 32] {
    let mut out = [0u8; 32];
    out[28..32].copy_from_slice(&f.0.to_be_bytes());
    out
}

/// Encode an unsigned scalar (identity / role) as a wide-plane `FieldElement` (LE, round-trips).
pub fn u64_to_fe(v: u64) -> [u8; 32] {
    let mut out = [0u8; 32];
    out[..8].copy_from_slice(&v.to_le_bytes());
    out
}

/// Encode a signed param value as a wide-plane `FieldElement` (two's-complement LE, round-trips
/// EXACTLY). What matters for the substrate: a DIFFERENT value yields a different `fields_root`,
/// hence a different commitment — and it reads back bit-for-bit.
pub fn param_to_fe(v: i64) -> [u8; 32] {
    let mut out = [0u8; 32];
    out[..8].copy_from_slice(&v.to_le_bytes());
    out
}

fn read_u64_fe(cell: &Cell, key: u64) -> u64 {
    let fe = cell.state.fields_root_membership(key).unwrap_or([0u8; 32]);
    let mut b = [0u8; 8];
    b.copy_from_slice(&fe[..8]);
    u64::from_le_bytes(b)
}

fn read_i64_fe(cell: &Cell, key: u64) -> i64 {
    read_u64_fe(cell, key) as i64
}

/// Write an entity's projection (identity, role, params) into a cell's wide plane at `base`.
/// After this the cell's state commitment is a function of the projection.
pub fn install_projection(cell: &mut Cell, base: u64, s: &Subject) {
    cell.state.set_field_ext(base, u64_to_fe(s.identity));
    cell.state.set_field_ext(base + 1, u64_to_fe(s.role));
    for (i, &p) in s.params.iter().enumerate() {
        cell.state
            .set_field_ext(base + 2 + i as u64, param_to_fe(p));
    }
}

/// Read an entity's projection back OUT of the committed wide plane (via `fields_root_membership`,
/// so a read only succeeds when the recomputed `fields_root` matches the stored one) — the
/// round-trip that makes "the params ARE the subjects" real rather than carried alongside.
pub fn read_projection(cell: &Cell, base: u64, param_count: usize) -> Subject {
    Subject {
        identity: read_u64_fe(cell, base),
        role: read_u64_fe(cell, base + 1),
        params: (0..param_count as u64)
            .map(|i| read_i64_fe(cell, base + 2 + i))
            .collect(),
    }
}

/// Compute a cell's canonical **v9 chip commitment** — the 32-byte value the Custom-VK Door
/// welds (`old8`/`new8` = `bytes32_to_felt8` of this). The wide `fields_map` is folded in, so
/// this moves when the entity's params move.
pub fn v9_commitment(cell: &Cell) -> ([u8; 32], V9RotationContext) {
    let mut ctx_ledger = Ledger::new();
    let _ = ctx_ledger.insert_cell(cell.clone());
    let ctx = V9RotationContext {
        cells_root: dregg_turn::rotation_witness::cells_root(&ctx_ledger),
        nullifier_root: dregg_circuit::heap_root::empty_heap_root_8(),
        commitments_root: dregg_circuit::heap_root::empty_heap_root_8(),
        revoked_root: dregg_turn::rotation_witness::empty_revoked_root_8(),
        iroot: dregg_turn::rotation_witness::iroot8(&[]),
        material: Default::default(),
    };
    let commitment = compute_canonical_state_commitment_v9_8(cell, &ctx);
    (commitment, ctx)
}

fn open_permissions() -> dregg_cell::Permissions {
    use dregg_cell::AuthRequired;
    dregg_cell::Permissions {
        send: AuthRequired::None,
        receive: AuthRequired::None,
        set_state: AuthRequired::None,
        set_permissions: AuthRequired::None,
        set_verification_key: AuthRequired::None,
        increment_nonce: AuthRequired::None,
        delegate: AuthRequired::None,
        access: AuthRequired::None,
    }
}

/// A deployed sovereign entity: a cell whose wide plane carries its projection, its v9
/// commitment (the Door's `old8` source), and the projection itself (the composition subject).
#[derive(Clone)]
pub struct DeployedEntity {
    pub cell: Cell,
    pub subject: Subject,
    pub ctx: V9RotationContext,
    pub commitment: [u8; 32],
}

impl DeployedEntity {
    pub fn cell_id(&self) -> CellId {
        self.cell.id()
    }
    /// The Door's `old8` — the pre-state root the state weld compares against the cell's
    /// registered sovereign commitment.
    pub fn old8(&self) -> [BabyBear; 8] {
        bytes32_to_felt8(&self.commitment)
    }
    /// Register this entity as a sovereign cell at its real commitment (the pre-state the
    /// executor reads as `old_commit8`) and return a ledger carrying it.
    pub fn into_registered_ledger(self) -> (CellId, Ledger, Self) {
        let cell_id = self.cell.id();
        let mut ledger = Ledger::new();
        ledger
            .register_sovereign_cell(cell_id, self.commitment)
            .expect("sovereign registration");
        let _ = ledger.insert_cell(self.cell.clone());
        (cell_id, ledger, self)
    }
}

/// **An entity's key** — the full 32-byte cell key an entity is deployed at.
///
/// The cell id is `CellId::derive_raw(&key, &token_id)`, so DISTINCT keys are distinct entities
/// and the key space is the entity namespace. It is the full width on purpose: a narrow
/// ordinal-shaped seed caps a deployer at that many live entities (the app then has to fail
/// closed at the cap or, worse, collide two entities onto one cell), which is a property of the
/// wiring rather than of anything the app means.
pub type EntityKey = [u8; 32];

/// **A key from an ordinal** — the injective little-endian encoding of `n` into [`EntityKey`].
/// Injective, so two ordinals never name one cell; `2^64` entities per deployer, which is not a
/// cap any caller reaches. A caller that already HAS a 32-byte identity (an asset id, a pubkey,
/// a digest of the thing the entity stands for) should pass it straight to [`deploy_entity`]
/// instead — this exists for the ordinary "the nth entity I minted" case.
pub fn entity_key(n: u64) -> EntityKey {
    let mut key = [0u8; 32];
    key[..8].copy_from_slice(&n.to_le_bytes());
    key
}

/// Deploy a primary entity: a sovereign cell whose wide plane carries `subject`'s projection.
///
/// `key` is the entity's full-width cell key ([`entity_key`] builds one from an ordinal). The
/// wiring imposes no bound on how many entities a deployer can carry — an exhausted namespace is
/// not a thing this hook can hand its callers.
pub fn deploy_entity(key: EntityKey, balance: i64, subject: Subject) -> DeployedEntity {
    let mut cell = Cell::with_balance(key, [0u8; 32], balance);
    cell.permissions = open_permissions();
    cell.mode = CellMode::Sovereign;
    install_projection(&mut cell, PROJECTION_WIDE_BASE, &subject);
    let (commitment, ctx) = v9_commitment(&cell);
    DeployedEntity {
        cell,
        subject,
        ctx,
        commitment,
    }
}

/// The result of composing a primary entity's params (+ partners) into a committed outcome and
/// packaging it as a state-welded custom sub-proof ready to land through the Door.
pub struct LandedComposition {
    /// The primary entity whose cell the turn lands on.
    pub cell_id: CellId,
    /// The composition (subjects read from the entity + partners, the ruleset).
    pub composition: Composition,
    pub shape: ComposeShape,
    /// The exact composed outcome (`i128`, the AIR's field twin is `fb(outcome)`).
    pub outcome: i128,
    /// The 8-felt `outcome_commitment` (both the sub-proof's PI and what the post cell carries).
    pub outcome_commitment: Vec<BabyBear>,
    /// The Door's `old8` (the entity's real pre-state commitment).
    pub old_commitment: [u8; 32],
    /// The Door's claimed `new8` — the commitment of a POST cell carrying the outcome.
    pub new_commitment: [u8; 32],
    /// The post cell (a clone of the entity's cell with `outcome_commitment` in its wide plane).
    pub post_cell: Cell,
    /// The composition sub-proof's public inputs `[old8 ‖ new8 ‖ ..app]` — produced by, and
    /// identical to, [`LandedComposition::witness`]'s.
    pub pis: Vec<BabyBear>,
    /// **The produced witness for the LEAN-AUTHORED AIR.** The trace row filling the column layout
    /// `metatheory/Dregg2/Circuit/Emit/ParamComposeEmit.lean` §2 declares, from this composition's
    /// host-side data. Rust fills columns here; it authors no constraint.
    pub witness: ComposeWitness,
}

impl LandedComposition {
    /// The sub-proof PIs as `u32` (the wire form `CustomProgramProof::public_inputs` carries).
    pub fn pis_u32(&self) -> Vec<u32> {
        self.pis.iter().map(|f| f.0).collect()
    }

    /// **The app-root weld declaration.** The sub-proof's published `outcome_commitment` occupies
    /// PIs `[outcome_commitment_base .. +8)`, and it MUST equal the entity cell's committed native
    /// `fields[0..8]` octet (`field_key = OUTCOME_NATIVE_BASE`, width 8). This is the deployed
    /// [`AppRootBinding`] a game/offering hands to the chain prover
    /// (`bundle.app_root_binding = landed.app_root_binding()`); the prover then routes the
    /// custom turn through `prove_direct_ir2_binding_node_app_root_segmented`, whose in-circuit
    /// `connect` forces published-outcome == committed-octet lane-by-lane. NOT hand-written AIR —
    /// see the crate doc.
    pub fn app_root_binding(&self) -> AppRootBinding {
        AppRootBinding {
            app_root_pi_offset: pi::outcome_commitment_base(),
            app_root_len: OUTCOME_OCTET_LEN,
            field_key: OUTCOME_NATIVE_BASE,
        }
    }

    /// **The direct-IR2 fold-leaf inputs, bound to a leg's REAL rotated roots.** Re-produce the
    /// witness with the door prefix set to `(old8, new8)` — the wide Custom leg's real rotated
    /// anchors, which are computed from the leg's rotation witness and differ from the crate's own
    /// `v9_commitment` context — and return `(descriptor, base_trace, public_inputs)` ready for
    /// `prove_direct_ir2_leaf_with_app_root_commitment` / a `CustomIr2WitnessBundle`.
    ///
    /// **The descriptor is the LEAN-AUTHORED one** — `paramComposeDesc` at this shape, decoded
    /// straight out of its byte-pinned Lean golden. Rust supplies only the trace fill. The
    /// published `outcome_commitment` (PI `[outcome_commitment_base .. +8)`) is a function of the
    /// composition alone, so it is UNCHANGED by the roots and equals the committed native octet.
    ///
    /// Fail-closed twice: [`ComposeError::NoLeanDescriptor`] at a shape Lean has not pinned (there
    /// is no Rust-AIR fallback to degrade to), and [`ComposeError::WitnessRefusedByDescriptor`] if
    /// the produced trace does not satisfy the emitted gates — a witness-generator fault is refused
    /// here rather than handed to the prover.
    pub fn direct_ir2_leaf_inputs(
        &self,
        old8: &[BabyBear; 8],
        new8: &[BabyBear; 8],
        num_rows: usize,
    ) -> Result<(EffectVmDescriptor2, Vec<Vec<BabyBear>>, Vec<BabyBear>), ComposeError> {
        let desc = lean_descriptor_for(&self.shape).ok_or(ComposeError::NoLeanDescriptor)?;
        let w = compose_witness(&self.shape, &self.composition, old8, new8)?;
        if !compose_trace_accepts(&desc, &w) {
            return Err(ComposeError::WitnessRefusedByDescriptor);
        }
        Ok((desc, w.base_trace(num_rows), w.pis))
    }

    /// The canonical program bytes the composition's `vk_hash` binds: the Lean-emitted descriptor's
    /// own wire string. `None` at a shape Lean has not pinned.
    pub fn program_bytes(&self) -> Option<Vec<u8>> {
        program_bytes(&self.shape)
    }

    /// **The outcome→cell-field weld, fast shadow.** Returns true iff the POST cell's native
    /// `fields[0..8]` octet carries (at lane-0) EXACTLY the sub-proof's published
    /// `outcome_commitment` — the equality the deployed app-root fold now ENFORCES in-circuit.
    /// Reading it back here is a cheap host-side echo of the property the light client verifies
    /// for real once the turn is folded through `prove_custom_binding_node_app_root_segmented`.
    pub fn harness_verify_outcome_welded(&self) -> bool {
        let base = pi::outcome_commitment_base();
        for (j, expect) in self.outcome_commitment.iter().enumerate() {
            let Some(fe) = self.post_cell.state.get_field(OUTCOME_NATIVE_BASE + j) else {
                return false;
            };
            // The committed octet's lane-0 is the felt the wide leg exposes and the weld reads.
            if field_limbs9(fe)[0] != *expect {
                return false;
            }
            // ...and it is the same value the sub-proof published as its outcome PI.
            if self.pis[base + j] != *expect {
                return false;
            }
        }
        true
    }

    /// **THE FAIL-CLOSED PRODUCER CANARY** — whether the produced witness satisfies the
    /// LEAN-AUTHORED descriptor, judged by the DEPLOYED IR-v2 row-local evaluator
    /// (`Ir2Air::Main::eval`). This is the gate the deleted Rust-AIR `air_accepts` used to be, with
    /// the authority moved from a Rust predicate to the emitted object.
    ///
    /// `false` at a shape Lean has not pinned — blocked, not faked: there is no Rust-authored AIR
    /// to fall back to, so a shape without an emitted descriptor cannot be attested.
    pub fn lean_descriptor_accepts(&self) -> bool {
        match lean_descriptor_for(&self.shape) {
            Some(desc) => compose_trace_accepts(&desc, &self.witness),
            None => false,
        }
    }
}

/// Compose a primary entity's params (read from its wide plane) with zero or more `partners`
/// under `ruleset` at `shape`, and package the result as a state-welded custom sub-proof
/// bound to the entity's REAL pre/post commitments.
///
/// The POST cell is the entity's cell with the composition's `outcome_commitment` written into
/// its native `fields[0..8]` octet at [`OUTCOME_NATIVE_BASE`], so `new8` genuinely commits a
/// state carrying the outcome AND the octet is the value the deployed app-root weld reaches (see
/// the crate doc and [`LandedComposition::app_root_binding`]).
pub fn compose_onto(
    entity: &DeployedEntity,
    partners: &[Subject],
    ruleset: Ruleset,
    shape: ComposeShape,
    param_count: usize,
) -> Result<LandedComposition, ComposeError> {
    // THE READ: the primary subject is READ from the entity cell's committed wide plane, not
    // carried alongside — the params genuinely ARE the composition's subject.
    let primary = read_projection(
        &entity.cell,
        PROJECTION_WIDE_BASE,
        entity.subject.params.len(),
    );
    debug_assert_eq!(
        primary, entity.subject,
        "the wide-plane projection must round-trip to the deployed subject"
    );
    let mut subjects = vec![primary];
    subjects.extend_from_slice(partners);
    let composition = Composition {
        subjects,
        ruleset,
        param_count,
    };

    let composed = composition.compose()?;
    let outcome_commitment = composition.outcome_commitment(&shape)?;

    let old_commitment = entity.commitment;
    let old8 = bytes32_to_felt8(&old_commitment);

    // The POST cell carries the outcome in its NATIVE `fields[0..8]` octet -> its commitment is
    // `new8`. Written at lane-0 (`outcome_native_fe`) so the wide Custom leg exposes exactly this
    // octet and the deployed app-root weld ties it to the sub-proof's published outcome PI.
    let mut post_cell = entity.cell.clone();
    for (j, f) in outcome_commitment.iter().enumerate() {
        post_cell
            .state
            .set_field(OUTCOME_NATIVE_BASE + j, outcome_native_fe(*f));
    }
    let (new_commitment, _post_ctx) = v9_commitment(&post_cell);
    let new8 = bytes32_to_felt8(&new_commitment);

    // Produce the LEAN-AUTHORED AIR's witness bound to the entity's REAL (old8, new8). The PIs are
    // the producer's — one source, so the packaged PIs and the proven trace cannot disagree.
    let witness = compose_witness(&shape, &composition, &old8, &new8)?;
    let pis = witness.pis.clone();

    Ok(LandedComposition {
        cell_id: entity.cell_id(),
        composition,
        shape,
        outcome: composed.outcome,
        outcome_commitment,
        old_commitment,
        new_commitment,
        post_cell,
        pis,
        witness,
    })
}

/// Sanity re-exports so a downstream (a HOARDLIGHT ruleset) builds subjects/rulesets without
/// depending on `dregg-param-compose` directly.
pub use dregg_param_compose::model::{
    ComposeError as EntityComposeError, Ruleset as EntityRuleset,
};

/// Convenience: the v9 chip commitment as the Door's 8-felt form.
pub fn commitment_felt8(commitment: &[u8; 32]) -> [BabyBear; 8] {
    bytes32_to_felt8(commitment)
}

/// **The composition program's descriptor — the LEAN-AUTHORED one.** A function of the SHAPE, not
/// the content (two unrelated rulesets share one VK; that is the whole point of the crate), decoded
/// from its byte-pinned Lean golden. `None` at a shape Lean has not pinned.
pub fn program_descriptor(shape: &ComposeShape) -> Option<EffectVmDescriptor2> {
    lean_descriptor_for(shape)
}

/// The `program_bytes` a genuine v2 `vk_hash` binds: the Lean-emitted descriptor's own wire string,
/// so a turn names the composition program's own verification key rather than a stand-in — and the
/// key is over the LEAN object, not over a Rust re-authoring of it. `None` at an unpinned shape.
pub fn program_bytes(shape: &ComposeShape) -> Option<Vec<u8>> {
    lean_descriptor_json(shape).map(|j| j.as_bytes().to_vec())
}

/// Re-export the raw commitment helper for tests that want to assert the executor's comparand.
pub use commitment::bytes32_to_felt8 as door_felt8;
