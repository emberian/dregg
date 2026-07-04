//! KEYSTONE → DESCRIPTOR DEPLOYMENT GATE — the dual of R3's producer≡descriptor coverage gate.
//!
//! R3 (`producer_descriptor_coverage_gate.rs`) asserts *every DEPLOYED descriptor member has a test*.
//! This gate asserts the mirror: *every KEYSTONE-carrying descriptor is registry-reachable* — a green,
//! `#assert_axioms`-clean proof about a descriptor no deployed registry lists must be EXPLICITLY
//! allowlisted (with a named reason + closure lane), never silently pass as if it described the
//! deployed light-client path.
//!
//! Motivation (`docs/audit/ORPHAN-SWEEP.md`). Census R1 found `setFieldV3_pins_value` +
//! `setField_descriptorRefines` are axiom-clean but stated about `setFieldV3 = v3OfFrozenSetField`
//! (`EffectVmEmitRotationV3.lean:3143/3164`), while the DEPLOYED setField member ships `v3OfFrozen`
//! (`:5364`). The orphan sweep generalized this: a whole class of keystones proves properties of
//! descriptors the light client never runs. The DANGEROUS subset proves a property the deployed LC
//! path genuinely LACKS (the dedicated accumulator 8-felt binding; the setField circuit-grounded
//! refinement + large-write completeness).
//!
//! This is a STATIC LEDGER gate (same idiom as `producer_descriptor_coverage_gate::v3_coverage_ledger`).
//! `EffectVmDescriptor2` derives no structural `BEq` on its constraint list, so the ledger keys on
//! descriptor identity by name and is the reviewed source of truth. When a new keystone is written
//! about a descriptor, add a row here: `Deployed` if it (or a wrapper of it) is a `v3RegistryBare`
//! member, else `OrphanAllowlisted{reason}` with the §5/§6 orphan-sweep reason and its closure lane.
//! A bare orphan (no reason) FAILS the build.

/// The deployment status of the descriptor a keystone is stated about.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Deploy {
    /// The descriptor (or a wrapper of it) is a member of a deployed registry — the keystone
    /// describes what the light client actually runs. `&str` names the deployed registry member.
    Deployed(&'static str),
    /// The descriptor is NOT in any deployed registry. The keystone is green but describes a
    /// descriptor the LC never runs. Permitted ONLY with a named reason + closure lane. `&str` is
    /// "<reason>; deploy: <what it takes>".
    OrphanAllowlisted(&'static str),
}

/// `(keystone_theorem @ file:line, descriptor_it_is_about, Deploy)`.
/// Grounded to HEAD `c5de88508` — see `docs/audit/ORPHAN-SWEEP.md` §3.
fn keystone_deployment_ledger() -> Vec<(&'static str, &'static str, Deploy)> {
    use Deploy::*;
    vec![
        // ── setField: the SHARED per-row core (stated about `rotateV3 (setFieldTickFace slot)`,
        //    present in BOTH v3OfFrozen and v3OfFrozenSetField) — lane-0 value pinning genuinely
        //    holds for the deployed descriptor. SAFE/redundant.
        (
            "setFieldV3_pins_value @ EffectVmEmitRotationV3.lean:3200",
            "rotateV3 (setFieldTickFace slot)  [shared core]",
            Deployed("setFieldVmDescriptor2-{slot}R24 (v3OfFrozen shares the rotateV3 core)"),
        ),
        (
            "setFieldV3_pins_nonce_tick @ EffectVmEmitRotationV3.lean:3169",
            "rotateV3 (setFieldTickFace slot)  [shared core]",
            Deployed("setFieldVmDescriptor2-{slot}R24 (shared rotateV3 core)"),
        ),
        // ── setField: the REFINEMENT stack — stated at `Satisfied2 (setFieldV3 slot)` =
        //    v3OfFrozenSetField (freeze-EXCEPT), which is in NO registry. DANGEROUS (grounding +
        //    completeness): deployed setField rides v3OfFrozen (freeze-ALL) whose refinement is the
        //    ASSUMED EffectDecodeBridge, not these teeth; and freeze-ALL rejects honest large writes.
        (
            "setField_value_forced @ RotatedKernelRefinementSetField.lean:204",
            "setFieldV3 = v3OfFrozenSetField (EffectVmEmitRotationV3.lean:3143/3164)",
            OrphanAllowlisted(
                "v3OfFrozenSetField in no registry; deployed ships v3OfFrozen (RotationV3:5364). Soundness-safe (freeze binds harder) but refinement rides assumed EffectDecodeBridge. deploy: swap registry wrap to freeze-EXCEPT + VALUE8 lane weld (VK-affecting, gated)",
            ),
        ),
        (
            "setField_descriptorRefines @ RotatedKernelRefinementSetField.lean:238",
            "setFieldV3 = v3OfFrozenSetField",
            OrphanAllowlisted(
                "undeployed variant; deployed refinement is assumed EffectDecodeBridge (CircuitSoundnessAssembled.lean:68). deploy: VALUE8 setField weld",
            ),
        ),
        (
            "setField_descriptorRefines_fullActionStep @ RotatedKernelRefinementSetField.lean:254",
            "setFieldV3 = v3OfFrozenSetField",
            OrphanAllowlisted(
                "undeployed variant; see setField_descriptorRefines. deploy: VALUE8 setField weld",
            ),
        ),
        (
            "descriptorRefines_rejects_wrong_value @ RotatedKernelRefinementSetField.lean:274",
            "setFieldV3 = v3OfFrozenSetField",
            OrphanAllowlisted("undeployed variant. deploy: VALUE8 setField weld"),
        ),
        (
            "descriptorRefines_rejects_moved_bystander @ RotatedKernelRefinementSetField.lean:287",
            "setFieldV3 = v3OfFrozenSetField",
            OrphanAllowlisted("undeployed variant. deploy: VALUE8 setField weld"),
        ),
        (
            "rotated_row_cellSpec @ RotatedKernelRefinementSetField.lean:122",
            "setFieldV3 = v3OfFrozenSetField",
            OrphanAllowlisted("undeployed variant. deploy: VALUE8 setField weld"),
        ),
        (
            "rotated_row_gates @ RotatedKernelRefinementSetField.lean:91",
            "setFieldV3 = v3OfFrozenSetField (via rotV3FrozenSetField_sound_v1)",
            OrphanAllowlisted("undeployed variant. deploy: VALUE8 setField weld"),
        ),
        (
            "setField_descriptorComplete @ CircuitCompletenessValue.lean:446",
            "setFieldV3 = v3OfFrozenSetField",
            OrphanAllowlisted(
                "completeness proven for freeze-EXCEPT; deployed freeze-ALL REJECTS honest large-value writes so completeness does NOT transfer. deploy: VALUE8 setField weld (buys faithful large writes)",
            ),
        ),
        // ── dedicated accumulator roots: 8-felt keystones stated about `effAccumWriteV3`
        //    (AccumulatorOpenEmit.lean:129 — in NO registry). DANGEROUS at the LC level: the deployed
        //    noteSpendV3/noteCreateV3/createCellV3 denote a lane-0 scalarRootGroup (~31-bit,
        //    RotationV3:1570). Full-node-safe via the Rust node8 AIR; NOT LC-faithful.
        (
            "nullifierWrite_forces_write8_sat @ RotatedKernelRefinementCapFamily.lean:1645",
            "effAccumWriteV3 (AccumulatorOpenEmit.lean:129)",
            OrphanAllowlisted(
                "ASSURANCE-TWIN (code label CapFamily:1637); deployed noteSpendV3 denotes lane-0 scalarRootGroup (~31-bit, RotationV3:1570). Full-node-safe via Rust node8 AIR (vk_epoch_notes). deploy: flip apex to quantify over effAccumWriteV3 for the 3 roots — SEPARATE VK epoch (producers already fill 8 lanes)",
            ),
        ),
        // NOTE: commitmentWrite / cellWrite 8-felt siblings share this status (noteCreateV3 /
        //    createCellV3). Add explicit rows if/when their keystones are named individually.
        // ── the cap/heap/fields accumulator roots DO deploy the after-spine 8-felt model (the safe
        //    counterexample): *WriteCapOpen family present in rotation-v3-staged-registry.tsv,
        //    effect_vm_descriptors.rs:2045 routes has_after_spine.
    ]
}

/// THE GATE: no keystone descriptor may be a bare orphan. Every `OrphanAllowlisted` must carry a
/// non-empty reason (the named residual + closure lane). A new keystone about an undeployed
/// descriptor, added without a ledger row, will not appear here — pair this with review of new
/// `#assert_axioms` blocks (see `docs/audit/ORPHAN-SWEEP.md` §7).
#[test]
fn every_keystone_descriptor_is_deployed_or_allowlisted() {
    let ledger = keystone_deployment_ledger();
    assert!(!ledger.is_empty(), "ledger must not be empty");

    let mut bare_orphans = Vec::new();
    for (keystone, descriptor, status) in &ledger {
        match status {
            Deploy::Deployed(_) => {}
            Deploy::OrphanAllowlisted(reason) => {
                // An allowlisted orphan MUST name its reason + closure lane. An empty reason is a
                // silent orphan masquerading as reviewed — the exact laundering this gate forbids.
                if reason.trim().is_empty() || !reason.contains("deploy:") {
                    bare_orphans.push((*keystone, *descriptor, *reason));
                }
            }
        }
    }

    assert!(
        bare_orphans.is_empty(),
        "keystone(s) about an undeployed descriptor lack a reason + `deploy:` closure lane \
         (silent orphan — forbidden; see docs/audit/ORPHAN-SWEEP.md §7): {bare_orphans:?}"
    );
}

/// Visibility probe: assert the two DANGEROUS families found by the orphan sweep are present in the
/// ledger and flagged orphan — so a future edit that wires them (or deletes the keystones) has to
/// touch this gate consciously.
#[test]
fn dangerous_families_are_flagged() {
    let ledger = keystone_deployment_ledger();

    let setfield_refinement_orphan = ledger.iter().any(|(k, _, s)| {
        k.contains("setField_descriptorRefines @") && matches!(s, Deploy::OrphanAllowlisted(_))
    });
    assert!(
        setfield_refinement_orphan,
        "setField refinement stack must remain flagged as orphan until the VALUE8 weld deploys \
         v3OfFrozenSetField (ORPHAN-SWEEP §5.2)"
    );

    let accumulator_orphan = ledger.iter().any(|(k, _, s)| {
        k.contains("nullifierWrite_forces_write8_sat") && matches!(s, Deploy::OrphanAllowlisted(_))
    });
    assert!(
        accumulator_orphan,
        "dedicated-accumulator 8-felt keystone must remain flagged as orphan until the apex flips to \
         quantify over effAccumWriteV3 (ORPHAN-SWEEP §5.1)"
    );
}
