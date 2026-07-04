//! Synthetic-forest tests: a balanced/well-formed forest PASSES; an
//! amplifying / non-conserving / malformed / unbalanced-ring forest FAILS
//! with the precise locus.

use dregg_cell::facet::{EFFECT_GRANT_CAPABILITY, EFFECT_SET_FIELD, EFFECT_TRANSFER};
use dregg_cell::note::{NoteCommitment, Nullifier};
use dregg_cell::permissions::AuthRequired;
use dregg_cell::{CapabilityRef, CellId};
use dregg_turn::action::{Action, Authorization, DelegationMode, Effect};
use dregg_turn::{CallForest, CallTree};

use crate::*;

fn cell(n: u8) -> CellId {
    let mut b = [0u8; 32];
    b[0] = n;
    CellId(b)
}

/// A bare signed action carrying the given effects.
fn action(target: CellId, effects: Vec<Effect>) -> Action {
    Action {
        target,
        method: [0u8; 32],
        args: Vec::new(),
        authorization: Authorization::Signature([1u8; 32], [2u8; 32]),
        preconditions: Default::default(),
        effects,
        may_delegate: DelegationMode::None,
        commitment_mode: Default::default(),
        balance_change: None,
        witness_blobs: vec![],
    }
}

fn cap(target: CellId, slot: u32, facet: Option<u32>, expiry: Option<u64>) -> CapabilityRef {
    CapabilityRef {
        target,
        slot,
        permissions: AuthRequired::Signature,
        breadstuff: None,
        expires_at: expiry,
        allowed_effects: facet,
        stored_epoch: None,
    }
}

fn forest_of(roots: Vec<CallTree>) -> CallForest {
    CallForest {
        roots,
        forest_hash: [0u8; 32],
    }
}

// ─── B: conservation ────────────────────────────────────────────────────────

#[test]
fn balanced_transfer_forest_conserves() {
    // A → B 100, B → A 100 : nets to zero.
    let f = forest_of(vec![
        CallTree::new(action(
            cell(1),
            vec![Effect::Transfer {
                from: cell(1),
                to: cell(2),
                amount: 100,
            }],
        )),
        CallTree::new(action(
            cell(2),
            vec![Effect::Transfer {
                from: cell(2),
                to: cell(1),
                amount: 100,
            }],
        )),
    ]);
    assert!(check_conservation(&f).is_pass());
}

#[test]
fn nonconserving_balance_change_fails_with_locus() {
    // A single +50 balance_change with no offsetting −50: residue 50.
    let mut a = action(cell(1), vec![Effect::IncrementNonce { cell: cell(1) }]);
    a.balance_change = Some(50);
    let f = forest_of(vec![CallTree::new(a)]);
    let v = check_conservation(&f);
    assert!(!v.is_pass());
    let finding = &v.findings()[0];
    assert_eq!(finding.locus.asset.as_deref(), Some(COMPUTRON_ASSET));
    assert!(finding.message.contains("conjured"));
}

#[test]
fn note_value_imbalance_fails() {
    // spend 100 of asset 7, create 60 of asset 7: residue +40.
    let f = forest_of(vec![CallTree::new(action(
        cell(1),
        vec![
            Effect::NoteSpend {
                nullifier: Nullifier([0u8; 32]),
                note_tree_root: [0u8; 32],
                value: 100,
                asset_type: 7,
                spending_proof: vec![],
                value_commitment: None,
            },
            Effect::NoteCreate {
                commitment: NoteCommitment([0u8; 32]),
                value: 60,
                asset_type: 7,
                encrypted_note: vec![],
                value_commitment: None,
                range_proof: None,
            },
        ],
    ))]);
    let v = check_conservation(&f);
    assert!(!v.is_pass());
    assert_eq!(v.findings()[0].locus.asset.as_deref(), Some("note:7"));
}

#[test]
fn note_value_balance_conserves() {
    let f = forest_of(vec![CallTree::new(action(
        cell(1),
        vec![
            Effect::NoteSpend {
                nullifier: Nullifier([0u8; 32]),
                note_tree_root: [0u8; 32],
                value: 100,
                asset_type: 7,
                spending_proof: vec![],
                value_commitment: None,
            },
            Effect::NoteCreate {
                commitment: NoteCommitment([0u8; 32]),
                value: 100,
                asset_type: 7,
                encrypted_note: vec![],
                value_commitment: None,
                range_proof: None,
            },
        ],
    ))]);
    assert!(check_conservation(&f).is_pass());
}

// ─── A: non-amplification ───────────────────────────────────────────────────

#[test]
fn in_forest_attenuating_grant_passes() {
    // root grants cell(2) a transfer-only cap on cell(9);
    // child (under 2's scope) re-grants the SAME (or narrower) cap → attenuation.
    let granted_cap = cap(cell(9), 0, Some(EFFECT_TRANSFER), None);
    let mut root = CallTree::new(action(
        cell(1),
        vec![Effect::GrantCapability {
            from: cell(1),
            to: cell(2),
            cap: granted_cap.clone(),
        }],
    ));
    // child: cell(2) re-grants the same cap to cell(3) — same target, same facet.
    root.children.push(CallTree::new(action(
        cell(2),
        vec![Effect::GrantCapability {
            from: cell(2),
            to: cell(3),
            cap: granted_cap,
        }],
    )));
    let f = forest_of(vec![root]);
    assert!(check_no_amplification(&f).is_pass());
}

#[test]
fn in_forest_amplifying_grant_fails_with_locus() {
    // root grants cell(2) a TRANSFER-ONLY cap on cell(9);
    // child cell(2) re-grants a WIDER cap (transfer + set_field) on cell(9): amplify.
    let narrow = cap(cell(9), 0, Some(EFFECT_TRANSFER), None);
    let wide = cap(cell(9), 0, Some(EFFECT_TRANSFER | EFFECT_SET_FIELD), None);
    let mut root = CallTree::new(action(
        cell(1),
        vec![Effect::GrantCapability {
            from: cell(1),
            to: cell(2),
            cap: narrow,
        }],
    ));
    root.children.push(CallTree::new(action(
        cell(2),
        vec![Effect::GrantCapability {
            from: cell(2),
            to: cell(3),
            cap: wide,
        }],
    )));
    let f = forest_of(vec![root]);
    let v = check_no_amplification(&f);
    assert!(!v.is_pass());
    let finding = &v.findings()[0];
    // locus is the child node (path [0, 0]) effect 0.
    assert_eq!(finding.locus.node_path, vec![0, 0]);
    assert_eq!(finding.locus.effect_index, Some(0));
    assert!(finding.message.contains("amplifies"));
}

#[test]
fn unrestricted_regrant_of_restricted_cap_fails() {
    // parent grant is faceted (transfer only); child re-grants UNRESTRICTED (None) → amplify.
    let narrow = cap(cell(9), 0, Some(EFFECT_TRANSFER), None);
    let unrestricted = cap(cell(9), 0, None, None);
    let mut root = CallTree::new(action(
        cell(1),
        vec![Effect::GrantCapability {
            from: cell(1),
            to: cell(2),
            cap: narrow,
        }],
    ));
    root.children.push(CallTree::new(action(
        cell(2),
        vec![Effect::GrantCapability {
            from: cell(2),
            to: cell(3),
            cap: unrestricted,
        }],
    )));
    let f = forest_of(vec![root]);
    assert!(!check_no_amplification(&f).is_pass());
}

#[test]
fn later_expiry_regrant_fails() {
    let parent = cap(cell(9), 0, Some(EFFECT_TRANSFER), Some(100));
    let extended = cap(cell(9), 0, Some(EFFECT_TRANSFER), Some(200));
    let mut root = CallTree::new(action(
        cell(1),
        vec![Effect::GrantCapability {
            from: cell(1),
            to: cell(2),
            cap: parent,
        }],
    ));
    root.children.push(CallTree::new(action(
        cell(2),
        vec![Effect::GrantCapability {
            from: cell(2),
            to: cell(3),
            cap: extended,
        }],
    )));
    let f = forest_of(vec![root]);
    assert!(!check_no_amplification(&f).is_pass());
}

#[test]
fn grant_over_unrelated_target_not_flagged() {
    // cell(2) grants a cap over cell(99) which was NEVER delegated in-forest.
    // Holding is a dynamic question → not flagged (the honest boundary).
    let granted = cap(cell(9), 0, Some(EFFECT_TRANSFER), None);
    let elsewhere = cap(cell(99), 0, None, None);
    let mut root = CallTree::new(action(
        cell(1),
        vec![Effect::GrantCapability {
            from: cell(1),
            to: cell(2),
            cap: granted,
        }],
    ));
    root.children.push(CallTree::new(action(
        cell(2),
        vec![Effect::GrantCapability {
            from: cell(2),
            to: cell(3),
            cap: elsewhere,
        }],
    )));
    let f = forest_of(vec![root]);
    assert!(check_no_amplification(&f).is_pass());
}

#[test]
fn cap_attenuates_basic() {
    let top = cap(cell(9), 0, None, None);
    let narrow = cap(cell(9), 0, Some(EFFECT_TRANSFER), None);
    assert!(cap_attenuates(&narrow, &top)); // narrower ⊑ top
    assert!(!cap_attenuates(&top, &narrow)); // top ⊄ narrow
    // different target never attenuates
    let other = cap(cell(8), 0, Some(EFFECT_TRANSFER), None);
    assert!(!cap_attenuates(&other, &narrow));
    // subset facet ok; superset facet not
    let xfer = cap(cell(9), 0, Some(EFFECT_TRANSFER), None);
    let xfer_grant = cap(
        cell(9),
        0,
        Some(EFFECT_TRANSFER | EFFECT_GRANT_CAPABILITY),
        None,
    );
    assert!(cap_attenuates(&xfer, &xfer_grant));
    assert!(!cap_attenuates(&xfer_grant, &xfer));
}

// ─── well-formedness ────────────────────────────────────────────────────────

#[test]
fn unchecked_authorization_flagged() {
    let mut a = action(cell(1), vec![Effect::IncrementNonce { cell: cell(1) }]);
    a.authorization = Authorization::Unchecked;
    let f = forest_of(vec![CallTree::new(a)]);
    let v = check_wellformed(&f);
    assert!(!v.is_pass());
    assert!(v.findings()[0].message.contains("Unchecked"));
}

#[test]
fn oneof_with_unchecked_flagged() {
    let mut a = action(cell(1), vec![Effect::IncrementNonce { cell: cell(1) }]);
    a.authorization = Authorization::OneOf {
        candidates: vec![
            Authorization::Signature([1u8; 32], [2u8; 32]),
            Authorization::Unchecked,
        ],
        proof_index: 0,
    };
    let f = forest_of(vec![CallTree::new(a)]);
    assert!(!check_wellformed(&f).is_pass());
}

#[test]
fn empty_action_flagged() {
    let f = forest_of(vec![CallTree::new(action(cell(1), vec![]))]);
    let v = check_wellformed(&f);
    assert!(!v.is_pass());
    assert!(
        v.findings()
            .iter()
            .any(|f| f.message.contains("zero effects"))
    );
}

#[test]
fn noop_exercise_flagged() {
    let f = forest_of(vec![CallTree::new(action(
        cell(1),
        vec![Effect::ExerciseViaCapability {
            cap_slot: 0,
            inner_effects: vec![],
        }],
    ))]);
    let v = check_wellformed(&f);
    assert!(!v.is_pass());
    assert!(
        v.findings()
            .iter()
            .any(|f| f.message.contains("no-op exercise"))
    );
}

#[test]
fn wellformed_signed_turn_passes() {
    let f = forest_of(vec![CallTree::new(action(
        cell(1),
        vec![Effect::Transfer {
            from: cell(1),
            to: cell(2),
            amount: 5,
        }],
    ))]);
    assert!(check_wellformed(&f).is_pass());
}

// ─── ring balance ───────────────────────────────────────────────────────────

#[test]
fn balanced_three_party_ring_passes() {
    // A →(X,10)→ B →(X,10)→ C →(X,10)→ A : every participant nets 0 in X.
    let legs = vec![
        RingLeg {
            from: cell(1),
            to: cell(2),
            asset: "X".into(),
            amount: 10,
        },
        RingLeg {
            from: cell(2),
            to: cell(3),
            asset: "X".into(),
            amount: 10,
        },
        RingLeg {
            from: cell(3),
            to: cell(1),
            asset: "X".into(),
            amount: 10,
        },
    ];
    assert!(check_ring_balance(&legs).is_pass());
}

#[test]
fn unbalanced_ring_fails_with_participant_locus() {
    // A gives 10 to B, B gives 10 to C, but C does NOT close back to A:
    // A nets −10, C nets +10. Open ring.
    let legs = vec![
        RingLeg {
            from: cell(1),
            to: cell(2),
            asset: "X".into(),
            amount: 10,
        },
        RingLeg {
            from: cell(2),
            to: cell(3),
            asset: "X".into(),
            amount: 10,
        },
    ];
    let v = check_ring_balance(&legs);
    assert!(!v.is_pass());
    // at least one finding names asset X and a nonzero net.
    assert!(
        v.findings().iter().any(|f| {
            f.locus.asset.as_deref() == Some("X") && f.message.contains("not balanced")
        })
    );
}

#[test]
fn self_loop_ring_flagged() {
    let legs = vec![
        RingLeg {
            from: cell(1),
            to: cell(1),
            asset: "X".into(),
            amount: 10,
        },
        RingLeg {
            from: cell(2),
            to: cell(2),
            asset: "X".into(),
            amount: 10,
        },
    ];
    let v = check_ring_balance(&legs);
    assert!(!v.is_pass());
    assert!(v.findings().iter().any(|f| f.message.contains("self-loop")));
}

#[test]
fn extract_ring_legs_from_transfer_forest() {
    let f = forest_of(vec![
        CallTree::new(action(
            cell(1),
            vec![Effect::Transfer {
                from: cell(1),
                to: cell(2),
                amount: 10,
            }],
        )),
        CallTree::new(action(
            cell(2),
            vec![Effect::Transfer {
                from: cell(2),
                to: cell(1),
                amount: 10,
            }],
        )),
    ]);
    let legs = extract_ring_legs(&f);
    assert_eq!(legs.len(), 2);
    assert!(check_ring_balance(&legs).is_pass());
}

// ─── the combined entry ─────────────────────────────────────────────────────

#[test]
fn analyze_clean_turn_passes() {
    let f = forest_of(vec![CallTree::new(action(
        cell(1),
        vec![Effect::Transfer {
            from: cell(1),
            to: cell(2),
            amount: 7,
        }],
    ))]);
    let a = analyze(&f, false);
    assert!(a.pass());
    assert!(a.all_findings().is_empty());
}

#[test]
fn analyze_serializes_to_json() {
    let f = forest_of(vec![CallTree::new(action(
        cell(1),
        vec![Effect::Transfer {
            from: cell(1),
            to: cell(2),
            amount: 7,
        }],
    ))]);
    let a = analyze(&f, true);
    let j = serde_json::to_string(&a).unwrap();
    assert!(j.contains("conservation"));
    let back: Assurance = serde_json::from_str(&j).unwrap();
    assert_eq!(a, back);
}

#[test]
fn boundary_report_lists_both_halves() {
    let r = crate::boundary::report();
    assert!(r.contains("STATIC"));
    assert!(r.contains("DYNAMIC"));
    assert!(r.contains("HOLDING"));
}

// ─── app: exposure bound (Σ provisional-exposure ≤ reserve) ──────────────────

/// Encode a small `u64` as the `field_from_u64` field element `decode_u64_field`
/// reads back (big-endian in the trailing 8 bytes, leading 24 bytes zero).
fn field_u64(v: u64) -> [u8; 32] {
    let mut f = [0u8; 32];
    f[24..32].copy_from_slice(&v.to_be_bytes());
    f
}

#[test]
fn exposure_within_reserve_passes() {
    // Mint 100 to cell(2), Burn 40 back: net provisional exposure 60.
    // Reserve slot 6 on cell(1) written = 70 → 60 ≤ 70 passes (exercises the
    // Mint RISE + Burn FALL fold and an in-forest reserve write).
    let f = forest_of(vec![CallTree::new(action(
        cell(1),
        vec![
            Effect::SetField {
                cell: cell(1),
                index: 6,
                value: field_u64(70),
            },
            Effect::Mint {
                target: cell(2),
                slot: 0,
                amount: 100,
            },
            Effect::Burn {
                target: cell(2),
                slot: 0,
                amount: 40,
            },
        ],
    ))]);
    let schema = app::ExposureSchema::new(cell(1), 6);
    assert!(app::check_exposure_bound(&f, &schema, None).is_pass());
}

#[test]
fn exposure_over_reserve_fails_with_locus() {
    // Mint 150 against a reserve of 100 → exposure 150 > 100: a Finding.
    let f = forest_of(vec![CallTree::new(action(
        cell(1),
        vec![
            Effect::SetField {
                cell: cell(1),
                index: 6,
                value: field_u64(100),
            },
            Effect::Mint {
                target: cell(2),
                slot: 0,
                amount: 150,
            },
        ],
    ))]);
    let schema = app::ExposureSchema::new(cell(1), 6);
    let v = app::check_exposure_bound(&f, &schema, None);
    assert!(!v.is_pass());
    let finding = &v.findings()[0];
    assert_eq!(finding.guarantee, "exposure (reserve bound)");
    assert!(finding.message.contains("exceeds the reserve"));
    assert!(
        finding
            .locus
            .asset
            .as_deref()
            .is_some_and(|a| a.starts_with("reserve:"))
    );
}

#[test]
fn exposure_uses_prior_reserve_when_forest_omits_it() {
    // The forest mints 50 but does NOT write the reserve slot: the ceiling comes
    // from `prior_reserve` (the earlier funding turn). 50 ≤ 100 passes; 50 > 40
    // fails — the ≤ boundary honored from the prior-committed reserve.
    let f = forest_of(vec![CallTree::new(action(
        cell(1),
        vec![Effect::Mint {
            target: cell(2),
            slot: 0,
            amount: 50,
        }],
    ))]);
    let schema = app::ExposureSchema::new(cell(1), 6);
    assert!(app::check_exposure_bound(&f, &schema, Some(100)).is_pass());
    assert!(!app::check_exposure_bound(&f, &schema, Some(40)).is_pass());
}

#[test]
fn exposure_unresolved_reserve_is_reported() {
    // Mint present, reserve neither written in-forest nor supplied: report the
    // unresolved reserve rather than passing (or failing) vacuously.
    let f = forest_of(vec![CallTree::new(action(
        cell(1),
        vec![Effect::Mint {
            target: cell(2),
            slot: 0,
            amount: 50,
        }],
    ))]);
    let schema = app::ExposureSchema::new(cell(1), 6);
    let v = app::check_exposure_bound(&f, &schema, None);
    assert!(!v.is_pass());
    assert!(
        v.findings()[0]
            .message
            .contains("cannot check the exposure bound")
    );
}

#[test]
fn analyze_defaults_exposure_to_pass_and_roundtrips() {
    // `analyze` cannot infer a reserve schema, so it leaves exposure Pass
    // (vacuous, like ring_balance) — and the field round-trips through serde.
    let f = forest_of(vec![CallTree::new(action(
        cell(1),
        vec![Effect::Transfer {
            from: cell(1),
            to: cell(2),
            amount: 7,
        }],
    ))]);
    let a = analyze(&f, false);
    assert!(a.exposure.is_pass());
    assert!(a.pass());
    let j = serde_json::to_string(&a).unwrap();
    assert!(j.contains("exposure"));
    let back: Assurance = serde_json::from_str(&j).unwrap();
    assert_eq!(a, back);
}

#[test]
fn ffi_exposure_subrequest_surfaces_verdict() {
    // The FFI `exposure` sub-request runs check_exposure_bound and folds the
    // verdict into `assurance.exposure`, flipping the roll-up `pass`.
    let f = forest_of(vec![CallTree::new(action(
        cell(1),
        vec![
            Effect::SetField {
                cell: cell(1),
                index: 6,
                value: field_u64(100),
            },
            Effect::Mint {
                target: cell(2),
                slot: 0,
                amount: 150,
            },
        ],
    ))]);
    let forest_json = serde_json::to_string(&f).unwrap();
    let mut cell_hex = String::new();
    for b in cell(1).0 {
        cell_hex.push_str(&format!("{b:02x}"));
    }
    let req = format!(
        r#"{{"forest":{forest_json},"app":{{"exposure":{{"cell":"{cell_hex}","reserve_slot":6}}}}}}"#
    );
    let resp = crate::ffi::analyze_json(&req);
    let v: serde_json::Value = serde_json::from_str(&resp).unwrap();
    assert_eq!(v["ok"], true);
    assert_eq!(v["pass"], false);
    // exposure is a Fail object (over-reserve), not the "Pass" string.
    assert!(v["assurance"]["exposure"].get("Fail").is_some());
}
