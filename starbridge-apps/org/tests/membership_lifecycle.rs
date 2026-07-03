//! End-to-end: the org membership lifecycle across the pure authority, the
//! role-cap lattice, the committed cell mirror, and the `invoke()` service.
//!
//! The unit tests (in `src/org.rs`, `src/cap.rs`) pin each tooth; this walks a
//! whole team's life and checks the seams line up: every receipted turn advances
//! the append-only audit height, the cell mirror reflects the roster, the minted
//! role-caps reach exactly their role, and a viewer's admin attempt is refused
//! in-band and cannot be forged wider.

use dregg_app_framework::field_from_u64;
use dregg_app_framework::{AgentCipherclerk, AppCipherclerk, EmbeddedExecutor, InvokeAuthority};
use dregg_cell::Cell;
use starbridge_org::cap;
use starbridge_org::service::{OrgService, OrgServiceError};
use starbridge_org::{
    MEMBER_COLL, OWNER_SLOT, OrgAuthority, Permission, ROLE_COLL, Role, SEQ_SLOT, field_to_u64,
    mirror_org, seed_org, subject_tag,
};

/// A whole team's life: found → invite two → accept → change-role → transfer → the
/// old owner remains as admin. Every step's role-cap reaches exactly its role, and
/// the committed cell mirror tracks the roster + the monotone audit height.
#[test]
fn a_team_grows_reroles_and_hands_off_ownership() {
    let mut auth = OrgAuthority::found_with_seed([11u8; 32], "acme", "dregg:owner");
    let owner_cap = auth.owner_cap();
    let pk = auth.public();
    let id = auth.id().to_string();

    // Owner invites Alice (member) and Bob (admin); both accept, minting caps.
    let inv_a = auth
        .invite(&owner_cap, "dregg:owner", "dregg:alice", Role::Member, 1)
        .unwrap();
    let alice_cap = auth.accept_invite(&inv_a, "dregg:alice").unwrap();
    let inv_b = auth
        .invite(&owner_cap, "dregg:owner", "dregg:bob", Role::Admin, 2)
        .unwrap();
    let _bob_cap = auth.accept_invite(&inv_b, "dregg:bob").unwrap();
    assert_eq!(auth.org().member_count(), 3);

    // Alice's member-cap reaches write but not manage; Bob (admin) can manage.
    assert!(cap::authorize(&alice_cap, &pk, &id, Permission::ResourceWrite, 10).is_ok());
    assert!(cap::authorize(&alice_cap, &pk, &id, Permission::MembersManage, 10).is_err());

    // Admin Bob re-roles Alice to Viewer; her NEW cap is read-only.
    let bob_cap = auth.mint_cap(Role::Admin, None);
    let alice_viewer = auth
        .change_role(&bob_cap, "dregg:bob", "dregg:alice", Role::Viewer, 11)
        .unwrap();
    assert!(cap::authorize(&alice_viewer, &pk, &id, Permission::ResourceRead, 12).is_ok());
    assert!(cap::authorize(&alice_viewer, &pk, &id, Permission::ResourceWrite, 12).is_err());

    // The committed cell mirror reflects the roster + the monotone audit height.
    let mut cell = Cell::with_balance([7u8; 32], [9u8; 32], 0);
    mirror_org(&mut cell, auth.org());
    assert_eq!(
        cell.state.get_field(OWNER_SLOT as usize).copied(),
        Some(subject_tag("dregg:owner"))
    );
    assert_eq!(
        cell.state.get_heap(MEMBER_COLL, 0),
        Some(subject_tag("dregg:owner"))
    );
    let seq_before = field_to_u64(cell.state.get_field(SEQ_SLOT as usize).unwrap());

    // Owner transfers to Bob: owner slot moves, old owner demoted to admin.
    auth.transfer_ownership(&owner_cap, "dregg:owner", "dregg:bob", 20)
        .unwrap();
    assert_eq!(auth.org().owner, "dregg:bob");
    assert_eq!(auth.org().role_of("dregg:owner"), Some(Role::Admin));

    // Re-mirror: the owner slot moved, and the audit height only advanced.
    mirror_org(&mut cell, auth.org());
    assert_eq!(
        cell.state.get_field(OWNER_SLOT as usize).copied(),
        Some(subject_tag("dregg:bob")),
        "the mirrored owner slot moved to the new owner"
    );
    let seq_after = field_to_u64(cell.state.get_field(SEQ_SLOT as usize).unwrap());
    assert!(
        seq_after > seq_before,
        "the append-only audit height advanced"
    );

    // Bob (now owner) can delete the org; his old admin-cap could not.
    let bob_owner_cap = auth.mint_cap(Role::Owner, None);
    assert!(cap::authorize(&bob_owner_cap, &pk, &id, Permission::OrgDelete, 21).is_ok());
    assert!(cap::authorize(&bob_cap, &pk, &id, Permission::OrgDelete, 21).is_err());
}

/// A viewer cannot manage members — the cap-verify refuses in-band — and cannot
/// forge the power by appending a caveat (no amplification).
#[test]
fn a_viewer_is_refused_manage_and_cannot_amplify() {
    let mut auth = OrgAuthority::found_with_seed([12u8; 32], "acme", "dregg:owner");
    let owner_cap = auth.owner_cap();
    let inv = auth
        .invite(&owner_cap, "dregg:owner", "dregg:val", Role::Viewer, 1)
        .unwrap();
    let viewer_cap = auth.accept_invite(&inv, "dregg:val").unwrap();

    // In-band refusal: a viewer inviting someone needs MembersManage → refused.
    assert!(matches!(
        auth.invite(&viewer_cap, "dregg:val", "dregg:mallory", Role::Member, 2),
        Err(starbridge_org::OrgError::NotAuthorized {
            perm: Permission::MembersManage,
            ..
        })
    ));

    // No amplification: appending a `members:manage` caveat only NARROWS. The forged
    // cap's meet (read AND manage) is unsatisfiable — it reaches nothing wider.
    let pk = auth.public();
    let id = auth.id();
    let forged = viewer_cap.attenuate([cap_perm_manage()]);
    assert!(cap::authorize(&forged, &pk, id, Permission::MembersManage, 3).is_err());
}

/// The `AnyOf(members:manage)` caveat a self-promotion attack would append.
fn cap_perm_manage() -> dregg_auth::credential::Caveat {
    use dregg_auth::credential::{Caveat, Pred};
    Caveat::FirstParty(Pred::AnyOf(vec![Pred::AttrEq {
        key: starbridge_org::PERM_KEY.to_string(),
        value: Permission::MembersManage.as_str().to_string(),
    }]))
}

/// The `invoke()` front door: an `invite` routes + desugars, `view` is a serviced
/// seam that refuses to fake a turn, and an unauthorized caller is refused.
#[test]
fn the_service_front_door_routes_mutators_and_refuses_the_serviced_read() {
    let cipherclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x33; 32]);
    let svc = OrgService::new(cipherclerk.cell_id());

    // A Signature holder's invite routes through the interface and desugars.
    let turn = svc
        .invite(
            &cipherclerk,
            "dregg:newbie",
            Role::Member,
            0,
            1,
            InvokeAuthority::Signature,
        )
        .expect("invite routes");
    assert_eq!(turn.call_forest.roots.len(), 1);

    // `view` is a serviced read — the front door refuses to desugar it.
    assert!(matches!(
        svc.view(&cipherclerk),
        Err(OrgServiceError::Refused(_))
    ));

    // An unauthorized invite (None) is refused before any turn is built.
    assert!(matches!(
        svc.invite(
            &cipherclerk,
            "dregg:newbie",
            Role::Member,
            0,
            1,
            InvokeAuthority::None
        ),
        Err(OrgServiceError::Refused(_))
    ));
}

/// Seeding an org cell installs the invariants program and mirrors the founding
/// roster into the committed heap — a light client reads the team off the cell.
#[test]
fn seeding_installs_the_program_and_the_witnessed_roster() {
    let cipherclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x44; 32]);
    let executor = EmbeddedExecutor::new(&cipherclerk, "default");

    let mut auth = OrgAuthority::found_with_seed([13u8; 32], "acme", "dregg:owner");
    let owner_cap = auth.owner_cap();
    let inv = auth
        .invite(&owner_cap, "dregg:owner", "dregg:alice", Role::Billing, 1)
        .unwrap();
    auth.accept_invite(&inv, "dregg:alice").unwrap();
    seed_org(&executor, auth.org());

    let state = executor
        .cell_state(executor.cell_id())
        .expect("seeded org cell exists");
    // The witnessed roster: owner at 0, alice (Billing) at 1.
    assert_eq!(
        state.get_heap(MEMBER_COLL, 1),
        Some(subject_tag("dregg:alice"))
    );
    assert_eq!(
        state.get_heap(ROLE_COLL, 1),
        Some(field_from_u64(Role::Billing.code()))
    );
}
