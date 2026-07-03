//! End-to-end: the custom-domain binding lifecycle across the cap-gated control
//! plane, the DNS challenge seam, and the executor-driven verified cell.
//!
//! The unit tests (in `src/*.rs`) pin each tooth; this walks a whole binding's life
//! and checks the seams line up: a forged credential cannot bind, an unverified
//! domain does not resolve, a wrong DNS nonce is refused, and the right nonce flips
//! the domain to verified exactly once — both in the routing-plane registry and as a
//! real signed turn through the executor (whose `Monotonic` verification tooth makes
//! the gated `verify` fire go dark once proven).

use dregg_app_framework::{AgentCipherclerk, AppCipherclerk, EmbeddedExecutor};
use dregg_auth::credential::RootKey;
use starbridge_domains::cap::{DomainCap, mint_domains_cap};
use starbridge_domains::dns::{ChallengeMethod, MockDns};
use starbridge_domains::{
    DomainBinding, DomainError, DomainRegistry, OWNER_RIGHTS, VERIFICATION_STATE_SLOT,
    VerificationState, domain_app, field_to_u64, fire_verify, seed_domain,
};

fn root() -> RootKey {
    RootKey::from_seed([21u8; 32])
}

/// The registry control plane: a cap-gated bind, an unverified domain that does NOT
/// resolve, a wrong DNS nonce refused, and the right nonce flipping to verified once.
#[test]
fn control_plane_bind_verify_and_the_gateway_reads() {
    let reg = DomainRegistry::with_authority(root().public());
    let cap = DomainCap::new(
        mint_domains_cap(&root(), "dregg:alice").encode(),
        "blog.acme.io",
    );
    let receipt = reg
        .bind(&cap, "blog.acme.io", "blog", ChallengeMethod::Txt)
        .expect("the rightful cap binds");
    assert_eq!(receipt.owner, "dregg:alice");
    assert_eq!(receipt.challenge.record_name, "_dregg-verify.blog.acme.io");

    // (1) An unverified (Pending) domain does not resolve — no route, no cert.
    assert!(!reg.is_verified("blog.acme.io"));
    assert_eq!(reg.site_for_host("blog.acme.io"), None);

    // (3) A wrong DNS nonce is refused; the binding stays Pending.
    let wrong = MockDns::new().with_txt(&receipt.challenge.record_name, "dregg-verify-nope");
    assert!(matches!(
        reg.verify("blog.acme.io", &wrong),
        Err(DomainError::ChallengeUnmet { .. })
    ));
    assert!(!reg.is_verified("blog.acme.io"));

    // (2) The right nonce flips to Verified; the domain now resolves.
    let dns = MockDns::new().with_txt(
        &receipt.challenge.record_name,
        &receipt.challenge.expected_value,
    );
    let b = reg
        .verify("blog.acme.io", &dns)
        .expect("the right nonce verifies");
    assert!(b.is_verified());
    let seq = b.verified_seq.expect("a verifying turn was recorded");
    assert_eq!(reg.site_for_host("blog.acme.io").as_deref(), Some("blog"));

    // Flips ONCE: an idempotent re-verify does not advance the verifying sequence.
    let again = reg
        .verify("blog.acme.io", &dns)
        .expect("idempotent re-verify");
    assert_eq!(
        again.verified_seq,
        Some(seq),
        "the flip happened exactly once"
    );
}

/// A credential minted by a DIFFERENT root (the self-asserted-cap attack) cannot bind
/// — the cap-verify refuses it under the trusted root.
#[test]
fn a_forged_credential_cannot_bind() {
    let reg = DomainRegistry::with_authority(root().public());
    let attacker = RootKey::from_seed([99u8; 32]);
    let forged = DomainCap::new(
        mint_domains_cap(&attacker, "dregg:mallory").encode(),
        "blog.acme.io",
    );
    assert!(matches!(
        reg.bind(&forged, "blog.acme.io", "blog", ChallengeMethod::Txt),
        Err(DomainError::CapRefused { .. })
    ));
}

/// The verified cell: seeding installs the invariants program, the gated `verify`
/// fire flips `VERIFICATION_STATE` 0 -> 1 through a real signed turn, and the fire
/// goes dark once verified (the not-yet-verified precondition darkens — flips once).
#[test]
fn deos_verify_flips_state_once_through_the_executor() {
    let cipherclerk = AppCipherclerk::new(AgentCipherclerk::new(), [42u8; 32]);
    let executor = EmbeddedExecutor::new(&cipherclerk, "default");
    let app = domain_app(&cipherclerk, &executor);

    let demo = DomainBinding::pending(
        "blog.acme.io",
        "blog",
        "dregg:owner",
        ChallengeMethod::Txt,
        "dregg-verify-seed",
    );
    seed_domain(&executor, &demo);

    // Pending → the gated verify fire is LIT; it flips state 0 -> 1 through a turn.
    let before =
        executor.cell_state(executor.cell_id()).unwrap().fields[VERIFICATION_STATE_SLOT as usize];
    assert_eq!(field_to_u64(&before), VerificationState::Pending.code());

    fire_verify(&app, &OWNER_RIGHTS, &cipherclerk, &executor).expect("the verify fire commits");

    let after =
        executor.cell_state(executor.cell_id()).unwrap().fields[VERIFICATION_STATE_SLOT as usize];
    assert_eq!(
        field_to_u64(&after),
        VerificationState::Verified.code(),
        "the verification state flipped to verified"
    );

    // Verified → the not-yet-verified precondition is DARK: a second fire refuses.
    assert!(
        fire_verify(&app, &OWNER_RIGHTS, &cipherclerk, &executor).is_err(),
        "the verify gate darkens once the domain is proven (flips once)"
    );
}
