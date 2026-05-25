//! End-to-end integration tests for the subscription app.
//!
//! The per-module tests under `crypto.rs`, `subscriber.rs`, `payments.rs`,
//! and `delivery.rs` cover unit-level behavior; this file glues them together
//! into realistic scenarios that span multiple modules.

use std::sync::Arc;

use pyana_app_framework::BatchExecutor;
use pyana_sdk::wallet::DelegatedToken;
use pyana_sdk::{AgentCipherclerk, Attenuation};
use pyana_token::BudgetSpec;
use tokio::sync::Mutex;

use crate::creator::{Creator, Tier};
use crate::crypto::{decrypt_with, pubkey_from_privkey};
use crate::delivery::{self, DeliveryLog, new_subscriber_inbox};
use crate::payments::{DebitTurn, PaymentExecutor};
use crate::subscriber::{SubscriberRegistry, deterministic_wallet};

fn wallet(seed: u8) -> AgentCipherclerk {
    let mut s = [0u8; 32];
    s[0] = seed;
    s[31] = seed.wrapping_mul(13);
    deterministic_wallet(s)
}

fn install_debit_auth(
    reg: &mut SubscriberRegistry,
    subscriber: &mut AgentCipherclerk,
    executor_w: &mut AgentCipherclerk,
    asset_id: u64,
    max_per_epoch: u64,
) -> DelegatedToken {
    let token = subscriber.mint_token(&[7u8; 32], "subscription-debit");
    let restrictions = Attenuation {
        budget: Some(BudgetSpec {
            id: "subscription:debit".into(),
            parent_id: None,
            class: format!("asset:{asset_id}"),
            limit: max_per_epoch,
            window: Some("epoch".into()),
        }),
        not_after: Some(i64::MAX),
        ..Default::default()
    };
    let envelope = subscriber
        .delegate(&token, &executor_w.public_key(), &restrictions)
        .unwrap();
    reg.receive_debit_delegation(executor_w, subscriber.public_key(), envelope.clone())
        .unwrap();
    envelope
}

/// End-to-end happy path:
///   1. Alice subscribes to a free tier with a published recv_pubkey.
///   2. Creator publishes content -> Alice's inbox now holds opaque ciphertext.
///   3. Alice retrieves the ciphertext (via the side-log) and decrypts it.
#[tokio::test]
async fn happy_path_free_tier_delivery() {
    let mut reg = SubscriberRegistry::new();
    let alice = wallet(1);
    let creator_w = wallet(2);

    // Alice's X25519 receive keypair.
    let alice_recv_priv = {
        let mut k = [0u8; 32];
        k[0] = 0xC0;
        k[31] = 0xDE;
        k
    };
    let alice_recv_pub = pubkey_from_privkey(&alice_recv_priv);
    reg.register_subscriber(alice.public_key(), alice_recv_pub);

    let mut creator = Creator::new(creator_w.public_key());
    creator.add_tier(Tier::free("free", "Free", 1));
    reg.subscribe(
        alice.public_key(),
        creator_w.public_key(),
        creator.tier("free").unwrap(),
        None,
    )
    .unwrap();

    let plaintext = b"The first issue is out!".to_vec();
    let hash = creator.publish("free", plaintext.clone(), 0);
    let item = creator.published.last().unwrap().clone();
    assert_eq!(item.content_hash, hash);

    let inbox = Arc::new(Mutex::new(new_subscriber_inbox(64)));
    let log = Arc::new(Mutex::new(DeliveryLog::new()));
    let pushed = delivery::publish_to_subscribers(&creator, &item, &reg, &inbox, &log)
        .await
        .unwrap();
    assert_eq!(pushed.len(), 1);

    // Side-log retrieval, then decrypt.
    let log_guard = log.lock().await;
    let pc = log_guard.get(alice.public_key(), &hash).unwrap();
    let recovered = decrypt_with(&alice_recv_priv, &pc.ciphertext).unwrap();
    assert_eq!(recovered, plaintext);
}

/// End-to-end happy path with paid tier:
///   - Alice subscribes to a premium tier (with valid credential).
///   - Alice delegates auto-debit to the executor.
///   - Executor runs the epoch, debits Alice, credits creator.
#[tokio::test]
async fn happy_path_premium_tier_with_debit() {
    let mut reg = SubscriberRegistry::new();
    let mut alice = wallet(3);
    let creator_w = wallet(4);
    let mut issuer_w = wallet(5);
    let mut executor_w = wallet(6);

    reg.register_subscriber(alice.public_key(), [0xAAu8; 32]);

    // Build the creator + premium tier issued by issuer_w.
    let mut creator = Creator::new(creator_w.public_key());
    creator.add_tier(Tier::premium("vip", "VIP", 1, 50, issuer_w.public_key()));

    // Issuer mints a premium credential for Alice.
    let issuer_token = issuer_w.mint_token(&[1u8; 32], "premium");
    let credential = issuer_w
        .delegate(
            &issuer_token,
            &alice.public_key(),
            &Attenuation {
                not_after: Some(i64::MAX),
                ..Default::default()
            },
        )
        .unwrap();

    // Alice subscribes WITH credential -> accepted.
    reg.subscribe(
        alice.public_key(),
        creator_w.public_key(),
        creator.tier("vip").unwrap(),
        Some(credential),
    )
    .unwrap();

    // Alice delegates auto-debit (asset 1, up to 100/epoch).
    let _env = install_debit_auth(&mut reg, &mut alice, &mut executor_w, 1, 100);

    // Seed Alice's balance.
    let mut exec = PaymentExecutor::new();
    exec.ledger.set(alice.public_key(), 1, 500);

    // Schedule + apply for epoch 0.
    let creators = vec![(creator_w.public_key(), &creator)];
    let n = exec.schedule_epoch(&reg, &creators, 0);
    assert_eq!(n, 1);
    let batch = exec.collect_batch(10);
    let applied = exec.apply_batch(&reg, &batch);
    assert_eq!(applied.len(), 1);

    // Numbers moved.
    assert_eq!(exec.ledger.balance(alice.public_key(), 1), 450);
    assert_eq!(exec.ledger.balance(creator_w.public_key(), 1), 50);
}

/// Premium tier rejects subscription if no credential is presented.
#[tokio::test]
async fn premium_tier_requires_credential() {
    let mut reg = SubscriberRegistry::new();
    let alice = wallet(7);
    let creator_w = wallet(8);
    let issuer_w = wallet(9);

    reg.register_subscriber(alice.public_key(), [0xAAu8; 32]);
    let mut creator = Creator::new(creator_w.public_key());
    creator.add_tier(Tier::premium("vip", "VIP", 1, 50, issuer_w.public_key()));

    let r = reg.subscribe(
        alice.public_key(),
        creator_w.public_key(),
        creator.tier("vip").unwrap(),
        None,
    );
    assert!(matches!(
        r,
        Err(crate::subscriber::SubscriberError::MissingCredential(_))
    ));
}

/// Adversarial: the inbox holds OPAQUE bytes, not the plaintext newsletter
/// body. Anyone who can read the inbox (e.g. the storage layer) sees noise.
#[tokio::test]
async fn inbox_never_contains_plaintext() {
    let mut reg = SubscriberRegistry::new();
    let alice = wallet(10);
    let creator_w = wallet(11);

    let alice_recv_priv = [0xC1u8; 32];
    reg.register_subscriber(alice.public_key(), pubkey_from_privkey(&alice_recv_priv));
    let mut creator = Creator::new(creator_w.public_key());
    creator.add_tier(Tier::free("free", "F", 1));
    reg.subscribe(
        alice.public_key(),
        creator_w.public_key(),
        creator.tier("free").unwrap(),
        None,
    )
    .unwrap();

    let plaintext = b"DO NOT LEAK THIS LINE INTO THE INBOX".to_vec();
    creator.publish("free", plaintext.clone(), 0);
    let item = creator.published.last().unwrap().clone();
    let inbox = Arc::new(Mutex::new(new_subscriber_inbox(64)));
    let log = Arc::new(Mutex::new(DeliveryLog::new()));
    let pushed = delivery::publish_to_subscribers(&creator, &item, &reg, &inbox, &log)
        .await
        .unwrap();
    assert_eq!(pushed.len(), 1);
    let ct = &pushed[0].ciphertext;

    // Ciphertext does not contain the plaintext as a substring.
    assert!(
        !ct.windows(plaintext.len()).any(|w| w == plaintext),
        "INBOX LEAKED PLAINTEXT: ciphertext contains the verbatim newsletter body"
    );
    // Even a partial substring shouldn't appear.
    let needle = &plaintext[..16];
    assert!(!ct.windows(needle.len()).any(|w| w == needle));
}

/// Adversarial: a debit for an asset NOT in the delegation is rejected.
#[tokio::test]
async fn auto_debit_pinned_to_authorized_asset() {
    let mut reg = SubscriberRegistry::new();
    let mut alice = wallet(12);
    let bob = wallet(13);
    let mut executor_w = wallet(14);

    install_debit_auth(&mut reg, &mut alice, &mut executor_w, 1, 1000);

    let mut exec = PaymentExecutor::new();
    exec.ledger.set(alice.public_key(), 7, 500);
    let r = exec.debit(
        &reg,
        DebitTurn {
            subscriber: alice.public_key(),
            creator: bob.public_key(),
            tier_id: "x".into(),
            asset_id: 7, // NOT authorized
            amount: 10,
            epoch: 0,
        },
    );
    assert!(matches!(
        r,
        Err(crate::payments::PaymentsError::WrongAsset {
            authorized: 1,
            requested: 7
        })
    ));
}

/// Adversarial: a debit that exceeds `max_per_epoch` is rejected, AND
/// nothing moves in the ledger.
#[tokio::test]
async fn auto_debit_max_per_epoch_enforced() {
    let mut reg = SubscriberRegistry::new();
    let mut alice = wallet(15);
    let bob = wallet(16);
    let mut executor_w = wallet(17);

    install_debit_auth(&mut reg, &mut alice, &mut executor_w, 1, 50);

    let mut exec = PaymentExecutor::new();
    exec.ledger.set(alice.public_key(), 1, 1_000);
    let r = exec.debit(
        &reg,
        DebitTurn {
            subscriber: alice.public_key(),
            creator: bob.public_key(),
            tier_id: "x".into(),
            asset_id: 1,
            amount: 9_999,
            epoch: 0,
        },
    );
    assert!(matches!(
        r,
        Err(crate::payments::PaymentsError::ExceedsLimit { limit: 50, .. })
    ));
    assert_eq!(exec.ledger.balance(alice.public_key(), 1), 1_000);
    assert_eq!(exec.ledger.balance(bob.public_key(), 1), 0);
}

/// Adversarial: a debit with NO authorization on file is rejected
/// (equivalent to "unsigned delegation rejected" for the wire path: there's
/// no way to land an authorization without `receive_signed_delegation` first
/// running its signature check).
#[tokio::test]
async fn auto_debit_without_authorization_rejected() {
    let reg = SubscriberRegistry::new();
    let alice = wallet(18);
    let bob = wallet(19);
    let mut exec = PaymentExecutor::new();
    exec.ledger.set(alice.public_key(), 1, 500);
    let r = exec.debit(
        &reg,
        DebitTurn {
            subscriber: alice.public_key(),
            creator: bob.public_key(),
            tier_id: "x".into(),
            asset_id: 1,
            amount: 1,
            epoch: 0,
        },
    );
    assert!(matches!(
        r,
        Err(crate::payments::PaymentsError::NoAuthorization)
    ));
}

/// Adversarial: a tampered delegation envelope (signature flipped) cannot
/// install an authorization at all.
#[tokio::test]
async fn tampered_delegation_envelope_rejected() {
    let mut reg = SubscriberRegistry::new();
    let mut alice = wallet(20);
    let mut executor_w = wallet(21);

    let token = alice.mint_token(&[7u8; 32], "subscription-debit");
    let restrictions = Attenuation {
        budget: Some(BudgetSpec {
            id: "subscription:debit".into(),
            parent_id: None,
            class: "asset:1".into(),
            limit: 100,
            window: Some("epoch".into()),
        }),
        not_after: Some(i64::MAX),
        ..Default::default()
    };
    let mut envelope = alice
        .delegate(&token, &executor_w.public_key(), &restrictions)
        .unwrap();
    // Flip a signature byte.
    envelope.delegator_signature.0[7] ^= 0x40;

    let r = reg.receive_debit_delegation(&mut executor_w, alice.public_key(), envelope);
    assert!(matches!(
        r,
        Err(crate::subscriber::SubscriberError::InvalidDelegation(_))
    ));
    assert!(reg.debit_authorizations.is_empty());
}
