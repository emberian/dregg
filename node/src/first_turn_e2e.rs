//! first_turn_e2e.rs — CAN A FRESH CLIENT SPEND WHAT THE FAUCET GAVE IT?
//!
//! The faucet moving money is only half of onboarding. The other half is the
//! recipient acting on it, and until 2026-07-25 that half did not exist: a fresh
//! client could receive coins and then do nothing, forever.
//!
//! WHY. `signed_turn_validation::validate_signed_turn` resolves a turn's
//! authority against the LIVE agent cell. Under the deployed required-PQ posture
//! it therefore answered, for a first turn:
//!
//!   * `pq-identity-not-enrolled` when the client had no cell at all — a fresh
//!     identity has nowhere to enrol its PQ key before its first turn; and
//!   * `live-agent-signer-mismatch` when the faucet HAD funded it — the faucet's
//!     grant lands in a zero-pk stub (`provision_transfer_destinations` mints the
//!     destination from turn data alone, since the recipient's key is not carried
//!     over consensus), and a zero-pk cell does not bind the client's signer.
//!
//! Both answers came out BEFORE the provisioning that would have fixed either:
//! `provision_signer_actor_cell` ran inside the execution clone, strictly after
//! validation, on every ingress and at finalization alike. The fix is an
//! ORDERING one — `claim_signer_actor_cell` runs before the predicate reads the
//! cell — and the predicate itself is untouched.
//!
//! WHAT THIS ASSERTS, and where it bites:
//!
//!   [1] faucet → the client's OWN signed turn → FINALIZED: a destination cell
//!       that existed nowhere ends up holding exactly the transferred amount on
//!       the AUTHORITATIVE ledger, and the client's cell is debited. Not the
//!       HTTP `accepted:true` — that was true throughout the outage.
//!   [2] the claim commits the client's identity: after the first turn the
//!       client's cell is bound to its Ed25519 key AND carries the ML-DSA anchor
//!       the envelope proved possession of, and the faucet grant survived the
//!       upgrade to the last computron.
//!   [3] a client with no grant at all is refused for being BROKE, not for being
//!       unknown — the `pq-identity-not-enrolled` half, pinned by its absence.
//!   [4] the tooth still bites: a turn naming a foreign agent is refused
//!       `agent-signer-mismatch` and no cell is fabricated for it.
//!
//! THE CANARY (run it, it is cheap): in `claim_signer_actor_cell`, change
//! `carried_balance` to `stub.state.balance() - 1`. [1] stays green through the
//! HTTP response and goes RED on the finalized destination balance; [2] goes RED
//! on the surviving grant. Reverting restores both. Deleting the claim call from
//! `execute_finalized_turn` alone (leaving the ingress one) also reds [1] — the
//! ingress rolls back, finalization is the only durable application.

#![cfg(test)]

use std::time::Duration;

use dregg_sdk::AgentCipherclerk;
use dregg_turn::action::Effect;
use dregg_types::hex_encode;

use crate::faucet_grant_e2e::{
    await_balance, faucet_node, faucet_node_with, post_faucet, post_faucet_json,
};
use crate::state::NodeState;

/// The `blake3("default")` asset every actor cell lives in
/// (`executor_setup::default_token_id`).
fn default_token() -> [u8; 32] {
    crate::executor_setup::default_token_id()
}

/// POST a postcard-encoded `SignedTurn` to `/turns/submit` through the real
/// router — the external-client ingress, byte-for-byte what an SDK sends.
async fn post_signed_turn(app: &axum::Router, signed: &dregg_sdk::SignedTurn) -> serde_json::Value {
    use axum::body::Body;
    use axum::extract::ConnectInfo;
    use axum::http::Request;
    use http_body_util::BodyExt;
    use tower::ServiceExt;

    let addr: std::net::SocketAddr = "127.0.0.1:4455".parse().unwrap();
    let wire = postcard::to_stdvec(signed).expect("encode SignedTurn");
    let response = app
        .clone()
        .oneshot(
            Request::builder()
                .method("POST")
                .uri("/turns/submit")
                .header("content-type", "application/octet-stream")
                .extension(ConnectInfo(addr))
                .body(Body::from(wire))
                .expect("submit request"),
        )
        .await
        .expect("submit response");
    let status = response.status();
    let bytes = response
        .into_body()
        .collect()
        .await
        .expect("body")
        .to_bytes();
    assert_eq!(
        status,
        axum::http::StatusCode::OK,
        "/turns/submit answered {status}: {}",
        String::from_utf8_lossy(&bytes)
    );
    serde_json::from_slice(&bytes).expect("submit json")
}

/// Build the client's own single-Transfer turn, signed with its own key — the
/// exact shape `payoff_client_turn.rs` and the SDK produce.
async fn client_transfer_turn(
    state: &NodeState,
    client: &AgentCipherclerk,
    to: dregg_cell::CellId,
    amount: u64,
    fee: u64,
) -> dregg_sdk::SignedTurn {
    let actor = client.cell_id("default");
    let federation_id = {
        let s = state.read().await;
        crate::executor_setup::federation_id_for_executor(&s)
    };
    let action = client.make_action(
        actor,
        "client_transfer",
        vec![Effect::Transfer {
            from: actor,
            to,
            amount,
        }],
        &federation_id,
    );
    let mut turn = client.make_turn(action);
    turn.fee = fee;
    turn.valid_until = Some(
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.as_secs() as i64)
            .unwrap_or(0)
            + 3_600,
    );
    client.sign_turn(&turn)
}

/// Every deterministic finalized-payload rejection this node recorded, by reason
/// code. An EMPTY list is the real check: a refused finalized turn is silent on
/// the HTTP surface and durable only here.
async fn finalized_rejection_codes(state: &NodeState) -> Vec<String> {
    let s = state.read().await;
    let blocklace = state.blocklace().await.expect("blocklace handle");
    let block_ids: Vec<[u8; 32]> = blocklace
        .lace
        .read()
        .await
        .all_blocks()
        .iter()
        .map(|block| block.id().0)
        .collect();
    block_ids
        .into_iter()
        .filter_map(|id| {
            let key =
                crate::signed_turn_validation::FinalizedPayloadRejectionRecord::storage_key(&id);
            s.store.get_config(&key).ok().flatten().and_then(|bytes| {
                postcard::from_bytes::<crate::signed_turn_validation::FinalizedPayloadRejectionRecord>(
                    &bytes,
                )
                .ok()
                .map(|record| record.reason_code)
            })
        })
        .collect()
}

/// THE QUICKSTART CHAIN, end to end: run a node, faucet a fresh client, have
/// that client take its OWN first turn, and watch it FINALIZE.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn a_faucet_funded_fresh_client_can_take_its_own_first_turn() {
    let (state, app, _faucet_cell_id, _tmp) = faucet_node().await;

    // A client identity NO node has ever seen — no cell, no enrollment, nothing.
    let client = AgentCipherclerk::from_key_bytes(zeroize::Zeroizing::new([0xC1; 32]));
    let actor = client.cell_id("default");
    let actor_hex = hex_encode(&actor.0);
    let grant = 10_000u64;

    // ── §1 of QUICKSTART: the faucet grant. ─────────────────────────────────
    let json = post_faucet(&app, &actor_hex, grant).await;
    assert_eq!(
        json["success"], true,
        "faucet must accept the grant: {json}"
    );
    let credited = await_balance(&state, &actor, grant as i64, Duration::from_secs(30)).await;
    assert_eq!(
        credited,
        Some(grant as i64),
        "the grant must land on the authoritative ledger before onboarding can continue"
    );

    // The shape the client is handed: a zero-pk landing stub holding real value.
    // This is the state that used to answer `live-agent-signer-mismatch`.
    {
        let s = state.read().await;
        let funded = s.ledger.get(&actor).expect("granted cell present");
        assert_eq!(
            *funded.public_key(),
            [0u8; 32],
            "a faucet grant materializes the destination from turn data alone, so its key is \
             zero until the recipient claims it — if this ever changes, the claim's stub branch \
             is no longer the path under test"
        );
    }

    // ── THE FIRST TURN: the client signs its own Transfer to a fresh cell. ──
    let destination = dregg_cell::CellId::derive_raw(&[0xD5; 32], &default_token());
    let moved = 1_000u64;
    let fee = 5_000u64;
    let signed = client_transfer_turn(&state, &client, destination, moved, fee).await;
    let response = post_signed_turn(&app, &signed).await;
    assert_eq!(
        response["accepted"], true,
        "a fresh, faucet-funded client's FIRST turn must be admitted. \
         `live-agent-signer-mismatch` here means the claim no longer runs before the predicate; \
         `pq-identity-not-enrolled` means it declined to commit the envelope's ML-DSA anchor. \
         Response: {response}"
    );

    // ── [1] THE ASSERTION THAT BITES: the AUTHORITATIVE ledger, after
    //        finalization. Admission staging is rolled back in every mode, so an
    //        `accepted:true` that never finalizes moves nothing at all. ───────
    let landed = await_balance(&state, &destination, moved as i64, Duration::from_secs(30)).await;
    assert_eq!(
        landed,
        Some(moved as i64),
        "the client's own turn must FINALIZE and fund its destination (got {landed:?}). The node \
         answered {response} — a success that is not one is exactly what this asserts past."
    );

    // ── [2] the claim committed the client's identity, and kept its money. ──
    {
        let s = state.read().await;
        let claimed = s.ledger.get(&actor).expect("client cell present");
        assert_eq!(
            *claimed.public_key(),
            client.public_key().0,
            "the stub must have been upgraded to the client's canonical account"
        );
        let identity = claimed
            .pq_identity()
            .expect("the first turn commits the ML-DSA anchor it proved possession of");
        let expected = dregg_cell::ml_dsa_public_key_commitment(&signed.pq_signer)
            .expect("canonical ML-DSA-65 key");
        assert_eq!(
            identity.ml_dsa_key_commitment, expected,
            "the committed anchor must be the key the envelope signed with, not any other"
        );
        assert_eq!(identity.key_epoch, 0, "a first claim is epoch zero");

        // NOTHING MINTED, NOTHING LOST — to the computron. An INEQUALITY here is
        // not a check: a claim that quietly drops one computron of the grant
        // satisfies "less than what you started with" forever. The client keeps
        // exactly the grant minus what its own turn moved and what it paid.
        let remaining = claimed.state.balance();
        assert_eq!(
            remaining,
            grant as i64 - moved as i64 - fee as i64,
            "the claim must carry the grant over VERBATIM: expected grant({grant}) - \
             moved({moved}) - fee({fee}); a claim that re-mints or drops even one computron \
             shows up here and nowhere else"
        );
    }

    // ── nothing was thrown away at finalization. ────────────────────────────
    let rejected = finalized_rejection_codes(&state).await;
    assert!(
        rejected.is_empty(),
        "no finalized payload in the onboarding chain may be deterministically rejected; got \
         {rejected:?}"
    );
}

/// [3] The `pq-identity-not-enrolled` half, pinned by its ABSENCE: a client that
/// never touched the faucet is refused for having no money, not for having no
/// identity. (Its cell is materialized by the claim and then cannot pay.)
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn an_unfunded_fresh_client_is_refused_for_being_broke_not_for_being_unknown() {
    let (state, app, _faucet, _tmp) = faucet_node().await;

    let client = AgentCipherclerk::from_key_bytes(zeroize::Zeroizing::new([0xC2; 32]));
    let destination = dregg_cell::CellId::derive_raw(&[0xD6; 32], &default_token());
    let signed = client_transfer_turn(&state, &client, destination, 1_000, 5_000).await;
    let response = post_signed_turn(&app, &signed).await;

    let error = response["error"].as_str().unwrap_or_default().to_string();
    assert_eq!(
        response["accepted"], false,
        "an unfunded client cannot pay for a turn: {response}"
    );
    assert!(
        !error.contains("post-quantum") && !error.contains("identity"),
        "the refusal must be about VALUE, not IDENTITY — a fresh client having nowhere to enrol \
         its PQ key is the bug, and this is how it comes back. Got: {error}"
    );
}

/// [5] THE CLAIM IS A CANDIDATE WRITE, NOT AN AUTHORITATIVE ONE.
///
/// `execute_finalized_turn` runs the first-turn claim before the admission
/// predicate reads the actor cell — correct, and [1]/[2] above depend on it. But
/// the claim must not touch the AUTHORITATIVE ledger before the durable commit
/// point, because a finalized payload can pass the whole outer perimeter and
/// still be refused afterwards (receipt continuity, the executor's own phase-1
/// charge, a faithful-note or nullifier refusal). Consensus records those as
/// `DeterministicallyRejected` and writes NOTHING durable — so a claim that
/// landed in RAM survives only in RAM.
///
/// THE DIVERGENCE THAT CAUSES: the node's durable image is `checkpoint ⊕
/// touched-cell overlay`, and `ledger_touched_diff` is taken against a base
/// captured after the claim, so a RAM-only claim is in NO commit record. A node
/// that restarts reconstructs a ledger WITHOUT the ghost cell; a node that did
/// not restart keeps it — and `canonical_ledger_root` hashes the whole cell, so
/// the very next finalized turn attests two different roots on the two nodes.
///
/// Reachable inside #65's own threat model: one enrolled Byzantine validator
/// proposes a well-formed hybrid envelope from a fresh key with a fee it cannot
/// pay. Honest HTTP ingress never gossips such a turn (it stages, rejects, and
/// rolls back), so consensus is the only way in — which is exactly the auditor's
/// point that block payloads are opaque to block admission.
///
/// THE CANARY: put `claim_signer_actor_cell(&mut s.ledger, …)` back in place of
/// the pure `claimed_actor_cell` + candidate install in `execute_finalized_turn`
/// and this goes RED on the surviving cell and on the root.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn a_refused_finalized_first_turn_leaves_no_ram_only_ghost_cell() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let state = NodeState::new(tmp.path(), Vec::new()).expect("node state");

    // A fresh identity with no cell anywhere, and a fee it cannot pay. The
    // envelope is honest: correct agent binding, both signature halves valid,
    // genesis receipt link. Only the money is missing.
    let client = AgentCipherclerk::from_key_bytes(zeroize::Zeroizing::new([0xC5; 32]));
    let actor = client.cell_id("default");
    let destination = dregg_cell::CellId::derive_raw(&[0xD7; 32], &default_token());
    let signed = client_transfer_turn(&state, &client, destination, 1_000, 5_000).await;
    let payload = postcard::to_stdvec(&signed).expect("encode SignedTurn");

    let before = {
        let s = state.read().await;
        assert!(
            s.ledger.get(&actor).is_none(),
            "the fixture must start with no cell at the actor id"
        );
        crate::blocklace_sync::canonical_ledger_root(&s.ledger)
    };

    let outcome = crate::blocklace_sync::finalize_admitted_turn_for_test(
        &state,
        dregg_blocklace::finality::BlockId([0x5C; 32]),
        &payload,
    )
    .await;

    // CLASSIFY THE REFUSAL. `is_err()`-shaped assertions pass for an
    // infrastructure fault too; this turn must be refused by the EXECUTOR, after
    // the outer perimeter admitted it — anything else (a validation code, a
    // retryable store error) means the test never reached the state under test.
    match &outcome {
        crate::execution_cursor::FinalizedExecutionOutcome::DeterministicallyRejected {
            reason_code,
            ..
        } => assert_eq!(
            reason_code, "executor-rejected",
            "the envelope must pass the outer SignedTurn perimeter and fail on VALUE; a \
             validation reason code here means the claim never ran and the ghost path was \
             never entered"
        ),
        other => panic!("expected a deterministic executor rejection, got {other:?}"),
    }

    let s = state.read().await;
    assert!(
        s.ledger.get(&actor).is_none(),
        "a refused finalized payload wrote a cell into the authoritative ledger that no commit \
         record carries — it exists only until this node restarts"
    );
    assert_eq!(
        crate::blocklace_sync::canonical_ledger_root(&s.ledger),
        before,
        "the attested ledger root moved for a turn that committed nothing"
    );
}

/// [4] The tooth the claim must never blunt: naming someone else's cell as your
/// agent is still `agent-signer-mismatch`, and no cell is fabricated for it.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn claiming_never_fabricates_authority_over_a_foreign_agent() {
    let (state, app, _faucet, _tmp) = faucet_node().await;

    let attacker = AgentCipherclerk::from_key_bytes(zeroize::Zeroizing::new([0xC3; 32]));
    let victim = dregg_cell::CellId::derive_raw(&[0xEE; 32], &default_token());
    let federation_id = {
        let s = state.read().await;
        crate::executor_setup::federation_id_for_executor(&s)
    };
    let action = attacker.make_action(
        victim,
        "steal",
        vec![Effect::Transfer {
            from: victim,
            to: attacker.cell_id("default"),
            amount: 1_000,
        }],
        &federation_id,
    );
    let mut turn = attacker.make_turn(action);
    turn.agent = victim;
    turn.fee = 5_000;
    let signed = attacker.sign_turn(&turn);

    let response = post_signed_turn(&app, &signed).await;
    assert_eq!(response["accepted"], false, "must be refused: {response}");
    assert!(
        response["error"]
            .as_str()
            .unwrap_or_default()
            .contains("does not match signer default cell"),
        "the agent/signer binding is what makes a turn attributable; got {response}"
    );

    let s = state.read().await;
    assert!(
        s.ledger.get(&victim).is_none(),
        "no cell may be fabricated at a foreign agent id"
    );
}

/// The client's own fee-0 `EmitEvent` on its own cell, signed with its own key:
/// the chat send `dregg-client-sign` builds on a coordination-exempt node.
async fn client_emit_turn(state: &NodeState, client: &AgentCipherclerk) -> dregg_sdk::SignedTurn {
    let actor = client.cell_id("default");
    let federation_id = {
        let s = state.read().await;
        crate::executor_setup::federation_id_for_executor(&s)
    };
    let emit = Effect::EmitEvent {
        cell: actor,
        event: dregg_turn::action::Event {
            topic: dregg_turn::action::symbol("helm.chat"),
            data: vec![[0x42; 32]],
        },
    };
    let action = client.make_action(actor, "helm.chat", vec![emit], &federation_id);
    let mut turn = client.make_turn(action);
    turn.fee = 0;
    turn.valid_until = Some(
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.as_secs() as i64)
            .unwrap_or(0)
            + 3_600,
    );
    client.sign_turn(&turn)
}

/// [6] THE ZERO-AMOUNT FAUCET'S TWO SHAPES, on the node `run` builds without a
/// genesis: solo, no configured committee, the default posture (required PQ).
/// A chat client materializes its cell this way and then sends fee-0 events.
///
///   * WITH `public_key`, the node mints a hosted cell already bound to the
///     Ed25519 key and carrying NO ML-DSA anchor. The first-turn claim declines
///     it (it is already the signer's account), and `validate_signed_turn`
///     refuses the hybrid turn as not enrolled, a branch that returns before it
///     reads the posture. The cell can never act.
///   * WITHOUT it, the node leaves a zero-pk stub, and the same first turn
///     claims it with the envelope's hybrid identity and finalizes.
///
/// So a client materializes without `public_key` on every node shape.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn a_key_bound_zero_amount_cell_cannot_act_but_a_stub_takes_its_first_turn() {
    let (state, app, _faucet, _tmp) = faucet_node_with(|s| {
        // `run` arms solo consensus for a node with no peers; the faucet mints
        // the key-bound hosted cell only under it.
        let sk = s.cclerk.gossip_signing_key().to_bytes();
        s.solo_consensus = Some(dregg_federation::solo::SoloConsensusState::new(sk));
        // Fee-0 EmitEvent-only turns, as a chat seat sends them.
        s.coordination_fee_exempt = true;
    })
    .await;
    {
        let s = state.read().await;
        assert!(
            !s.federation_configured,
            "the node under test is the genesis-less one: no configured committee"
        );
        assert!(
            crate::executor_setup::new_submit_executor(&s).require_pq(),
            "the node under test runs the default posture: post-quantum admission required"
        );
    }

    for (seed, bind_key) in [(0xC7u8, true), (0xC8u8, false)] {
        let client = AgentCipherclerk::from_key_bytes(zeroize::Zeroizing::new([seed; 32]));
        let actor = client.cell_id("default");
        let mut body = serde_json::json!({ "recipient": hex_encode(&actor.0), "amount": 0 });
        if bind_key {
            body["public_key"] = hex_encode(&client.public_key().0).into();
        }
        let json = post_faucet_json(&app, body).await;
        assert_eq!(json["success"], true, "materialization: {json}");
        let key = state
            .read()
            .await
            .ledger
            .get(&actor)
            .map(|c| *c.public_key());
        let want = if bind_key {
            client.public_key().0
        } else {
            [0u8; 32]
        };
        assert_eq!(
            key,
            Some(want),
            "bind_key={bind_key}: the materialized cell is not the shape under test"
        );

        let response = post_signed_turn(&app, &client_emit_turn(&state, &client).await).await;
        if bind_key {
            let error = response["error"].as_str().unwrap_or_default();
            assert_eq!(response["accepted"], false, "key-bound cell: {response}");
            assert!(
                error.contains("neither Cell-committed nor independently enrolled"),
                "a key-bound cell with no PQ anchor is refused as not enrolled; got {response}"
            );
            let anchored = state
                .read()
                .await
                .ledger
                .get(&actor)
                .map(|c| c.pq_identity().is_some());
            assert_eq!(anchored, Some(false), "the refused turn anchored nothing");
            continue;
        }
        assert_eq!(
            response["accepted"], true,
            "a stub's first hybrid turn must be admitted: {response}"
        );
        let deadline = std::time::Instant::now() + Duration::from_secs(30);
        loop {
            let claimed = state
                .read()
                .await
                .ledger
                .get(&actor)
                .map(|c| (*c.public_key(), c.state.nonce(), c.pq_identity().is_some()));
            if claimed == Some((client.public_key().0, 1, true)) {
                break;
            }
            assert!(
                std::time::Instant::now() < deadline,
                "the stub's first turn must FINALIZE: claimed by the signer, nonce 1, ML-DSA \
                 anchor committed; last saw (key, nonce, anchored) = {claimed:?}"
            );
            tokio::time::sleep(Duration::from_millis(100)).await;
        }
    }
}
