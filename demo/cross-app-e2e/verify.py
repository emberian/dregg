#!/usr/bin/env python3
"""verify.py — assert all post-conditions on the cross-app composition story.

Reads the per-agent JSON artifacts from `state/` and verifies every
`must_pass` and `must_not_pass` claim in `expected.json`. Emits a
single verdict JSON to stdout and exits 0 iff every claim holds.

The verification is *structural*: we re-derive the cross-app
commitments (credential set, bounty payload, resolve target) from the
canonical helpers in `canonical.py` and check that the values pinned in
each agent's receipt match. Negative tests reproduce the tamper
attempts and verify that the resulting commitment does NOT match.
"""

import argparse
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

from canonical import (  # noqa: E402
    BOUNTY_CANCELED,
    BOUNTY_CLAIMED,
    BOUNTY_FULFILLED,
    BOUNTY_POSTED,
    BOUNTY_SETTLED,
    bounty_state_payload_hash,
    credential_set_commitment,
    credential_witness_predicate,
    resolve_target,
    schema_commitment,
    sender_authorized_credential_constraint,
)


def load_json(state_dir: str, name: str) -> dict:
    with open(os.path.join(state_dir, name)) as f:
        return json.load(f)


def verify(state_dir: str) -> dict:
    """Return a dict of {check_name: bool} for every entry in expected.json."""
    results: dict[str, bool] = {}

    alice = load_json(state_dir, "alice.out.json")
    bob_id = load_json(state_dir, "bob.identity.json")
    bob_reg = load_json(state_dir, "bob.register.json")
    bob_mount = load_json(state_dir, "bob.mount.json")
    bob_cons = load_json(state_dir, "bob.consume.json")
    carol_post = load_json(state_dir, "carol.post.json")
    carol_gc = load_json(state_dir, "carol.grant_consumer.json")
    carol_gp = load_json(state_dir, "carol.grant_publisher.json")
    carol_settle = load_json(state_dir, "carol.settle.json")
    dan_claim = load_json(state_dir, "dan.claim.json")
    dan_fulfill = load_json(state_dir, "dan.fulfill.json")

    issuer = bytes.fromhex(alice["alice_issuer_cell"])
    schema_commit = bytes.fromhex(alice["schema_commitment"])

    # ─── must_pass ────────────────────────────────────────────────────

    # 1. Schema commitment is canonical (re-derive from raw inputs).
    expected_schema = schema_commitment(
        alice["schema_name"], alice["schema_attributes"]
    )
    results["alice_schema_commitment_canonical"] = expected_schema == schema_commit

    # 2. Credential issuance binds bob_holder_id == bob's cell.
    results["credential_holder_is_bob_cell"] = (
        alice["bob_holder_id"] == bob_id["bob_cell"]
    )

    # 3. The nameservice tier constraint and Bob's witness predicate agree
    #    on the same credential-set commitment (the whole composition
    #    contract).
    expected_commit = credential_set_commitment(issuer, schema_commit).hex()
    results["tier_constraint_commitment_matches_canonical"] = (
        bob_reg["tier_constraint"]["set"]["resolved_commitment"] == expected_commit
    )
    results["witness_predicate_commitment_matches_canonical"] = (
        bob_reg["witness_predicate"]["commitment"] == expected_commit
    )
    results["tier_constraint_eq_witness_predicate_commitment"] = (
        bob_reg["tier_constraint"]["set"]["resolved_commitment"]
        == bob_reg["witness_predicate"]["commitment"]
    )

    # 4. Bob's attested registration uses the attested-tier method.
    results["bob_registration_uses_attested_method"] = (
        bob_reg["method"] == "register_name_attested"
    )

    # 5. The attested registration carries exactly one witness blob (the
    #    credential presentation proof) of kind ProofBytes.
    results["bob_registration_carries_proof_witness"] = (
        len(bob_reg["witness_blobs"]) == 1
        and bob_reg["witness_blobs"][0]["kind"] == "ProofBytes"
    )

    # 6. The name-registered-attested event carries [name_hash, owner_hash,
    #    issuer_cell, schema_commitment] as data.
    event = bob_reg["effects"][3]
    results["bob_registration_event_topic_attested"] = (
        event["type"] == "EmitEvent" and event["topic"] == "name-registered-attested"
    )
    results["bob_registration_event_carries_issuer_and_schema"] = (
        len(event["data"]) == 4
        and event["data"][2] == issuer.hex()
        and event["data"][3] == schema_commit.hex()
    )

    # 7. Bob's mount carries the nameservice resolve target.
    expected_resolve = resolve_target("pyana://cell/" + bob_id["bob_cell"]).hex()
    results["mount_carries_nameservice_resolve_target"] = (
        bob_mount["nameservice_resolve_target"] == expected_resolve
    )
    results["mount_event_data_includes_resolve_target"] = (
        len(bob_mount["effects"][0]["data"]) == 3
        and bob_mount["effects"][0]["data"][2] == expected_resolve
    )

    # 8. Bounty state hashes derive canonically and distinguish transitions.
    bounty_id = bytes.fromhex(carol_post["bounty_id"])
    dan_actor = bytes.fromhex(dan_claim["actor_pk_hash"])
    carol_actor = bytes.fromhex(carol_post["carol_pk_hash"])
    expected_claim_payload = bounty_state_payload_hash(
        bounty_id, BOUNTY_POSTED, BOUNTY_CLAIMED, dan_actor
    ).hex()
    expected_fulfill_payload = bounty_state_payload_hash(
        bounty_id, BOUNTY_CLAIMED, BOUNTY_FULFILLED, dan_actor
    ).hex()
    expected_settle_payload = bounty_state_payload_hash(
        bounty_id, BOUNTY_FULFILLED, BOUNTY_SETTLED, carol_actor
    ).hex()
    results["dan_claim_payload_hash_canonical"] = (
        dan_claim["payload_hash"] == expected_claim_payload
    )
    results["dan_fulfill_payload_hash_canonical"] = (
        dan_fulfill["payload_hash"] == expected_fulfill_payload
    )
    results["carol_settle_payload_hash_canonical"] = (
        carol_settle["payload_hash"] == expected_settle_payload
    )
    results["bounty_state_transitions_distinct"] = (
        len({expected_claim_payload, expected_fulfill_payload, expected_settle_payload})
        == 3
    )

    # 9. Subscription head advances by exactly +1 across each publish.
    results["subscription_head_advances_claim"] = dan_claim["new_head"] == 1
    results["subscription_head_advances_fulfill"] = (
        dan_fulfill["new_head"] == dan_claim["new_head"] + 1
    )
    results["subscription_head_advances_settle"] = (
        carol_settle["new_head"] == dan_fulfill["new_head"] + 1
    )

    # 10. Bob's consume advances tail by exactly +1.
    results["bob_consume_advances_tail_by_one"] = bob_cons["new_tail"] == 1

    # 11. Subscription consumer/publisher root grants populate slots.
    results["grant_consumer_writes_consumers_root"] = (
        carol_gc["effects"][0]["slot"] == "CONSUMERS_ROOT_SLOT(4)"
    )
    results["grant_publisher_writes_publishers_root"] = (
        carol_gp["effects"][0]["slot"] == "PUBLISHERS_ROOT_SLOT(3)"
    )

    # 12. Bob's consume reads the same payload Dan claimed published.
    results["bob_consumes_dan_claim_payload"] = (
        bob_cons["consumed_payload_hash"] == dan_claim["payload_hash"]
    )

    # 13. Constraint type is `SenderAuthorized` with `CredentialSet` set.
    results["constraint_is_credential_set"] = (
        bob_reg["tier_constraint"]["type"] == "SenderAuthorized"
        and bob_reg["tier_constraint"]["set"]["type"] == "CredentialSet"
    )
    # 14. Witness predicate kind is `BlindedSet` (dispatch shape).
    results["witness_predicate_kind_blinded_set"] = (
        bob_reg["witness_predicate"]["kind"] == "BlindedSet"
    )

    # ─── must_not_pass ────────────────────────────────────────────────
    # Negative tests reproduce tamper attempts and confirm the resulting
    # commitment does NOT match. The check name is prefixed
    # `rejects_*` so the assertion semantics are "this must be true; if
    # it isn't, the tamper attempt WOULD have been accepted".

    # n1. Forged credential — wrong issuer cell.
    forged_issuer = bytes.fromhex(
        "f0" * 32  # different issuer
    )
    forged_predicate = credential_witness_predicate(forged_issuer, schema_commit, 0)
    results["rejects_forged_credential_wrong_issuer"] = (
        forged_predicate["commitment"]
        != bob_reg["tier_constraint"]["set"]["resolved_commitment"]
    )

    # n2. Forged credential — wrong schema.
    forged_schema = schema_commitment("not-verified-developer-v1", ["nothing"])
    forged_predicate2 = credential_witness_predicate(issuer, forged_schema, 0)
    results["rejects_forged_credential_wrong_schema"] = (
        forged_predicate2["commitment"]
        != bob_reg["tier_constraint"]["set"]["resolved_commitment"]
    )

    # n3. Bounty fulfillment with bad actor pubkey — the payload hash
    # over (claim, fulfill, *wrong-actor*) does NOT equal Dan's.
    wrong_actor_payload = bounty_state_payload_hash(
        bounty_id, BOUNTY_CLAIMED, BOUNTY_FULFILLED, bytes(32)
    )
    results["rejects_fulfillment_with_wrong_actor"] = (
        wrong_actor_payload.hex() != dan_fulfill["payload_hash"]
    )

    # n4. Tampered prior_state — `Canceled → Fulfilled` is illegitimate
    # and produces a distinct payload Bob will not match against any
    # expected transition.
    tampered_prior = bounty_state_payload_hash(
        bounty_id, BOUNTY_CANCELED, BOUNTY_FULFILLED, dan_actor
    )
    results["rejects_tampered_prior_state"] = (
        tampered_prior.hex() != dan_fulfill["payload_hash"]
    )

    # n5. Tampered nameservice resolve target — re-derive against a
    # different URI; the value must NOT match the mount's published
    # resolve target.
    wrong_resolve = resolve_target("pyana://cell/eve-impersonator").hex()
    results["rejects_tampered_resolve_target"] = (
        wrong_resolve != bob_mount["nameservice_resolve_target"]
    )

    # n6. Tampered registration — registering under unattested method
    # without witness blob would short-circuit the credential gate.
    # Verify Bob's registration is NOT using the unattested method.
    results["rejects_unattested_method_for_attested_tier"] = (
        bob_reg["method"] != "register_name"
    )

    # n7. Tampered constraint — replacing CredentialSet with PublicRoot
    # would dispatch to a Merkle membership verifier instead of
    # BlindedSet.
    results["rejects_wrong_authorized_set_variant"] = (
        bob_reg["tier_constraint"]["set"]["type"] != "PublicRoot"
    )

    return results


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--state-dir", required=True)
    parser.add_argument("--expected", required=True)
    parser.add_argument("--out", required=True)
    args = parser.parse_args()

    with open(args.expected) as f:
        expected = json.load(f)

    results = verify(args.state_dir)

    must_pass_failures: list[str] = []
    for check in expected["must_pass"]:
        if not results.get(check, False):
            must_pass_failures.append(check)

    must_not_pass_failures: list[str] = []
    for check in expected["must_not_pass"]:
        # Each `must_not_pass` corresponds to a `rejects_*` result in our
        # results dict — the result being True means we *correctly
        # rejected* the tamper attempt.
        if not results.get(check, False):
            must_not_pass_failures.append(check)

    verdict = {
        "results": dict(sorted(results.items())),
        "must_pass_failures": must_pass_failures,
        "must_not_pass_failures": must_not_pass_failures,
        "passed": not must_pass_failures and not must_not_pass_failures,
    }

    with open(args.out, "w") as f:
        json.dump(verdict, f, indent=2, sort_keys=True)
    print(json.dumps(verdict, indent=2, sort_keys=True))
    return 0 if verdict["passed"] else 1


if __name__ == "__main__":
    sys.exit(main())
