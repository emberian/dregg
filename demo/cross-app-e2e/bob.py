#!/usr/bin/env python3
"""bob.py — credential holder side of the cross-app-e2e composition story.

Bob plays two roles:
  - In mode `register`, he registers `bob.dev` in the nameservice's
    identity-attested tier, presenting his credential. The action
    carries a `WitnessedPredicate::BlindedSet` whose commitment is
    derived from (alice_issuer_cell, schema_commitment).
  - In mode `mount`, he mounts his cell under the governed-namespace at
    `pyana://bob.dev` via a `register_service` turn that carries the
    nameservice's canonical resolve target.

The substrate primitives this step exercises:
  - AuthorizedSet::CredentialSet (constraint side)
  - WitnessedPredicate::BlindedSet (witness side; same commitment)
  - build_register_with_credential_action (the action shape with
    witness_blobs[0] carrying ProofBytes)
  - register_nameservice_route_action (governed-namespace's nameservice
    mount turn shape)
"""

import argparse
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

from canonical import (  # noqa: E402
    blake3_field,
    credential_set_commitment,
    credential_witness_predicate,
    name_hash,
    resolve_target,
    sender_authorized_credential_constraint,
    u64_field,
)


def identity_args(state_dir: str) -> dict:
    """Compute Bob's identity (deterministic seed)."""
    bob_cell = blake3_field(b"bob-cell-seed")
    bob_pk_hash = blake3_field(b"bob-pk-v1")
    return {
        "bob_cell": bob_cell.hex(),
        "bob_pk_hash": bob_pk_hash.hex(),
    }


def cmd_identity(args: argparse.Namespace) -> int:
    """Emit Bob's identity. Always pure-derived from the seed."""
    out = {"agent": "bob", "step": "identity"} | identity_args(args.state_dir)
    path = os.path.join(args.state_dir, "bob.identity.json")
    with open(path, "w") as f:
        json.dump(out, f, indent=2, sort_keys=True)
    print(json.dumps(out, indent=2, sort_keys=True))
    return 0


def cmd_register(args: argparse.Namespace) -> int:
    """Register `bob.dev` in the nameservice's identity-attested tier.

    The action carries the credential as `witness_blobs[0]` (kind
    `ProofBytes`); the cell program's tier-bearing case will
    `SenderAuthorized` against the credential set commitment.
    """
    ident = identity_args(args.state_dir)
    bob_cell = bytes.fromhex(ident["bob_cell"])
    bob_pk_hash = bytes.fromhex(ident["bob_pk_hash"])

    # Read alice's issuance receipt to pick up issuer_cell + schema_commitment.
    with open(os.path.join(args.state_dir, "alice.out.json")) as f:
        alice = json.load(f)
    alice_issuer = bytes.fromhex(alice["alice_issuer_cell"])
    schema_commit = bytes.fromhex(alice["schema_commitment"])
    bob_credential_id = bytes.fromhex(alice["bob_credential_id"])

    # The on-cell constraint and the action's witness predicate MUST
    # agree on the credential-set commitment.
    constraint = sender_authorized_credential_constraint(alice_issuer, schema_commit)
    predicate = credential_witness_predicate(alice_issuer, schema_commit, 0)
    assert (
        constraint["set"]["resolved_commitment"] == predicate["commitment"]
    ), "cross-app composition contract violated: constraint commit != predicate commit"

    # The presentation-proof bytes are an opaque blob from the demo's
    # point of view (the executor delegates to the registered
    # `WitnessedPredicateKind::BlindedSet` verifier). We carry a stable
    # stand-in that binds to (credential_id, bob_pk_hash) so a tamper
    # attempt (negative test) can swap it for an inconsistent value.
    presentation_proof_bytes = b"presentation|" + bob_credential_id + b"|" + bob_pk_hash

    # The registry cell Bob registers into. Deterministically derived
    # for the demo; in a real deployment it's the nameservice tier cell
    # the federation runs.
    registry_cell = blake3_field(b"nameservice-attested-tier-registry-v1")

    out = {
        "agent": "bob",
        "step": "register_attested",
        "bob_cell": bob_cell.hex(),
        "bob_pk_hash": bob_pk_hash.hex(),
        "name": "bob.dev",
        "name_hash": name_hash("bob.dev").hex(),
        "registry_cell": registry_cell.hex(),
        "method": "register_name_attested",
        "expiry_height": 5_256_000,
        "expiry_field": u64_field(5_256_000).hex(),
        "alice_issuer_cell": alice_issuer.hex(),
        "schema_commitment": schema_commit.hex(),
        "credential_id": bob_credential_id.hex(),
        # The constraint the cell program installs on the attested-tier
        # method case.
        "tier_constraint": constraint,
        # The witness-predicate shape the action carries.
        "witness_predicate": predicate,
        # `witness_blobs[0]` — ProofBytes carrying the credential
        # presentation.
        "witness_blobs": [
            {"kind": "ProofBytes", "bytes_len": len(presentation_proof_bytes)}
        ],
        # The four effects of the attested-tier registration action.
        "effects": [
            {"type": "SetField", "slot": "NAME_HASH_SLOT(2)", "value": name_hash("bob.dev").hex()},
            {"type": "SetField", "slot": "OWNER_HASH_SLOT(3)", "value": blake3_field(bob_pk_hash).hex()},
            {"type": "SetField", "slot": "EXPIRY_SLOT(4)", "value": u64_field(5_256_000).hex()},
            {
                "type": "EmitEvent",
                "topic": "name-registered-attested",
                "data": [
                    name_hash("bob.dev").hex(),
                    blake3_field(bob_pk_hash).hex(),
                    alice_issuer.hex(),
                    schema_commit.hex(),
                ],
            },
        ],
    }
    path = os.path.join(args.state_dir, "bob.register.json")
    with open(path, "w") as f:
        json.dump(out, f, indent=2, sort_keys=True)
    print(json.dumps(out, indent=2, sort_keys=True))
    return 0


def cmd_mount(args: argparse.Namespace) -> int:
    """Mount Bob's cell under a governed-namespace at `pyana://bob.dev`.

    Carries the nameservice's canonical resolve target so the route
    table's classifier and the nameservice's resolve slot agree.
    """
    ident = identity_args(args.state_dir)
    bob_cell = bytes.fromhex(ident["bob_cell"])

    # The governed-namespace cell that hosts the federation's route table.
    # Deterministic seed for the demo.
    namespace_cell = blake3_field(b"governed-namespace-federation-v1")

    # The route-table path and its nameservice resolve target.
    path_str = "/bob.dev"
    ns_resolve = resolve_target("pyana://cell/" + bob_cell.hex())

    out = {
        "agent": "bob",
        "step": "mount_namespace",
        "bob_cell": bob_cell.hex(),
        "namespace_cell": namespace_cell.hex(),
        "path": path_str,
        "path_hash": blake3_field(path_str.encode()).hex(),
        "target_cell": bob_cell.hex(),
        "nameservice_resolve_target": ns_resolve.hex(),
        "method": "register_service",
        # Single emit-event effect — the `register_service` cell-program
        # case freezes every governance slot.
        "effects": [
            {
                "type": "EmitEvent",
                "topic": "service-registered",
                "data": [
                    blake3_field(path_str.encode()).hex(),
                    bob_cell.hex(),
                    ns_resolve.hex(),
                ],
            },
        ],
    }
    path = os.path.join(args.state_dir, "bob.mount.json")
    with open(path, "w") as f:
        json.dump(out, f, indent=2, sort_keys=True)
    print(json.dumps(out, indent=2, sort_keys=True))
    return 0


def cmd_consume(args: argparse.Namespace) -> int:
    """Bob consumes a subscription event (Dan's claim).

    The consume turn advances the subscription cell's
    `SEQ_TAIL_SLOT` by exactly +1 (MonotonicSequence) and emits a
    `subscription-consumed` event.
    """
    ident = identity_args(args.state_dir)
    bob_pk_hash = bytes.fromhex(ident["bob_pk_hash"])

    with open(os.path.join(args.state_dir, "dan.claim.json")) as f:
        dan_claim = json.load(f)
    subscription_cell = bytes.fromhex(dan_claim["subscription_cell"])
    consumed_payload_hash = bytes.fromhex(dan_claim["payload_hash"])

    new_tail = 1  # Bob is consuming the first message in the queue.
    out = {
        "agent": "bob",
        "step": "consume",
        "bob_pk_hash": bob_pk_hash.hex(),
        "subscription_cell": subscription_cell.hex(),
        "new_tail": new_tail,
        "new_tail_field": u64_field(new_tail).hex(),
        "consumed_payload_hash": consumed_payload_hash.hex(),
        "method": "consume",
        "effects": [
            {"type": "SetField", "slot": "SEQ_TAIL_SLOT(1)", "value": u64_field(new_tail).hex()},
            {
                "type": "EmitEvent",
                "topic": "subscription-consumed",
                "data": [u64_field(new_tail).hex(), consumed_payload_hash.hex()],
            },
        ],
    }
    path = os.path.join(args.state_dir, "bob.consume.json")
    with open(path, "w") as f:
        json.dump(out, f, indent=2, sort_keys=True)
    print(json.dumps(out, indent=2, sort_keys=True))
    return 0


def main() -> int:
    parser = argparse.ArgumentParser()
    sub = parser.add_subparsers(dest="cmd", required=True)
    for name, fn in [
        ("identity", cmd_identity),
        ("register", cmd_register),
        ("mount", cmd_mount),
        ("consume", cmd_consume),
    ]:
        p = sub.add_parser(name)
        p.add_argument("--state-dir", required=True)
        p.set_defaults(fn=fn)
    args = parser.parse_args()
    return args.fn(args)


if __name__ == "__main__":
    sys.exit(main())
