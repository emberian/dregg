#!/usr/bin/env python3
"""carol.py — bounty poster side of the cross-app-e2e composition story.

Carol posts a bounty and creates a subscription cell that publishes
bounty-state events. After Dan fulfills, Carol settles.

The substrate primitives this step exercises:
  - subscription_factory_descriptor (Immutable CAPACITY_SLOT / OWNER_PK_HASH_SLOT,
    Monotonic on SEQ_HEAD/TAIL, PUBLISHERS_ROOT, CONSUMERS_ROOT,
    MESSAGE_ROOT)
  - build_grant_consumer_action (adding Bob as a consumer)
  - build_grant_publisher_action (adding Carol's bounty cell as a publisher)
  - build_bounty_state_publish_action (the settle event)
"""

import argparse
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

from canonical import (  # noqa: E402
    BOUNTY_FULFILLED,
    BOUNTY_SETTLED,
    blake3_field,
    bounty_state_payload_hash,
    u64_field,
)


def identity(state_dir: str) -> dict:
    carol_pk_hash = blake3_field(b"carol-pk-v1")
    carol_bounty_cell = blake3_field(b"carol-bounty-cell-seed")
    return {
        "carol_pk_hash": carol_pk_hash.hex(),
        "carol_bounty_cell": carol_bounty_cell.hex(),
    }


def cmd_post(args: argparse.Namespace) -> int:
    """Carol creates a subscription cell + posts a bounty."""
    ident = identity(args.state_dir)
    carol_pk_hash = bytes.fromhex(ident["carol_pk_hash"])

    bounty_id = blake3_field(b"CVE-2025-1234|carol-bounty")
    subscription_cell = blake3_field(b"carol-bounty-subscription-cell-seed")

    # Subscription's `field_constraints` enforce head=tail=0 + capacity ≥ 1
    # at creation time. We pin a capacity of 100.
    out = {
        "agent": "carol",
        "step": "post_bounty",
        "carol_pk_hash": carol_pk_hash.hex(),
        "carol_bounty_cell": ident["carol_bounty_cell"],
        "bounty_id": bounty_id.hex(),
        "subscription_cell": subscription_cell.hex(),
        "initial_state": {
            "seq_head": 0,
            "seq_tail": 0,
            "capacity": 100,
            "owner_pk_hash": carol_pk_hash.hex(),
        },
        "field_constraints": [
            {"type": "Equality", "slot": "SEQ_HEAD_SLOT(0)", "value": 0},
            {"type": "Equality", "slot": "SEQ_TAIL_SLOT(1)", "value": 0},
            {"type": "Range", "slot": "CAPACITY_SLOT(2)", "min": 1, "max": 1_000_000},
            {"type": "NonZero", "slot": "OWNER_PK_HASH_SLOT(5)"},
        ],
    }
    path = os.path.join(args.state_dir, "carol.post.json")
    with open(path, "w") as f:
        json.dump(out, f, indent=2, sort_keys=True)
    print(json.dumps(out, indent=2, sort_keys=True))
    return 0


def cmd_grant_consumer(args: argparse.Namespace) -> int:
    """Carol grants Bob a consumer cap on the subscription cell."""
    with open(os.path.join(args.state_dir, "carol.post.json")) as f:
        carol = json.load(f)
    with open(os.path.join(args.state_dir, "bob.identity.json")) as f:
        bob = json.load(f)

    subscription_cell = bytes.fromhex(carol["subscription_cell"])
    bob_pk = bytes.fromhex(bob["bob_pk_hash"])

    # The new consumers root advances monotonically; we fold the new
    # consumer pk into a fresh blake3 hash over (old_root || new_pk).
    old_root = bytes(32)  # empty set
    new_root = blake3_field(b"consumers-root-v1|" + old_root + bob_pk)

    out = {
        "agent": "carol",
        "step": "grant_consumer",
        "subscription_cell": subscription_cell.hex(),
        "new_consumer_pk": bob_pk.hex(),
        "old_consumers_root": old_root.hex(),
        "new_consumers_root": new_root.hex(),
        "method": "grant_consumer",
        "effects": [
            {"type": "SetField", "slot": "CONSUMERS_ROOT_SLOT(4)", "value": new_root.hex()},
            {
                "type": "EmitEvent",
                "topic": "subscription-consumer-granted",
                "data": [new_root.hex(), bob_pk.hex()],
            },
        ],
    }
    path = os.path.join(args.state_dir, "carol.grant_consumer.json")
    with open(path, "w") as f:
        json.dump(out, f, indent=2, sort_keys=True)
    print(json.dumps(out, indent=2, sort_keys=True))
    return 0


def cmd_grant_publisher(args: argparse.Namespace) -> int:
    """Carol grants her own bounty cell publishing rights."""
    with open(os.path.join(args.state_dir, "carol.post.json")) as f:
        carol = json.load(f)
    subscription_cell = bytes.fromhex(carol["subscription_cell"])
    carol_bounty_cell = bytes.fromhex(carol["carol_bounty_cell"])

    # The publisher is Carol's bounty cell (treat its id as the publisher pk).
    new_publisher_pk = carol_bounty_cell
    old_root = bytes(32)
    new_root = blake3_field(b"publishers-root-v1|" + old_root + new_publisher_pk)

    out = {
        "agent": "carol",
        "step": "grant_publisher",
        "subscription_cell": subscription_cell.hex(),
        "new_publisher_pk": new_publisher_pk.hex(),
        "old_publishers_root": old_root.hex(),
        "new_publishers_root": new_root.hex(),
        "method": "grant_publisher",
        "effects": [
            {"type": "SetField", "slot": "PUBLISHERS_ROOT_SLOT(3)", "value": new_root.hex()},
            {
                "type": "EmitEvent",
                "topic": "subscription-publisher-granted",
                "data": [new_root.hex(), new_publisher_pk.hex()],
            },
        ],
    }
    path = os.path.join(args.state_dir, "carol.grant_publisher.json")
    with open(path, "w") as f:
        json.dump(out, f, indent=2, sort_keys=True)
    print(json.dumps(out, indent=2, sort_keys=True))
    return 0


def cmd_settle(args: argparse.Namespace) -> int:
    """Carol settles the bounty after dispute window.

    Publishes a `Fulfilled → Settled` transition into the subscription
    cell.
    """
    with open(os.path.join(args.state_dir, "carol.post.json")) as f:
        carol = json.load(f)
    with open(os.path.join(args.state_dir, "dan.fulfill.json")) as f:
        dan_fulfill = json.load(f)

    subscription_cell = bytes.fromhex(carol["subscription_cell"])
    bounty_id = bytes.fromhex(carol["bounty_id"])
    carol_pk_hash = bytes.fromhex(carol["carol_pk_hash"])

    # Carol's `Fulfilled → Settled` payload hash.
    payload_hash = bounty_state_payload_hash(
        bounty_id, BOUNTY_FULFILLED, BOUNTY_SETTLED, carol_pk_hash
    )

    # Advance head from prior (Dan's fulfill = head 2 → head 3).
    prior_head = int(dan_fulfill["new_head"])
    new_head = prior_head + 1
    prior_root = bytes.fromhex(dan_fulfill["new_message_root"])
    new_root = blake3_field(
        b"message-root-v1|" + prior_root + u64_field(new_head) + payload_hash
    )

    out = {
        "agent": "carol",
        "step": "settle_bounty",
        "subscription_cell": subscription_cell.hex(),
        "bounty_id": bounty_id.hex(),
        "prior_state": "Fulfilled",
        "new_state": "Settled",
        "actor_pk_hash": carol_pk_hash.hex(),
        "payload_hash": payload_hash.hex(),
        "new_head": new_head,
        "new_head_field": u64_field(new_head).hex(),
        "new_message_root": new_root.hex(),
        "method": "publish",
        "effects": [
            {"type": "SetField", "slot": "SEQ_HEAD_SLOT(0)", "value": u64_field(new_head).hex()},
            {"type": "SetField", "slot": "MESSAGE_ROOT_SLOT(6)", "value": new_root.hex()},
            {"type": "SetField", "slot": "LATEST_PAYLOAD_SLOT(7)", "value": payload_hash.hex()},
            {
                "type": "EmitEvent",
                "topic": "subscription-published",
                "data": [u64_field(new_head).hex(), new_root.hex(), payload_hash.hex()],
            },
        ],
    }
    path = os.path.join(args.state_dir, "carol.settle.json")
    with open(path, "w") as f:
        json.dump(out, f, indent=2, sort_keys=True)
    print(json.dumps(out, indent=2, sort_keys=True))
    return 0


def main() -> int:
    parser = argparse.ArgumentParser()
    sub = parser.add_subparsers(dest="cmd", required=True)
    for name, fn in [
        ("post", cmd_post),
        ("grant-consumer", cmd_grant_consumer),
        ("grant-publisher", cmd_grant_publisher),
        ("settle", cmd_settle),
    ]:
        p = sub.add_parser(name)
        p.add_argument("--state-dir", required=True)
        p.set_defaults(fn=fn)
    args = parser.parse_args()
    return args.fn(args)


if __name__ == "__main__":
    sys.exit(main())
