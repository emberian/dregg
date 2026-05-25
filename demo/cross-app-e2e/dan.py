#!/usr/bin/env python3
"""dan.py — bounty claimer side of the cross-app-e2e composition story.

Dan claims Carol's bounty and submits a fulfillment proof. Both turns
publish bounty-state transitions into the subscription cell so Bob's
consume turn sees them.

The substrate primitives this step exercises:
  - build_bounty_state_publish_action (Claimed and Fulfilled transitions)
  - bounty_state_payload_hash (canonical payload for both)
  - subscription's `publish` case (MonotonicSequence head, Monotonic
    message root, SenderAuthorized publisher set)
"""

import argparse
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

from canonical import (  # noqa: E402
    BOUNTY_CLAIMED,
    BOUNTY_FULFILLED,
    BOUNTY_POSTED,
    blake3_field,
    bounty_state_payload_hash,
    u64_field,
)


def dan_pk_hash() -> bytes:
    return blake3_field(b"dan-pk-v1")


def cmd_claim(args: argparse.Namespace) -> int:
    """Dan claims the bounty — `Posted → Claimed` publish."""
    with open(os.path.join(args.state_dir, "carol.post.json")) as f:
        carol = json.load(f)
    subscription_cell = bytes.fromhex(carol["subscription_cell"])
    bounty_id = bytes.fromhex(carol["bounty_id"])

    actor = dan_pk_hash()
    payload_hash = bounty_state_payload_hash(
        bounty_id, BOUNTY_POSTED, BOUNTY_CLAIMED, actor
    )

    # First publish on a fresh queue: head 0 → 1, message_root grows
    # from zero by folding (new_head, payload_hash).
    new_head = 1
    prior_root = bytes(32)
    new_root = blake3_field(
        b"message-root-v1|" + prior_root + u64_field(new_head) + payload_hash
    )

    out = {
        "agent": "dan",
        "step": "claim_bounty",
        "subscription_cell": subscription_cell.hex(),
        "bounty_id": bounty_id.hex(),
        "prior_state": "Posted",
        "new_state": "Claimed",
        "actor_pk_hash": actor.hex(),
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
    path = os.path.join(args.state_dir, "dan.claim.json")
    with open(path, "w") as f:
        json.dump(out, f, indent=2, sort_keys=True)
    print(json.dumps(out, indent=2, sort_keys=True))
    return 0


def cmd_fulfill(args: argparse.Namespace) -> int:
    """Dan submits a fulfillment proof — `Claimed → Fulfilled` publish."""
    with open(os.path.join(args.state_dir, "carol.post.json")) as f:
        carol = json.load(f)
    with open(os.path.join(args.state_dir, "dan.claim.json")) as f:
        claim = json.load(f)

    subscription_cell = bytes.fromhex(carol["subscription_cell"])
    bounty_id = bytes.fromhex(carol["bounty_id"])
    actor = dan_pk_hash()

    payload_hash = bounty_state_payload_hash(
        bounty_id, BOUNTY_CLAIMED, BOUNTY_FULFILLED, actor
    )

    prior_head = int(claim["new_head"])
    new_head = prior_head + 1
    prior_root = bytes.fromhex(claim["new_message_root"])
    new_root = blake3_field(
        b"message-root-v1|" + prior_root + u64_field(new_head) + payload_hash
    )

    out = {
        "agent": "dan",
        "step": "fulfill_bounty",
        "subscription_cell": subscription_cell.hex(),
        "bounty_id": bounty_id.hex(),
        "prior_state": "Claimed",
        "new_state": "Fulfilled",
        "actor_pk_hash": actor.hex(),
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
    path = os.path.join(args.state_dir, "dan.fulfill.json")
    with open(path, "w") as f:
        json.dump(out, f, indent=2, sort_keys=True)
    print(json.dumps(out, indent=2, sort_keys=True))
    return 0


def main() -> int:
    parser = argparse.ArgumentParser()
    sub = parser.add_subparsers(dest="cmd", required=True)
    for name, fn in [("claim", cmd_claim), ("fulfill", cmd_fulfill)]:
        p = sub.add_parser(name)
        p.add_argument("--state-dir", required=True)
        p.set_defaults(fn=fn)
    args = parser.parse_args()
    return args.fn(args)


if __name__ == "__main__":
    sys.exit(main())
