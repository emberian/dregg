#!/usr/bin/env python3
"""alice.py — identity-issuer side of the cross-app-e2e composition story.

Alice creates an identity-issuer cell and issues a "verified-developer-v1"
credential to Bob. The receipt artifact pinned to disk records:

  - alice_issuer_cell:        the issuer cell-id
  - alice_pk_hash:            Alice's pubkey hash (her issuer signing key)
  - schema_name + attrs:      the credential schema (verified-developer-v1)
  - schema_commitment:        canonical commitment to the schema
  - bob_credential_id:        the credential's 32-byte id (issued to Bob)
  - bob_holder_id:            Bob's cell-id as the credential holder
  - issuance_counter:         the issuer cell's MonotonicSequence-bound counter
  - revocation_root:          the issuer cell's REVOCATION_ROOT_SLOT value

The substrate primitives this step exercises:
  - issuer_factory_descriptor (Immutable SCHEMA_COMMITMENT_SLOT,
                              MonotonicSequence ISSUANCE_COUNTER_SLOT,
                              Monotonic REVOCATION_ROOT_SLOT)
  - schema_commitment (canonical)
  - the issuer's authorized-issuer set (PublicRoot)
"""

import argparse
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

from canonical import schema_commitment, blake3_field  # noqa: E402


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--state-dir", required=True)
    parser.add_argument("--bob-cell", required=True, help="hex-encoded 32-byte cell id")
    args = parser.parse_args()

    os.makedirs(args.state_dir, exist_ok=True)

    # Deterministic issuer cell id seed (in a real run this comes from
    # the factory's `create_cell` turn; here we derive it from a fixed
    # seed so the demo is reproducible).
    alice_seed = b"alice-issuer-cell-seed"
    alice_issuer_cell = blake3_field(alice_seed)
    alice_pk_hash = blake3_field(b"alice-pk-v1")

    # The "verified-developer-v1" credential schema. The schema commitment
    # is the canonical 32-byte digest the issuer cell pins into
    # SCHEMA_COMMITMENT_SLOT.
    schema_name = "verified-developer-v1"
    schema_attrs = ["github_handle", "verified_repos", "vouching_issuer", "issued_at"]
    schema_commit = schema_commitment(schema_name, schema_attrs)

    # Issue a credential to Bob. The credential id binds the holder and the
    # attribute values; here we derive a stable id from (bob_holder, schema,
    # issuance_counter).
    bob_holder = bytes.fromhex(args.bob_cell)
    if len(bob_holder) != 32:
        print("ERROR: bob_cell must be 32 hex-encoded bytes", file=sys.stderr)
        return 2
    issuance_counter = 1
    bob_credential_id = blake3_field(
        b"credential-id|" + bob_holder + schema_commit
        + issuance_counter.to_bytes(8, "big")
    )

    # The revocation root: at issuance time the set is empty. The
    # `Monotonic(REVOCATION_ROOT_SLOT)` caveat permits the root to grow
    # in subsequent revoke turns.
    revocation_root = bytes(32)

    out = {
        "agent": "alice",
        "step": "issue_credential",
        "alice_issuer_cell": alice_issuer_cell.hex(),
        "alice_pk_hash": alice_pk_hash.hex(),
        "schema_name": schema_name,
        "schema_attributes": schema_attrs,
        "schema_commitment": schema_commit.hex(),
        "bob_credential_id": bob_credential_id.hex(),
        "bob_holder_id": bob_holder.hex(),
        "issuance_counter": issuance_counter,
        "revocation_root": revocation_root.hex(),
        # The cell-program constraints the issuer cell carries (mirroring
        # `starbridge_identity::issuer_program`).
        "cell_program_constraints": [
            {"type": "Immutable", "slot": "SCHEMA_COMMITMENT_SLOT(2)"},
            {"type": "MonotonicSequence", "slot": "ISSUANCE_COUNTER_SLOT(3)"},
            {"type": "Monotonic", "slot": "REVOCATION_ROOT_SLOT(4)"},
            {"type": "SenderAuthorized", "set": "PublicRoot{ISSUER_AUTH_ROOT_SLOT(5)}"},
        ],
        # The action's method symbol (informational only, used by indexers).
        "method": "issue_credential",
    }

    out_path = os.path.join(args.state_dir, "alice.out.json")
    with open(out_path, "w") as f:
        json.dump(out, f, indent=2, sort_keys=True)
    print(json.dumps(out, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    sys.exit(main())
