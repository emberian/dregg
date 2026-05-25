"""Canonical hashing + commitment derivation for the cross-app-e2e demo.

Uses the real `blake3` Python module so the commitments computed here
byte-equal what the Rust starbridge-apps produce — same domain-keyed
derivation, same byte ordering, same digest size.

The shape mirrors:
- `pyana_cell::program::AuthorizedSet::credential_set_commitment`
- `starbridge_identity::schema_commitment`
- `starbridge_subscription::bounty_state_payload_hash`
- `starbridge_nameservice::resolve_target` / `name_hash`
- `pyana_app_framework::FieldElement` (32-byte big-endian-padded u64)
"""

import blake3


def hash_keyed(domain: str, *parts: bytes) -> bytes:
    """Domain-separated keyed hash, mirroring `blake3::Hasher::new_derive_key`.

    The Rust call shape is `blake3::Hasher::new_derive_key(domain)` then
    `update(p)` for each part. We reproduce the same byte-level digest.
    """
    h = blake3.blake3(derive_key_context=domain)
    for p in parts:
        h.update(p)
    return h.digest()


def hash_blake3(*parts: bytes) -> bytes:
    """Un-keyed BLAKE3 hash, mirroring `blake3::hash`."""
    h = blake3.blake3()
    for p in parts:
        h.update(p)
    return h.digest()


def blake3_field(data: bytes) -> bytes:
    """Mirrors `pyana_app_framework::FieldElement` byte form (32 bytes)."""
    return hash_blake3(data)


def u64_field(value: int) -> bytes:
    """Big-endian-padded 32-byte u64, matching `u64_field` in the apps."""
    return b"\x00" * 24 + value.to_bytes(8, "big")


def cell_id_field(cell_id: bytes) -> bytes:
    """A `CellId` is 32 bytes; pass-through."""
    assert len(cell_id) == 32
    return cell_id


# ─── Cross-app commitment derivations ──────────────────────────────────


def credential_set_commitment(issuer_cell: bytes, schema_commitment_bytes: bytes) -> bytes:
    """Mirror of `AuthorizedSet::credential_set_commitment`.

    Byte-equal to the Rust:
        let mut hasher = blake3::Hasher::new_derive_key("pyana-credential-set-v1");
        hasher.update(issuer_cell);
        hasher.update(credential_schema_id);
        *hasher.finalize().as_bytes()
    """
    return hash_keyed("pyana-credential-set-v1", issuer_cell, schema_commitment_bytes)


def schema_commitment(schema_name: str, attributes: list[str]) -> bytes:
    """Mirror of `starbridge_identity::schema_commitment`.

    Byte-equal to the Rust:
        let mut hasher = blake3::Hasher::new_derive_key("pyana-credential-schema-v1");
        hasher.update(schema.name.as_bytes());
        hasher.update(&(schema.attributes.len() as u64).to_le_bytes());
        for attr in &schema.attributes {
            hasher.update(&(attr.len() as u64).to_le_bytes());
            hasher.update(attr.as_bytes());
        }
    """
    parts: list[bytes] = [schema_name.encode("utf-8")]
    parts.append(len(attributes).to_bytes(8, "little"))
    for attr in attributes:
        parts.append(len(attr).to_bytes(8, "little"))
        parts.append(attr.encode("utf-8"))
    return hash_keyed("pyana-credential-schema-v1", *parts)


def bounty_state_payload_hash(
    bounty_id: bytes,
    prior_tag: int,
    new_tag: int,
    actor_pk_hash: bytes,
) -> bytes:
    """Mirror of `starbridge_subscription::bounty_state_payload_hash`."""
    return hash_keyed(
        "pyana-bounty-state-v1",
        bounty_id,
        bytes([prior_tag]),
        bytes([new_tag]),
        actor_pk_hash,
    )


# Canonical BountyState tag values, mirroring `starbridge_subscription::BountyState::tag`.
BOUNTY_POSTED = 1
BOUNTY_CLAIMED = 2
BOUNTY_FULFILLED = 3
BOUNTY_SETTLED = 4
BOUNTY_CANCELED = 5


def resolve_target(uri: str) -> bytes:
    """Mirror of `starbridge_nameservice::resolve_target`."""
    return blake3_field(uri.encode("utf-8"))


def name_hash(name: str) -> bytes:
    """Mirror of `starbridge_nameservice::name_hash`."""
    return blake3_field(name.encode("utf-8"))


# ─── Witnessed-predicate / authorized-set shapes ───────────────────────


def witnessed_predicate(
    kind: str,
    commitment: bytes,
    input_ref: str,
    proof_witness_index: int,
) -> dict:
    """Build a `WitnessedPredicate` dict for the receipt-chain artifacts."""
    return {
        "kind": kind,
        "commitment": commitment.hex(),
        "input_ref": input_ref,
        "proof_witness_index": proof_witness_index,
    }


def authorized_set_credential(issuer_cell: bytes, schema_commitment_bytes: bytes) -> dict:
    """Build an `AuthorizedSet::CredentialSet` shape."""
    return {
        "type": "CredentialSet",
        "issuer_cell": issuer_cell.hex(),
        "credential_schema_id": schema_commitment_bytes.hex(),
        "resolved_commitment": credential_set_commitment(
            issuer_cell, schema_commitment_bytes
        ).hex(),
    }


def sender_authorized_credential_constraint(
    issuer_cell: bytes, schema_commitment_bytes: bytes
) -> dict:
    """Build a `StateConstraint::SenderAuthorized { CredentialSet }` shape."""
    return {
        "type": "SenderAuthorized",
        "set": authorized_set_credential(issuer_cell, schema_commitment_bytes),
    }


def credential_witness_predicate(
    issuer_cell: bytes,
    schema_commitment_bytes: bytes,
    proof_witness_index: int,
) -> dict:
    """Build the predicate an action carries to discharge a credential constraint.

    Mirrors `starbridge_identity::credential_set_predicate` /
    `starbridge_nameservice::identity_attested_witness_predicate` /
    `starbridge_governed_namespace::credential_gated_witness_predicate`.
    All three return identical shapes pointing at the same commitment —
    the *whole point* of the cross-app composition contract.
    """
    return witnessed_predicate(
        kind="BlindedSet",
        commitment=credential_set_commitment(issuer_cell, schema_commitment_bytes),
        input_ref="Sender",
        proof_witness_index=proof_witness_index,
    )
