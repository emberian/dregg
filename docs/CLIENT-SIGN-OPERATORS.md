# Client signing operators

## Behaviour contract

These features change HTTP/client transport only. They do not change turn,
receipt, signature, consensus, or effect encodings. An ingress credential never
replaces the signature or the existing admission checks.

`dregg-client-sign daemon --socket PATH --batch-window-ms N --max-batch K
--profile P --topic anchors` keeps one profile loaded. Fund the profile first
with the existing `join` flow; the daemon does not issue funding turns. It needs
the same verified signing cores as `send`. One newline-terminated
JSON request per Unix connection supplies `id`, `topic`, and `digest` (64 hex
characters). The ID is a durable idempotency key. A reused ID with different
contents is refused. Different IDs with identical digests remain distinct leaves.
The socket is published with mode 0600; an OS lock keyed by the public identity
excludes another daemon even if it specifies a different socket. The caller must
have access to the profile, and other signing programs must not concurrently
spend its nonce.

The first new request starts the window. Up to K requests enter one batch;
K is bounded at 4096. Every leaf binds its supplied topic. The single EmitEvent
uses the daemon's `--topic`, and carries the lowercase hex Merkle root through
the existing `prepare_send` payload/memo encoding. Mixed leaf topics are allowed.

A reply has `outcome: receipted`, `turn_hash`, `receipt_hash`, `leaf_index`,
`sibling_path`, `merkle_proof`, `witness` (the local signed-turn file path), and
`finality`. `receipted` means the node returned a matching receipt; it does not
upgrade tentative finality or assert independently verified consensus. Save
`merkle_proof` to a JSON file and run:

```
dregg-client-sign verify-anchor --witness FILE --merkle-proof PROOF.json --topic anchors
```

The proof includes the original topic and digest; the auditor must compare them
to the intended input. Existing `verify-anchor` finality/committee options apply.
A standalone proof establishes inclusion only, not finality.

Requests are persisted as `undecided` before preparing or posting. Signed bytes
and their hash are persisted before the POST. The terminal reply is persisted
before writing it to any socket. Exact retries return the recorded result and
never POST again. An interrupted connection is **not** a success: reconnect with
the same ID. After a crash, pending IDs return `undecided`, with the witness and
turn hash if signing completed. Any pending outcome blocks new nonce allocation.
This implementation deliberately requires operator reconciliation of an
undecided journal before accepting new work; it does not automatically retry
ambiguous submissions. Journals and witnesses live in the profile directory's
`daemon-<public-key>` subdirectory. The journal pins the node URL and anchor
topic and refuses to reuse cached receipts under a different configuration. Do not delete an undecided journal to unblock
it: reconcile its exact turn hash with the node first. An owned stale socket is
removed on restart only when its device/inode matches the persisted record.

## Merkle format (client-only v1)

BLAKE3 leaves hash `dregg-anchor-leaf-v1 || count:u64le || index:u64le ||
topic_utf8_length:u64le || topic_utf8 || digest:32`. Inner nodes hash
`dregg-anchor-node-v1 || left:32 || right:32`. Odd levels duplicate their final
node; a single leaf is its own root. Proofs include count and index, and require
exact path depth and the canonical odd-node sibling. Domain separation prevents
substitution of an internal node as a leaf digest. JSON byte arrays are used for
proof hashes; the socket request digest and emitted root use hex.

## Attenuated HTTP bearers

`POST /api/auth/mint-ingress` takes JSON `{agent: hex32, topic: string,
expires: unix_seconds}` behind the full bearer. `mint-bearer --agent CELL --topic
S --expires UNIX --token-file FULL_BEARER_FILE` calls it without needing signer
keys; `--profile P` may replace `--agent CELL` to select a local profile. The returned token is
sensitive; store it like a bearer. Use `Authorization: Bearer em2_...` (or the
existing signer token-file option).

The macaroon root key is the existing `dregg-api-bearer-v1` derivation of the node
bearer seed. Purpose `dregg-api-ingress-v1` and first-party caveat types 80..83
bind agent bytes, literal `EmitEvent`, topic symbol bytes, and expiry u64le.
The topic caveat constrains the emitted anchor topic; leaf topics are committed
metadata, not additional emitted events.
All caveats, including added caveats, are ANDed. Unknown caveats fail closed.
Expiry is exclusive (`now < expires`). Only `/turns/submit` and
`/api/turns/submit-signed` admit these tokens; the similarly named unsigned
route, mint endpoint, and all other operator endpoints require the full bearer.

After decoding the signed turn and before admission, every effect must be an
EmitEvent for the permitted agent and topic. Nonzero action balance deltas and
empty actions are refused too. Failures return `accepted:false`
and `error: ingress-caveat-failed:<name>`. Malformed or forged credentials fail
authentication with HTTP 401 before decoding. The node still verifies the signed
turn through the unchanged admission path. Full bearer behaviour is preserved.

## Receipt projection

`GET /api/starbridge/receipts` includes `emitted_events`, with each event's topic
as hex32 and `data_digest`. The digest hashes `dregg-api-event-data-v1 ||
field_count:u64le || field_0:32 || ...` with BLAKE3. It describes the stored event
data fields, not the original unpadded application string. This is a read-only
projection and does not alter the receipt commitment.

## Verification on a host with verified signing cores

The composed test counts actual HTTP submissions, verifies both callers' signed
witnesses, retries across daemon restarts, and interrupts a durable window before
posting. Run on a host with a matching verified archive:

```
DREGG_TEST_REQUIRE_LEAN=1 CARGO_TARGET_DIR=./target-dep CARGO_BUILD_JOBS=4 cargo test -p dregg-sdk-net --features test-support --bin dregg-client-sign daemon_composed_
```

Keep the Lean requirement armed: a skipped signing fixture is not an end-to-end
success. The pure `daemon_`, `merkle_anchor`, `mint_bearer`,
`ingress_caveats_have_teeth`, and node `ingress_operator_` filters exercise the
socket, journal, proof, authentication, and read-projection boundaries separately.
