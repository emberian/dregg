# Initiative 9 — attested transport composed with receipts (call-tree certificates)

Register row (2026-11-06): `| 9 | Attested transport + receipts (MPC-TLS call-tree certificates) | lane 9 (Opus 5.5) | breadstuffs | L3 | one real HTTPS call tree certified end to end, a receipt per hop, dataflow edges checked, offline one-command verify | typed JSON-field edges keyed by call id; verifier challenge; independent notary; renter-anchored root | 2026-11-06 |`

Ember's target: "combine with tlsnotary and you can certify entire distributed api call trees."

## 1. What exists (read, with paths) and what each actually gives

| Piece | Path | What it really does today | Reuse? |
|---|---|---|---|
| MPC-TLS backend | `zkoracle-live/src/tlsn_live.rs`, `tlsn_bedrock.rs`, `notary_server.rs`, `verify.rs` | Real TLSNotary 2PC (tlsn **v0.1.0-alpha.15**, rev `47aee45`) against live hosts. `run_url_roundtrip_blocking(host, path)` = GET any public host; `tlsn_bedrock` = SigV4 POST to Bedrock with the `Authorization` value redacted. `verify_coinbase_presentation` pins host + notary key, runs `presentation.verify()` with Mozilla roots, returns the authenticated sent/recv bytes. | **Reused as the per-hop transport.** Needs: a generic POST (body + redacted secret header) path, and the notary on a different machine. |
| Notary | `zkoracle-live/src/notary_server.rs` | A notary on a TCP socket with a durable key file. **But every roundtrip spawns it inside the prover's own process** (`spawn_hosted_notary` in `run_*_inner`) — "separate" in socket only; the prover's process holds the notary key. | Reused, but run as its own process on bb2 for the real tree. |
| zkOracle 3-leg attestation | `zkoracle-prove/src/attestation.rs` | authentic ∧ well-formed (CFG cert) ∧ injection-free, welded by an 8-lane Poseidon2 `content_commitment` over the authenticated body. `AuthenticPolicy::RequireMpcTls` + `MpcTlsLeg` injection. | Optional per-hop enrichment for LLM hops (later); not required for the tree. |
| Lean zkOracle | `metatheory/Dregg2/Crypto/ZkOracle.lean` | `zkOracle_sound` conjoins three legs **taken as independent inputs** (its own SCOPE note: cross-leg binding not modeled); the authentic leg is the Stripe/DECO model `Deco.lean`, not TLSNotary's notary-signed attestation. | Not the transport model for this tree. Trust carrier for a hop is stated fresh (§5). |
| grain turn-cell | `grain-turn/src/lib.rs` | `ToolGatewayMinter`: each admitted action is a committed executor turn; slots HISTORY_ROOT(3, Blake3 MMR over prior receipt hashes), CALLS_MADE(4), CONSUMED(5), HEAP_ROOT(6), ACTION(7, `action_commit(label,cost)`), ATTESTATION(8, caller 32-byte commit, `bind_attestation`). | **Reused, not forked**: each hop is minted as one grain turn with its node commitment bound at ATTESTATION_SLOT; the tree root is the last turn's ATTESTATION. Ordering of hops comes free from HISTORY_ROOT. |
| ToolGateway | `sdk` (`dregg_sdk::ToolGateway`) | rate/deadline/scope mandate, `calls_made` FieldLte+Monotonic enforced by the executor. | Reused through `ToolGatewayMinter`. |
| grain-verify R0–R3 | `grain-verify/src/lib.rs`, `r3.rs` | R0–R2 landed: chain/budget/receipt verification, renter anchor, turn linkage; R3 whole-history STARK is the named gap. | The tree verifier sits beside it: grain-verify checks the turn chain; the tree checker checks the tree against the root that chain committed. |
| MMR (Lean) | `metatheory/Dregg2/Lightclient/MMR.lean` | `mroot`, `mroot_binds_or_collides` (unconditional, total extractor `mrootFind`), `server_cannot_omit_position`, `light_client_position_non_omission`. Abstract `hash : List ℤ → ℤ`. | **Reused**: children roots are `MMR.mroot`. Its "1 felt ≈ 2^15.5" caveat does not apply here: we instantiate `hash` at BLAKE3-256 (§4). |
| MMR (Rust) | `dregg-query/src/mmr.rs` (`Blake3Mmr`) | 32-byte BLAKE3 MMR used by grain history. Different byte scheme from the Lean `mroot`. | Not used for the tree root: the tree root must be what the Lean checker recomputes, so the Rust recorder produces Lean's scheme (a producer, never a verifier). |
| BLAKE3 in Lean | `metatheory/Dregg2/Crypto/Blake3Compute.lean` | Pure-Lean computable BLAKE3, core-only imports, KAT-pinned (compiler-trusted identity). | **Reused**: the Lean checker hashes every byte string itself. |
| Extracted-checker pattern | `metatheory/DfaRun.lean`, `Policyc.lean`, `DatalogCheck.lean` (lakefile `[[lean_exe]]`) | Core-only Lean exe reads JSON, decides, exits 0/1. | **Followed** for `calltree-check`. |
| deco-prove `tlsn_live.rs` | `deco-prove/src/` | Older Stripe copy of the same live path. | Not used. |

What the 2026-07-06 "full fusion" wired: one attestation commitment per grain turn (the brain that drove the action). What it left: no notion of a *call tree*; no binding between a hop's attested bytes and the next hop's request; notary co-resident with the prover; the Anthropic path never pointed at a real host (Bedrock was).

## 2. Outside, and what each proves

- **TLSNotary alpha.15** (2026-05-21, the latest release; our pinned rev *is* it). Two commitment modes: **MPC** (prover and notary jointly run the TLS client; the notary sees no plaintext, holds a key share; soundness needs notary non-collusion with the prover) and **proxy** (new in alpha.15: the notary relays the encrypted traffic and the prover proves in ZK about it; soundness additionally needs the prover not to control the network path between notary and server). Output is a notary-signed `Attestation` (secp256k1) over the server identity, the connection time, and transcript commitments; the `Presentation` reveals chosen ranges. TLSNotary's own 2026-06-17 post: the proof is designated-verifier; "publicly verifiable" means "verifiable by whoever trusts that notary". Main since alpha.15 has a notary DoS fix (#1196, unbounded commit ranges) and moves connection time from prover-supplied (±5 s checked) to notary receipt time (#1209). Neither is a soundness break for us.
- **DECO** (Zhang et al., CCS 2020): three-party handshake, verifier holds a MAC key share; same trust shape as MPC mode. `Dregg2/Crypto/Deco.lean` models a DECO verifier kernel.
- **PageSigner / TLSNotary v1**: notary-held MAC key, TLS 1.0/1.1-era; superseded.
- **Janus** (PoPETs 2025): proxy-model data provenance with a faster garbled-circuit split. **Reclaim / zkPoPE** (ePrint 2026/2187): the first transport-agnostic UC definition ("proof of protocol execution"), and Reclaim realizing it with a three-party AEAD. **zkPass hybrid**, **Primus** (MPC/proxy, QuickSilver), TEE-based (Opacity, Phala).
- **Agent-level**: Primus "Verifiable AI Agent Execution" — a zkTLS proof per step checked against a policy; no tree, no commitment to the set of steps (an omitted step is invisible unless the policy names it). **zkAgent** (ePrint 2026/199, CCS 2026) — SNARK over open-weight inference with zkTLS/zkVM subproofs for tool observations; does not apply to a closed API.
- **Trace trees**: OpenTelemetry spans carry no signatures or commitments. **Sigstore Rekor**: Merkle transparency log with inclusion and consistency proofs — the append-only/omission half, no transport attestation.

**What ours adds**: (a) a Merkleized call tree whose root binds every hop and the *exact* child list (non-omission, reorder and splice detection) under a named-pair collision extractor rather than an assumed CR floor; (b) **distributed nesting**: a callee that also records returns its subtree root inside its HTTPS response, so the caller's attestation binds the callee's subtree; (c) **dataflow edges**: a hop's request is checked to contain the bytes a previous attested response produced (the tool_result the agent sends the model is the tool's attested output; the tool call's arguments are the model's attested tool_use); (d) the accept decision is a Lean function with proved soundness; (e) the root lands in a committed grain turn whose history is MMR-bound.

## 3. Decision: is zkoracle-live current?

**Yes. No re-base.** The pinned rev is alpha.15, the newest release. Re-base trigger: alpha.16 (it will carry #1196/#1209). Proxy mode is cheaper but adds a network assumption; MPC stays the default per hop, proxy is allowed only if the hop's record says so and the policy admits it. Every live host we need negotiates `ECDHE-*-AES128-GCM-SHA256` over TLS 1.2 (probed today: api.anthropic.com, bedrock-runtime.us-east-1, api.github.com, example.com, en.wikipedia.org, raw.githubusercontent.com), which is the suite tlsn implements.

## 4. Design (what gets built)

**Lean** (`metatheory/Dregg2/Lightclient/CallTree.lean` + core-only `CallTreeCore.lean`):
`Hop = (kind, att, host, req, resp)`; `CallTree = node Hop (List CallTree)`;
`commit t = hash [kind, att, host, req, resp, mroot (kids.map commit)]` (arity 6; MMR uses 0/1/2, so domains are separated by arity).
`verify V root t := commit t = root ∧ every node passes V hop (kidsRoot)`.
Theorems: `commit_binds_or_collides` (total extractor `treeFind`; an `∃ collision` form would be vacuous for any compressing hash), `verify_sound` (accept ⇒ every node of every tree with that root passes V, or `treeFind` names a collision), the non-omission corollary (no child dropped, added, reordered, swapped), the transport carrier (`V` accept on a transport hop ⇒ `Attested hop`), and falsifiers by `decide`: dropped child, swapped response, attestation for a different host, kid reorder.
`hash` at deployment: `BLAKE3("dregg-calltree-v1" ‖ injective encoding of the ℤ list)` read as a 256-bit integer.

**V, decided in Lean** per hop kind: 0 = local turn node (no transport); 1 = attested HTTPS hop: `att = H(presentation)`, `host = H(server_name)`, `req = H(sent)`, `resp = H(recv)`, notary key ∈ pins, server name ∈ policy hosts; 2 = attested hop to a recording callee: kind 1 plus the hex of `mroot(kids)` occurs in the authenticated response. Dataflow edges are a second Lean check over the authenticated bytes.

**Rust** (`calltree/`, crate `dregg-calltree`): recorder wrapping outbound HTTPS through `dregg-zkoracle-live` (generalized to POST with a redacted header), minting each hop as a grain turn via `ToolGatewayMinter::bind_attestation` + `mint_turn`; a tool server that records its own page fetch and returns its subtree root; a verifier CLI that runs `presentation.verify()` (the only Rust-decided step, and it only *extracts*: server name, notary key, authenticated bytes) and hands the tree, the presentations and the extracts to the Lean exe `calltree-check`, whose exit code is the verdict.

## 5. Trust model per hop (stated, not hidden)

| Hop | Mode | A stranger trusts |
|---|---|---|
| agent → Bedrock (LLM) | MPC-TLS, notary on bb2 | ember's notary key not colluding with the prover; AWS's cert chain (WebPKI). SigV4 `Authorization` redacted. |
| agent → tool server | MPC-TLS | same notary; the tool server's identity is a **pinned self-signed cert** unless ember gives it a public name (decision below). |
| tool server → page | MPC-TLS | same notary; WebPKI for the page host. The tool server's subtree root is bound by the agent's attested response from it. |
| root (agent turn) | none | the recorder's commitment; landed in a grain turn. |

## 6. What a verified root does NOT prove (seed for the cross-model attack)

Not liveness (a recorder can stop or never publish). Not completeness against **unrecorded** calls: non-omission is relative to the committed tree; a bypassing agent's extra calls are invisible unless a dataflow edge needs them. Not timing or order beyond tlsn's notary-clock connection time and the grain history order. Not the notary's honesty (MPC: non-collusion; proxy: plus the network path). Not that the LLM "meant" the tool call — only that the bytes match. Not freshness against replay of an old attestation unless the policy bounds connection time. The `presentation.verify()` → extract step is Rust TCB.

## 7. The bar, amended

The original bar (a receipt per hop, root as a single object, offline one-command verify) is kept and raised by two things a per-hop zkTLS tree lacks: **dataflow edges** checked over authenticated bytes, and **distributed nesting** bound through the callee's attested response. Without those, "certified call tree" is a bag of independently attested calls with a hash over them, which Primus already ships.

## 8. Decisions only ember can make

1. A public name + WebPKI cert for the tool server (e.g. a dregg.online subdomain), or keep the pinned self-signed cert for L3.
2. Which notary key a stranger should pin: ember's bb2 notary (default), or an independent operator.
3. Bedrock spend on `commonquant-ember` for the real tree (two small `converse` calls per run; the repo already uses this profile).

## 9. Cross-model round 1 (gpt-6-astra, 2026-11-06), adjudicated

Verdict: the binding extractor is meaningful (`treeFind` follows the trees' own preimages; its fallback `([], [])` can never be a `SpongeColl`). Findings and what was done:

| # | Finding | Action |
|---|---|---|
| 1 | Kind-0 downgrade: any node relabelled local skips `V`. | **Fixed**: `verify` now requires the root to be kind 0 and every descendant kind ≠ 0 (`allOkL isTransport`); `verify_sound` exports it; falsifier `relabelled_local_refused`. `deployedV` admits only kinds 1 and 2. |
| 2 | `Attested : Hop → Prop` cannot say the kind-2 child root is authenticated. | **Fixed**: carrier is `Attested : Hop → ℤ → Prop` over the hop and its children root; `verify_attested` concludes `Attested n.hop (kidsRoot n.kids)` for every descendant. |
| 3 | `other_host_refused` was confounded (the attested host was also off the allowlist). | **Fixed**: att 104 now authenticates an *allowed* host; refused by host comparison alone. `unlisted_host_refused` isolates the allowlist. |
| 4 | Docstring claimed MMR arities separate peak nodes from bags (both arity 2). | **Fixed** wording; tree preimages (arity 6) are disjoint from all MMR preimages. |
| 5 | Residual non-vacuity. | **Added** `treeFind_self`, `treeFind_self_not_coll`: on an honest pair the extractor names nothing, for every hash. |
| 6 | Deployment bridge: `SpongeColl treeHash p → BLAKE3 collision` needs `encList` injectivity; content digests need their own reduction. | **Open (L2 gate)**: prove `encList_injective` + `ofBE` injectivity on 32-byte outputs in `CallTreeDeploy`. |
| 7 | No premise authenticates `root` as this run's root; replay/duplication of valid hops into a fresh tree is accepted; no freshness. | **Open (L2 gate)**: the root is read from the committed grain turn (ATTESTATION_SLOT of the turn whose history grain-verify checks), and the policy bounds connection time per hop against the turn; a uniqueness check rejects one presentation used twice. Stated as composition theorems, not as `verify` itself. |
| 8 | Dataflow and partial disclosure are not in `verify`. | **Open (L3 gate)**: dataflow check over authenticated bytes as a second Lean decision; partial disclosure via MMR openings (`MMR.server_cannot_omit_position`). |
| 9 | Bypass (unrecorded calls) and recorder completeness cannot come from tree binding. | **Accepted as a limit** (§6); dataflow edges bound what a bypass can hide, nothing more. |

## 10. L2 construction (2026-11-06/07)

Reversible defaults per the root, then ember's answers: the LLM hop is **GLM `glm-5.3-flash` on the Z.AI coding-plan endpoint** (`api.z.ai/api/coding/paas/v4/chat/completions`, key at `~/.zai-key`, never printed; no Bedrock). Probed: `api.z.ai` negotiates TLS 1.2 `ECDHE-RSA-AES128-GCM-SHA256`, the suite tlsn implements; a plain non-streaming tool-call request returns `tool_calls` with the URL verbatim in `arguments`. Tool server: a **self-signed root pinned by the verifier** (`--extra-root`), no public name. Notary: **the bb2 notary as its own process**; its operator and key are recorded in every recording, and the verifier's policy (not the recording) pins the key.

| Piece | Where | What it does |
|---|---|---|
| hop prover | `zkoracle-live/src/tlsn_hop.rs` | `prove_hop_blocking(HopRequest, notary_addr)`: any method/headers/body, header VALUES in `redact_headers` hidden (names shown), connect address separate from SNI, extra roots. Same lock and stack as the Bedrock path. |
| extractor | `zkoracle-live/src/tlsn_hop.rs::extract_presentation` | `presentation.verify()` and nothing else: server name, `alg:hex` notary key, notary time, authenticated sent/recv (`X` where hidden). No pin, no policy. |
| notary | `zkoracle-live/src/bin/tlsn-notary.rs` | durable key, `--extra-root`, one session per connection, PID file. |
| recorder | `calltree/src/main.rs record` | GLM hop (tool_use) → tool hop (kind 2) → GLM hop (tool_result); refuses to record if a redacted header value is visible in the disclosed bytes; builds edges; mints every node post-order as a grain turn through `ToolGatewayMinter::bind_attestation` + `mint_turn` (public API only; the other lane's uncommitted `grain-turn` edits are not touched). |
| tool server | `calltree/src/main.rs tool-serve` | HTTPS (self-signed) `POST /fetch {url}`: an attested GET of the page through the same notary, returns a verbatim safe-character span of the authenticated page bytes plus its subtree root; the subtree file is fetched out of band (bound by the root inside the attested response). |
| verifier | `calltree/src/main.rs verify` | extract each presentation → bundle → `lake exe calltree-check`; exit code is Lean's. Reports the grain anchor separately (`ATTESTATION_SLOT` = root and `verify_grain_history` = Bound). |
| Lean | `CallTreeDeploy.lean` | `deployedVerify` now also requires: notary time inside the policy window; no presentation used by two hops (`nodupB (atts t)`); every listed dataflow edge holds over authenticated bytes (kind 0 response→later request, kind 1 callee response→caller response, ≥ 16 bytes, both ends in the tree) and every policy-required (kind, host, host) edge is witnessed. `deployedVerify_verify` transfers every `CallTree` theorem. |
| bridge | `CallTreeDeploy.lean`, `CallTree.lean §5` | `encList_injective`, `ofBE_injective_of_size`, `Blake3.hash_size`, `treeHash_coll_is_blake3_coll`, `deployed_coll_is_blake3_coll`: a `SpongeColl treeHash` at a `treeFind` pair is a BLAKE3-256 collision on distinct messages (bounds: < 2^32 elements, < 2^32 bytes each). Closes §9 item 6. |

## 11. Cross-model round 2 (gpt-6-astra, recorder bypass and verifier trust), adjudicated

Verdict: "the claimed property fails" as first built. Findings and actions:

| # | Finding | Action |
|---|---|---|
| 1 | **Critical**: the grain anchor is recording-supplied; a copied cell with a new ATTESTATION slot passes `verify_grain_history`. | **Demoted, not hidden**: the anchor is now reported as `host_asserted_grain_anchor` and is NOT part of the exit code. The root a stranger trusts comes from `--root` (obtained out of band: the signed commit that lands the fixture, the microsite); without it the verdict says `root_source: recording (self-asserted)`. A real anchor needs grain-verify's renter-anchored / R3 path: **open (L3+)**. |
| 2 | **High**: `X`-masked bytes let an edge be made of masked positions. | **Fixed**: the extractor masks with `0x00`; every Lean byte check (`inBody`) refuses a span containing `0x00`, so spans match authenticated bytes only. |
| 3 | **High**: substring edges can use header boilerplate (`application/json`) and match any two calls to the right hosts. | **Partly fixed**: spans must lie in the authenticated HTTP BODY on both sides; kind-0 edges must go forward in tree order; kind-1 edges must go child → parent. **Open (L3)**: typed JSON-field edges keyed by tool-call id. |
| 4 | **High**: relabel kind 2 → 1 keeps children unchecked; any response containing a hex string satisfies kind 2. | **Fixed**: kind 1 must be a leaf (`kr = mrootC treeHash []`); kind 2 only for policy-listed `recorders`, and the root must sit in the designated field `"subtree_root":"<hex>"` inside the authenticated body. Residual: a listed recorder can still return a root for a subtree it did not execute; its own hops are each attested, so what it can fake is the *assignment* of hops to the call, not the hops. |
| 5 | **High**: bincode 1.3 tolerates trailing bytes, so `P‖00`, `P‖01` are distinct `att` digests for one presentation; different disclosures of one session also evade `nodupB`. | **Fixed**: `reject_trailing_bytes()`; and Lean requires the signed SESSIONS (hex of the attestation header: id, version, field root) behind the hops to be distinct. |
| 6 | Checker invocation: shared temp path, verdict not bound to the root. | **Fixed**: the bundle goes over stdin (`calltree-check -`); the CLI accepts only if the checker's echoed `root` equals the trusted root. The checker binary is whatever the stranger built (`lake build calltree-check`). |
| 7 | Recorder completeness; root prompt/answer unattested; redaction checks sent bytes only. | **Limit, restated** (§6). Root `req`/`resp` digests are the recorder's claim. |
| 8 | Extra roots were global CAs. | **Fixed**: `--extra-root host=path` pins are host-scoped — tried only after Mozilla refuses, and must authenticate exactly that host. Freshness/challenge: **open**. |

## 12. The real tree (2026-11-06, bb2)

Notary `k256:02dffefb…c0f925` (`fixtures/notary.pin`) as its own process on bb2, bound to localhost; the tool server and the recorder as separate processes on the same box (one operator: ember). The recorder and tool server link the Lean-built executor archive (`libdregg_lean.a` copied from a same-day bb2 clone); without it the verified admission oracle refuses every grain turn fail-closed (measured), which is the right behaviour.

| Recording | Hops | Record wall | Per-hop MPC-TLS (ms) | Verify wall (extract + Lean) |
|---|---|---|---|---|
| `fixtures/glm.recording.json` — GLM `glm-5.3-flash` asks for `fetch_page`, the tool fetches `https://example.com/` through its own attested hop, GLM answers "This page exists as a domain reserved for use in documentation examples, without needing permission." | 4 (2 × api.z.ai, tool, example.com) | 36.4 s | 7712, 6473, 3314, 5442 | 0.06 s (extract 4 ms, Lean 57 ms) |
| `fixtures/free.recording.json` — free mode (example.com direct; tool → en.wikipedia.org REST summary) | 3 | 29.2 s | — | 0.06 s |

Edges in the GLM tree: kind 0 `https://example.com/` (GLM response → tool request); kind 1 the page's text span (example.com response → tool response, child → parent); kind 0 the same span (tool response → GLM's second request). No key material: the `Authorization` value is hidden in every LLM presentation (checked by the recorder, and the raw key bytes and their hex occur 0 times in the decoded presentations and the recording; the key file was shredded after the run).

Falsifiers run against both real recordings (`run/falsify.py` on bb2): honest ACCEPT; dropped child, reordered children, tool relabelled 2→1, tool subtree dropped, a flipped presentation byte, a trailing presentation byte, a header-boilerplate edge span, a masked (`0x00`) edge span, a missing required edge, a wrong trusted root: each REJECT, with the failing component named (`tree_and_hops` / `edges_ok`).

Stranger path: `calltree/verify/run.sh` (the light `dregg-calltree-verify` crate links only the tlsn extraction, not the grain executor; the Lean checker is core-only). Policy says facts about concrete data are compiled evaluations: the demo falsifiers are `native_decide` + `#assert_compiled`; the general theorems stay kernel-proved.

Stranger rehearsal (bb2, 2026-11-06): a fresh `--sparse --filter=blob:none` clone of github.com/emberian/dregg (19 s; only metatheory, calltree, zkoracle-live, zkoracle-prove, circuit, dfa, dregg-codec, dregg-dsl, vendor), the Mathlib package store symlinked from an existing clone (the checker is core-only and builds no Mathlib module), then `calltree/verify/run.sh`: 57 s wall, 1.58 GB peak RSS, ACCEPT on `fixtures/glm.recording.json` (extract 7 ms, Lean check 92 ms). Page: dregg-microsites `call-tree/` (local commit; publication is a separate step).
