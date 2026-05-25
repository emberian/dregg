# AUDIT — `intent/` crate

Scope: every file in `/Users/ember/dev/breadstuffs/intent/src/`, read in full,
with cross-referencing to the rest of the workspace where the intent crate is
consumed.

Crate manifest: `pyana-intent` (workspace member at `/intent`). Dependencies:
`pyana-cell`, `pyana-circuit`, `pyana-commit`, `pyana-token`, `pyana-trace`,
`pyana-turn`, plus crypto primitives (`blake3`, `curve25519-dalek`,
`x25519-dalek`, `globset`, `postcard`). 16,626 LOC across 16 source files.

Header `lib.rs` openly states: *"This crate is **TRANSITIONING** from
executor-trusted to trustless."* That status framing is honest and accurate —
the trustless path is wired in code but not in production deployment, and the
trust-critical primitive at its core (threshold encryption) is stubbed.

---

## `lib.rs` (~838 LOC)

- **Purpose** — Crate root. Defines the foundational matching language
  (`MatchSpec`, `Constraint`, `ActionPattern`), the discovery-time `Intent`
  type, `CommitmentId`, `StakeProof`, `FillConstraints`, and the
  epoch-scoped stake nullifier scheme.
- **Key types/functions**
  - `Intent { id, kind, matcher, creator, expiry, stake_proof,
    fill_constraints }` (content-addressed via canonical postcard +
    BLAKE3 with derived key `pyana-intent-id-v2`).
  - `IntentKind = Need | Offer | Query`.
  - `MatchSpec { actions, constraints, min_budget, resource_pattern,
    compound, predicate_requirements, strict_resource_matching }`.
  - `Constraint::Custom { predicate, value }` (fail-closed; see matcher).
  - `Match { intent_id, satisfier, proof, mode }`.
  - `VerificationMode = Trusted | Selective | Private`.
  - `StakeProof` carrying a Poseidon2 Merkle inclusion proof against the
    federation's note tree root.
  - `compute_stake_nullifier(commitment, epoch, counter)` —
    Poseidon2-based, hashed through BLAKE3 to 32 bytes; epoch-scoped so
    cross-epoch nullifiers are unlinkable.
  - Module declarations for the 15 sibling modules.
- **Notable design choices**
  - Intent IDs are derived deterministically from canonical serialization,
    not from `Debug` formatting — won't break under cosmetic refactors.
  - Stake proof retained `minimum_value` is explicitly documented as
    informational only ("cannot be verified without opening the
    commitment, so using it for access control is security theater").
    This is good — but does mean nothing in the gossip pipeline can
    actually meter spam by stake weight, only count uses-per-epoch.
  - Fence-post fix already in place: `is_expired(now) = now >= expiry`.
- **Integration status** — Consumed everywhere: `node/src/state.rs`,
  `node/src/api.rs`, `node/src/gossip.rs`, `sdk/src/wallet.rs`,
  `sdk/src/discovery.rs`, `preflight/src/checks/{intents,solver,privacy}.rs`,
  `apps/compute-exchange/src/orderbook.rs`, `app-framework/src/*`,
  `demo-agent/examples/*`, `wasm/src/{lib,bindings,privacy,runtime}.rs`,
  `teasting/tests/defi_primitives.rs`. The `Intent`, `MatchSpec`,
  `CommitmentId`, `FillConstraints` types are workspace lingua franca for
  capability shape.
- **Surprises / non-obvious**
  - The `creator` field of an `Intent` is included in the content hash. So
    two different anonymous creators posting *otherwise-identical*
    matchers produce different intent IDs — but a single creator who
    wants to refresh expiry must necessarily produce a different ID.
    There is no notion of intent revision.
  - `compute_stake_nullifier` encodes epoch as `(epoch & 0x7FFF_FFFF,
    (epoch >> 31) & 0x7FFF_FFFF)`. This is a quirky "two 31-bit halves"
    splitting rather than the more idiomatic high/low 32-bit split,
    presumably because `BabyBear` is a 31-bit prime field. The split
    yields an injective encoding for `epoch < 2^62`, which is fine for
    block heights divided by `EPOCH_DURATION_BLOCKS=1000`.
- **Open issues / TODOs / FIXMEs / stub markers** — None inline. Doc
  comments are stable.

---

## `validation.rs` (~555 LOC, ~225 SLOC of impl)

- **Purpose** — Hard size limits + structural invariants on `Intent`
  fields, applied before storage or propagation.
- **Key types/functions**
  - `ValidationError` enum with 9 variants (TooManyActions,
    TooManyConstraints, …, `ZeroBudget`, `InvalidFillConstraints`).
  - `validate_intent(&Intent) -> Result<(), ValidationError>`.
  - Constants: `MAX_COMPOUND_DEPTH=3`, `MAX_COMPOUND_SPECS=10`,
    `MAX_ACTIONS=64`, `MAX_CONSTRAINTS=64`, `MAX_STRING_LEN=256`,
    `MAX_RESOURCE_PATTERN_LEN=256`.
- **Notable design choices**
  - Min-budget of `Some(0)` is explicitly rejected as a "free-fulfillment
    bypass" — must be `None` to omit, or `>= 1` to constrain.
  - Fill constraints invariants (`min > 0`, `min <= max`) checked here in
    addition to the `FillConstraints::new` constructor — defence in depth.
  - Compound depth check is recursive and bounded.
- **Integration status** — Called from `gossip::IntentPool` (both for
  received and self-broadcast intents) and from `node/src/api.rs`
  (`pyana_intent::validation::validate_intent`).
- **Surprises** — `predicate_requirements` is not validated for size or
  string lengths. A malicious poster could attach thousands of predicate
  requirements with long attribute names.
- **Open issues** — Predicate-requirement size limit missing.

---

## `exchange.rs` (~68 LOC)

- **Purpose** — Asset metadata types for the asset-only ring solver.
- **Key types/functions**
  - `AssetId = [u8;32]`.
  - `AssetRegistry { assets: HashMap<AssetId, AssetInfo> }`.
  - `AssetType = Fungible | NonFungible { collection } | Capability { cell_id }`.
- **Notable design choices** — Pure data, no logic. `AssetRegistry` is a
  trivial wrapper, and `same_type` only returns true if BOTH assets are
  registered.
- **Integration status** — `solver.rs` and `generalized.rs` use `AssetId`.
  `AssetRegistry` itself appears to be **unused** outside this module.
  Grep confirms no external use.
- **Surprises** — Solver / generalized work directly off the `AssetId`
  bytes and never consult the registry. The registry exists but does no
  load-bearing work.
- **Open issues** — Dead infrastructure. Either wire `AssetRegistry` into
  the solver's compatibility check (so capability-class mismatches are
  detectable) or delete it.

---

## `matcher.rs` (~1507 LOC, ~590 SLOC impl + tests)

- **Purpose** — Wallet-local matching: given an intent and a set of
  `HeldCapability`s, decide if any held token satisfies the spec.
- **Key types/functions**
  - `Sensitivity = Public | Normal | Sensitive` (Sensitive is **never**
    auto-matched).
  - `HeldCapability { token_id, actions, resource, app_id, service,
    user_id, features, oauth_provider, expiry, budget, sensitivity }`.
  - `match_intent(intent, held_tokens, our_commitment, mode, now) ->
    MatchResult` — top-level entry. Handles expiry, `Query` rejection,
    `Offer`/`Need` divergence, compound dispatch.
  - `match_offer` — *inverse* matching: an offer matches if we *lack* a
    token that covers it. This is the "would I want this?" predicate.
  - `match_compound` — every sub-spec must be satisfied by some token
    (possibly different tokens for different sub-specs).
  - `satisfies_spec` and `satisfies_spec_with_custom` — the per-token
    predicate evaluator.
  - `CustomConstraintEvaluators` — registry of named predicates with
    `Fn(&str) -> bool` evaluators; default `evaluate()` returns `false`.
  - `resource_matches(token_resource, pattern)` — canonical resource
    matching (glob via `globset`, plus wildcard prefix handling). Shared
    with `fulfillment.rs`.
- **Notable design choices**
  - **Fail-closed custom constraints**: `constraint_satisfied` for
    `Constraint::Custom` returns `false` unconditionally. Callers must
    use `satisfies_spec_with_custom` with a registered evaluator. This
    is unusually principled and the in-line ADVERSARIAL tests guard the
    invariant.
  - Offer-matching using "we lack this" semantics (an Offer matches when
    we don't already hold something covering it) is a clever inversion
    of the Need direction.
  - Proof generation in Selective/Private mode hashes intent_id +
    token_id + 32 random bytes (the nonce prevents cross-match
    correlation, per the inline issue-#3 note). The "Private" mode
    *isn't actually generating STARK proofs here* — it's still a
    keyed-BLAKE3 commitment. The real STARK proof is generated through
    `fulfillment::produce_stark_proof` which calls
    `prove_authorization_stark` from `pyana-circuit`. So the matcher's
    `mode = Private` produces a placeholder, while the fulfillment
    pipeline produces the real artifact.
- **Integration status** — Called from `gossip.rs`
  (`IntentPool::receive_intent_checked` and `rematch_all`), from
  `app-framework`, from the `sdk` discovery layer (via `pyana_intent`
  re-exports), and from `apps/compute-exchange`.
- **Surprises** — `MatchResult::Matched { token_index: usize::MAX, .. }`
  is the sentinel for "Offer matched on absence" — there's no local
  token, just a gap. Easy to miss when indexing into `held_tokens`.
  Callers must check this case explicitly.
- **Open issues / TODOs** — None marked. The placeholder STARK proof in
  matcher (vs real STARK proof in fulfillment) is a small architectural
  inconsistency but works in practice.

---

## `solver.rs` (~1110 LOC)

- **Purpose** — Asset-only ring trade solver: find cycles A→B→C→A in the
  exchange compatibility graph where each participant offers what the
  next wants.
- **Key types/functions**
  - `ExchangeSpec { offer_asset, offer_amount, want_asset,
    want_min_amount, min_rate, max_rate }`.
  - `IntentNode` — solver-internal projection of an `Intent` plus
    exchange parameters.
  - `RingTrade { participants: Vec<IntentId>, settlements:
    Vec<Settlement>, score: f64 }`.
  - `Settlement { from: CommitmentId, to: CommitmentId, asset, amount }`.
  - `RingSolver { max_ring_size, min_edge_score, max_results }` with
    `build_graph`, `find_rings`, `validate_ring`, `solve_best`,
    `solve_greedy`.
  - `IntentGraph` — adjacency-list compatibility graph with
    `is_compatible` (returns `Some(score)` where score ∈ (0,1]).
  - `find_cycles(max_len)` — bounded DFS (a *simplified* Johnson's
    algorithm, per the doc comment), with cycle canonicalization (rotate
    so smallest index leads) and dedup.
- **Notable design choices**
  - Scoring favours close-to-exact matches: `score = want_min / offer`,
    clamped at 1.0. Overshoot is penalized so excess capital isn't wasted
    in a ring's narrowest leg.
  - `validate_ring` enforces a no-self-loop rule by commitment equality
    — same `CommitmentId` cannot appear twice in a ring.
  - `solve_greedy` picks the highest-scoring ring, removes its
    participants, repeats. Disjoint rings → multiple settlements; no
    backtracking.
- **Performance characteristics** — Quadratic graph build (O(n²) edge
  scan). Cycle enumeration is bounded by `max_ring_size` (default
  configurable; tests use 3–5). The "large pool" test runs 100 nodes /
  ring size 4 in well under 5 seconds; for realistic batch sizes
  (≤256 from trustless layer) this is fine. There is **no
  intent-zone/shard partitioning**, so a single solver sees the entire
  global pool — see §5/§6.
- **Cycle algorithm caveat** — The "bounded DFS" is *not* full Johnson's;
  it doesn't use the blocked-set optimization. It revisits nodes that
  could be safely skipped, which is observable as redundant work but
  not incorrectness. Cycle dedup via canonical rotation is correct.
- **Integration status** — Used directly by `intent::trustless`
  (`RingTrade` is the unit a solver submission carries) and by
  `intent::lowering` (`Intent::RingSettlement` carries `Vec<RingTrade>`).
  Also surfaced through `preflight/src/checks/solver.rs`.
- **Surprises**
  - The `settlements` amount uses
    `min(offer_amount, want_min).max(want_min)` — i.e. it's literally
    just `want_min` if offer >= want_min, else `min(offer, want_min)`.
    The `.max(want_min)` is a no-op when offer >= want_min; when offer
    < want_min the `min` returns offer and `.max(want_min)` *raises it
    back to want_min*. That seems to silently fix-up under-funded rings
    — but `validate_ring` rejects under-funded rings earlier
    (`InsufficientAmount`), so this branch is unreachable in practice.
    Still, it's confusing dead arithmetic.
  - `find_rings` recomputes `score` from edge weights, but
    `validate_ring` produces `score = ring.len() as f64` (the count of
    participants). Two different scoring rubrics produce two different
    "score" values for the same ring depending on which entry point you
    use.
- **Open issues** — Two scoring conventions in the same module; cleanup
  warranted. No partial-quantity ring support (every leg uses
  `want_min`; surplus on the offer side is discarded). Cross-batch
  intents are not deduplicated by `IntentId` in `build_graph` (only
  same-creator self-loops are caught in `validate_ring`).

---

## `trustless.rs` (~1580 LOC)

- **Purpose** — The 7-layer protocol that's *supposed* to remove
  executor trust: encrypted submit → consensus batch boundary →
  threshold decrypt → solver auction → STARK validity proofs →
  challenge window → atomic settlement turn.
- **Key types/functions**
  - `BatchState = Collecting | AwaitingDecrypt | Solving | Challenging
    | Settled`.
  - `EncryptedIntent { ciphertext: Vec<u8>, creator_commitment,
    submitted_at }` with `content_id()` for dedup.
  - **`DecryptionShare { validator_index: u8, share: [u8;32], batch_id:
    u64, share_mac: [u8;32] }`** — the opaque, no-crypto-here struct
    flagged by the privacy audit.
  - `SolverSubmission { solver_id, solution: Vec<RingTrade>,
    total_score, validity_proof: Vec<u8>, bond, submitted_at }`.
  - `SettlementOutput { batch_id, sealed: SealedTurn, proof_hash,
    solver_id }` — replaces the deleted ad-hoc `CompoundTurn`.
  - `IntentBatch { batch_id, encrypted_intents,
    batch_boundary_height, decrypted: Option<Vec<Intent>>, solutions,
    winning_solution, state, decrypt_shares, challenge_start_height,
    seen_intent_ids }`.
  - `ProofVerifier` trait (production verifier pluggable;
    `MockProofVerifier` ships and is the only impl in tree).
  - `TrustlessIntentEngine { current_batch, batch_interval,
    challenge_window, min_solver_bond, decrypt_threshold,
    num_validators, current_height, verifier: Box<dyn ProofVerifier>,
    next_batch_id, settled_batches }`.
  - Methods (one per protocol layer):
    `submit_encrypted`, `close_batch`, `contribute_decrypt_share`,
    `set_decrypted_intents`, `submit_solution`, `challenge`, `finalize`.
- **Notable design choices**
  - State machine is strictly linear with `WrongState` errors at every
    boundary. The challenge window logic uses `current_height` ticked
    by `advance_height`.
  - `finalize()` lowers the winning solution through the 4-layer tower
    (`lowering::Intent::RingSettlement` → `lower` → `seal_plan_uniform`)
    producing a real `SealedTurn`. The anchor is
    `CellId::from_bytes(solver_id)` (TODO inline notes that production
    deployments need to inject a configured anchor instead).
  - Bond is *posted* on each `SolverSubmission` but **never actually
    transferred or escrowed** — `min_solver_bond` is only a number-on-
    the-struct check. There is no slashing implementation despite the
    doc comment promising "bond slashing for under-performance."
- **Integration status — critical finding** — `TrustlessIntentEngine`
  has **zero production callers**. Grep `engine.submit\|engine.finalize\|
  engine.close_batch\|TrustlessIntentEngine` workspace-wide returns only
  test functions in `intent/src/trustless.rs` itself. The node
  (`node/src/api.rs`, `node/src/state.rs`) maintains a separate
  `encrypted_intent_pool: HashMap<[u8;32], pyana_intent::sse::EncryptedIntent>`
  and never invokes the trustless engine — encrypted intent storage
  exists but the batch/decrypt/auction pipeline is not wired into any
  production flow.
- **Stub quantification (the privacy-audit finding)** —
  - `DecryptionShare.share: [u8;32]` is an opaque byte array. The engine
    treats shares as **identity tokens** (count distinct
    validator_index values; transition to `Solving` when count >=
    `decrypt_threshold`). It never combines shares, never derives a
    decryption key, never verifies `share_mac`.
  - `set_decrypted_intents(intents: Vec<Intent>)` is a **cleartext
    side-channel**: after threshold "consensus", the caller hands the
    engine plaintext intents directly. There is no link between the
    `ciphertext` field of `EncryptedIntent` and the `Intent`s passed
    in. The engine has no way to verify the decrypted set actually
    corresponds to the submitted ciphertexts.
  - The mock `MockProofVerifier` does score-consistency checks
    (recompute sum, no double-spend, all intents in batch) but does
    **not** verify any cryptographic proof. It's a structural sanity
    check, not soundness.
  - A real verifier impl doesn't exist anywhere in the workspace; the
    trait is a hook.
- **The gap vs the doc-comment story** — The header documents a
  Flashbots-SUAVE-style fair-ordering protocol with hardware-trust-free
  threshold encryption replacing SGX. Concretely:
  - Threshold crypto: **stubbed.** `federation/src/threshold_decrypt.rs`
    *does* implement a real Shamir-over-GF(256) + ChaCha20-Poly1305
    scheme (with `DecryptionShare`, `ThresholdCiphertext`,
    `combine_shares`), but `intent::trustless` does not use it. The two
    crates each define their own `DecryptionShare` type with different
    fields (`batch_id` vs `ciphertext_id`) and are not bridged.
  - Encrypted intents: gossip-layer `sse::EncryptedIntent` exists and
    *is* used by the node (with X25519 + BLAKE3 XOF sealed-box, see
    `sse.rs`). But it's a separate type from `trustless::EncryptedIntent`,
    and the SSE path is single-recipient, not threshold-decryptable.
  - Validity proofs: `RingTrade` carries `validity_proof: Vec<u8>` that
    no real verifier checks. The STARK infrastructure for solver
    proofs (a circuit that says "I evaluated the matching graph
    correctly given this intent set, and the score is X") does not
    exist.
  - Challenge bond slashing: not implemented.
- **Surprises** — The state machine, the dedup, the ordering logic, and
  the lowering integration are real and exercised by 14 unit tests. The
  *cryptographic substance* is absent. A reviewer scanning the file
  would conclude "this engine works" — until noticing that the share
  field is bytes and the verifier is `Box::new(MockProofVerifier)`.
- **Open issues / TODOs**
  - Inline TODO at line 712: anchor should be configured per node, not
    derived from solver_id.
  - No production wiring.
  - Threshold scheme: completely stubbed (privacy audit's finding,
    confirmed and quantified).
  - Bond escrow / slashing: absent.
  - Proof verifier: trait + mock only.

---

## `lowering.rs` (~444 LOC)

- **Purpose** — The deterministic four-layer tower for converting a
  high-level executable intent into a runtime `pyana_turn::Turn`.
- **Key types/functions**
  - `Intent` (NB: **separate type from `crate::Intent`**, the discovery
    one). Variants: `Pay { from, to, amount }`,
    `RingSettlement { rings, anchor, solver_id, validity_proof_hash }`,
    `Custom { target, caller, method, effects }`. The header explicitly
    notes "the discovery-time `crate::Intent` type is unrelated."
  - `EffectPlan { actions: Vec<PendingAction>, validity_witness: Option }`.
  - `PendingAction { target, caller, method, effects, auth_hint }`.
  - `AuthHint = Signed | Proved { bound_action, bound_resource } |
    Bearer | Breadstuff`.
  - `ValidityWitness { solver_id, validity_proof_hash }`.
  - `SealedTurn { turn: Turn }` with `from_turn` asserting no
    `Authorization::Unchecked` in debug builds.
  - `LoweringContext { current_height, default_nonce }`.
  - `LoweringError = EmptyRing | NoRings`.
  - `lower(Intent, &LoweringContext) -> Result<EffectPlan, LoweringError>`
    — deterministic, total, order-preserving.
  - `seal_plan_uniform(plan, agent, nonce, authorization) -> SealedTurn`
    — applies a single `Authorization` to every action; debug-asserts
    non-`Unchecked`.
- **Notable design choices**
  - Ring settlement preserves leg order: rings in input order,
    settlements within each ring in original order. Confirmed by
    `ring_settlement_preserves_leg_order` test.
  - `seal_plan_uniform` embeds the validity witness (solver_id + proof
    hash) in `Turn.memo` as a human-readable string. That's a memo,
    not a binding — the witness is **not** cryptographically tied to
    the Turn beyond appearing in its serialization.
- **Integration status** — Called from `trustless::finalize`. The
  `Custom` variant is unused by any caller in tree but is documented as
  the escape hatch.
- **Surprises** — `lower_settlement_leg` constructs each
  `PendingAction` with `caller: anchor` but `target: from_cell` (the
  sender of the leg). That means the executor will see a method call
  *to* the sender cell *by* the federation anchor cell. The
  `method = "settle_ring_leg"` is a string symbol; whether the target
  cell actually exposes a method of that name is the executor's
  problem, not the lowering layer's. There is no in-tree cell that
  implements `settle_ring_leg`; **the lowered Turn would not actually
  execute on any current cell**.
- **Open issues** — No production cell implements `settle_ring_leg`.
  Either lowering should emit raw `Effect::Transfer`-only actions (it
  does include the effect, but it also dispatches a method that nothing
  handles), or a settlement cell module needs to exist somewhere.

---

## `gossip.rs` (~1631 LOC, ~800 SLOC impl)

- **Purpose** — Local pool ("mempool for capabilities") that receives
  intents from the network, performs auto-matching, enforces anti-spam
  invariants, and operates a commit-reveal protocol against
  fulfillment front-running.
- **Key types/functions**
  - `IntentPool` with rich state:
    - `intents: HashMap<[u8;32], StoredIntent>`,
    - `held_tokens`, `our_commitment`, `config`,
    - `pending_matches`, `our_intent_ids`,
    - `recent_by_creator`, `global_rate` (rate limiting),
    - `pending_commitments` (commit-reveal),
    - `known_note_root: BabyBear` (stake-proof anchor),
    - `used_stake_nullifiers: HashSet<[u8;32]>` (epoch-scoped),
    - `current_block_height`, `fulfilled_intents`.
  - `IntentPoolConfig { max_intents, gc_interval_secs, auto_match,
    minimum_stake_value }`.
  - `AutoFulfillPolicy = Never | ForPatterns(Vec<String>) | Always`.
  - `ReceiveError` — 9 variants covering rate limit, stake, validation,
    duplicate, expired, already-fulfilled, etc.
  - `FulfillmentCommitment { intent_id, satisfier_commitment,
    timestamp }`, `FulfillmentReveal { commitment_hash, fulfillment,
    nonce }`, `CommitRevealError`.
  - Methods: `broadcast_intent`, `receive_intent`,
    `receive_intent_checked`, `receive_local_intent`, `mark_fulfilled`,
    `gc`, `active_intents`, `rematch_all`, `commit_to_fulfill`,
    `reveal_fulfillment`.
  - Constants: `MAX_INTENTS_PER_CREATOR_PER_MINUTE=10`,
    `MAX_GLOBAL_INTENTS_PER_WINDOW=500`,
    `RATE_LIMIT_WINDOW_SECS=60`,
    `MAX_COMMITMENT_AGE_SECS=300`,
    `COMMIT_REVEAL_WINDOW_SECS=5`,
    `FULFILLED_RETENTION_BLOCKS=10_000`.
- **Notable design choices**
  - Strict stake-required mode for gossip-received intents
    (`require_stake: true`); local intents (own-page) bypass.
  - Epoch-scoped nullifier bookkeeping: each stake commitment gets K=5
    uses per `EPOCH_DURATION_BLOCKS=1000` blocks; nullifiers are
    computed from `Poseidon2(commitment, epoch, counter)` and stored.
    `update_block_height` clears the nullifier set when epoch advances.
  - Pool size enforcement evicts by **arrival time** (issue #9 cited
    inline), not by expiry, to avoid the attack of long-expiry intents
    pushing real ones out.
  - Commit-reveal hashes commitment as
    `BLAKE3_derive_key("pyana-fulfillment-commit-v1", intent_id ||
    fulfiller || actions || resource || nonce)`. The reveal must wait
    `COMMIT_REVEAL_WINDOW_SECS = 5s` before being accepted.
  - `fulfilled_intents` is a bounded set with GC (max
    `FULFILLED_RETENTION_BLOCKS` block age) to prevent unbounded
    memory growth.
- **Integration status** — The pool's API is the surface that
  `sdk::wallet`, the demo agent, and the node's WS layer interact with.
  `node/src/state.rs` keeps a `intent_pool: HashMap<[u8;32], Intent>`
  separately (a "node-side" mirror) — i.e. the node does *not* use
  `IntentPool` directly; it manages its own dedup. So `IntentPool` is
  the *client-side* abstraction, used by wallets / SDK consumers.
- **Surprises**
  - **`ForPatterns` glob matches PATTERN against PATTERN** — the inline
    code is:
    ```
    if let Some(ref resource_pattern) = intent.matcher.resource_pattern {
        patterns.iter().any(|p| {
            globset::Glob::new(p)
                .map(|g| g.compile_matcher().is_match(resource_pattern))
                .unwrap_or(false)
        })
    }
    ```
    That tests "does my whitelisted-pattern glob match THIS INTENT'S
    PATTERN STRING" — not "does it match the resource the intent
    targets." For an intent with `resource_pattern = "documents/*"`
    and policy `ForPatterns(vec!["documents/*"])`, the glob
    `documents/*` does not match the literal string `"documents/*"`
    (because `*` isn't a literal). This auto-fulfill policy is
    probably buggy as written.
  - `receive_intent_checked` always returns `Some(matched)` when a
    match is found, **regardless of whether `should_auto_fulfill`
    accepts**. The non-auto path stores the match in
    `pending_matches` AND returns the same match. Callers cannot
    distinguish "auto-fulfilled" from "pending user approval" by the
    return alone. That's at minimum a confusing API; possibly a bug
    if callers were expected to act on the returned Match
    immediately.
  - `mark_fulfilled` is called *only* from `reveal_fulfillment`. If the
    fulfillment is delivered out-of-band (no commit-reveal), nothing
    marks the intent. The replay-protection invariant therefore
    depends on the commit-reveal path being the *only* fulfillment
    path — which it isn't (see `fulfillment.rs` direct calls and
    `commit_reveal_fulfillment.rs`).
- **Open issues**
  - `AutoFulfillPolicy::ForPatterns` is likely incorrect; should match
    against the intent's *target resource*, not against its
    `resource_pattern` string.
  - `mark_fulfilled` is only triggered from one of the multiple
    fulfillment paths.
  - `IntentPool` and `node::state::intent_pool` are two parallel
    data structures; the node never uses the hardened pool.

---

## `fulfillment.rs` (~2716 LOC)

- **Purpose** — Producing and verifying capability fulfillments.
  Trusted mode → real attenuated macaroon. Selective/Private mode →
  real FRI STARK proof from `pyana_circuit::multi_step_air`. Plus
  cross-party predicate-proof attachment, automatic payment turns,
  and an end-to-end "execute the fulfillment flow" entry point.
- **Key types/functions**
  - `Fulfillment { intent_id, fulfiller, mode, token_data, proof,
    granted_actions, granted_resource, expiry }`.
  - `FulfillOptions { mode, max_expiry, restrict_actions,
    restrict_resource, root_key, stark_witness }`.
  - `fulfill(intent, &matched, source_token, our_commitment, options)
    -> Result<Fulfillment, ...>`.
  - `verify_fulfillment` / `verify_fulfillment_with_key` — checks
    proof / token, then enforces granted-actions ⊆ intent-actions
    (privilege-escalation guard for Private/Selective), and
    granted-resource ⊇ intent-resource-pattern.
  - `FulfillmentWithPredicates { base, predicate_proofs, state_root,
    state_root_block }` + verifier including freshness window check.
  - `compute_intent_request_hash(intent)` — binds STARK proof to a
    specific intent's `(action, resource_pattern)` via
    `compute_action_binding_narrow`. Verifier rejects on mismatch
    (replay defense).
  - `produce_attenuated_token` — builds a `MacaroonToken` with HMAC
    caveats, serialises, returns bytes.
  - `produce_stark_proof` — calls real
    `prove_authorization_stark(witness)`.
  - `create_fulfillment_turn` — builds a `ConditionalTurn` that
    transfers `payment_amount` from the intent creator to the
    fulfiller, conditioned on a deterministic hash preimage.
- **Notable design choices**
  - **Real cryptography**: macaroon HMAC chain verification, real
    STARK verification, real predicate-proof verification. This is in
    stark contrast to `trustless.rs`. The Trusted mode fully verifies;
    Private/Selective mode fully verifies; predicate freshness window
    is enforced against `current_block`.
  - Privilege-escalation guard on granted_actions only fires for
    Private/Selective — the rationale (inline): Trusted mode hands
    over a real macaroon whose attenuation is HMAC-verified anyway.
  - The intent→request_hash binding is essential and audited; without
    it any prior STARK proof could be replayed against a different
    intent.
- **Integration status** — `node/src/api.rs` exposes a REST endpoint
  (`execute_fulfillment_flow`) that uses `FulfillmentWithPredicates`
  and `verify_fulfillment_with_predicates_and_key`. `sdk::wallet`
  also calls into `fulfillment` (mainly for the Trusted path). The
  WASM crate re-exports key entry points for browser-side flows.
- **Surprises**
  - `create_fulfillment_turn` builds an `Action` with
    `authorization: Authorization::Unchecked`. The `ConditionalTurn`
    wrapper supplies its own gating, but the bare `Action` would
    *not* pass `SealedTurn::from_turn`'s `debug_assert`. So the
    payment turn path doesn't go through the lowering tower — it
    creates a Turn-shaped object that the executor must trust the
    conditional-resolver to gate.
  - The "automatic payment" assumes the intent's `min_budget` is the
    payment amount. There's no separate fee-quote step in the protocol
    — fulfillers either accept the advertised budget or they don't
    fulfill.
- **Open issues** — `Unchecked` authorization in
  `create_fulfillment_turn` is a code-smell that depends on the
  conditional resolver being correct. The intent's `min_budget` →
  payment-amount tying conflates "minimum I'm willing to pay" with
  "exact payment" — economic semantics are underspecified.

---

## `partial_fill.rs` (~882 LOC)

- **Purpose** — AMM/DEX-style partial fills: fill some-but-not-all of
  an intent's quantity, with residual chains.
- **Key types/functions**
  - `PartialFillResult { filled_amount, remaining_amount,
    residual_intent: Option<Intent>, fulfillment }`.
  - `PartialFillError` — BelowMinimum, FillOrKillRejected,
    InvalidConstraints, MaxResidualDepth, RequiresFreshStake, etc.
  - `check_fill_amount(constraints, available) -> Result<u64, ...>`.
  - `create_residual_intent(original, filled_amount) -> Option<Intent>`.
  - `execute_partial_fill(intent, matched, source_token, our_commitment,
    available_amount, &options)` — top-level.
  - `CumulativeFillTracker { original_intent_id, total_filled,
    max_fill_amount, fill_chain }`.
- **Notable design choices**
  - **Geometric degradation of min_fill_amount**: each residual
    doubles the minimum. Inline rationale: "makes repeated tiny fills
    exponentially more expensive."
  - `MAX_RESIDUAL_DEPTH=10` caps the chain length.
  - After `FRESH_STAKE_GENERATION=3`, the residual drops the inherited
    stake proof — the next filler must attach a fresh stake. Prevents
    one stake from underwriting an unbounded residual chain.
  - Defence-in-depth: `check_fill_amount` *and* `execute_partial_fill`
    both validate `min > 0` and `min <= max`.
- **Integration status** — Used by `apps/compute-exchange/orderbook.rs`
  (`check_fill_amount` is called for order matching) and by
  preflight/intent checks.
- **Surprises** — `Intent::id` changes between original and residual
  (because `fill_constraints` is part of the content hash). So the
  `fill_chain` is a chain of distinct IntentIds — not a single
  long-lived intent. The CumulativeFillTracker is the only thing
  that knows the chain belongs together.
- **Open issues** — None obvious. This module is one of the cleanest.

---

## `commit_reveal_fulfillment.rs` (~893 LOC)

- **Purpose** — Two-phase commit-reveal to prevent fulfillment
  front-running, with abandon-penalty bookkeeping.
- **Key types/functions**
  - `FulfillmentCommitment { intent_id, commitment_hash, committed_at,
    epoch }` — note the `epoch` field, separate from `gossip.rs`'s
    `FulfillmentCommitment` (different module, same name).
  - `FulfillmentResult { fulfillment, commitment, fulfilled_epoch }`.
  - `FulfillmentRegistry` — tracks all commitments per intent,
    enforces ordering, manages abandon counts.
  - `CommitRevealFulfiller` — wraps `fulfill()` with the protocol.
  - `MAX_ABANDONS_PER_EPOCH = 3`, `COMMITMENT_EXPIRY_SECS = 60`.
- **Notable design choices**
  - **Priority by timestamp**: the earliest non-expired commitment for
    an intent wins; later committers get `PriorityConflict`. This
    closes the gossip front-running gap.
  - **Abandon penalty**: if a committer never reveals (commitment
    expires), their commitment-hash is logged. After 3 abandons in
    an epoch, that committer is blocked from new commits this epoch.
  - **Epoch-binding of commitment hash**: hash includes the epoch
    *at commit time*, so reveals work across epoch boundaries without
    silently failing.
- **Integration status** — `intent_lifecycle` demo agent example uses
  this. The node-side production wiring is not present;
  `gossip::IntentPool::commit_to_fulfill` is its own (simpler,
  lower-level) commit-reveal path.
- **Surprises**
  - Two parallel commit-reveal implementations: `gossip::IntentPool`
    has one (timestamp + nonce in the commitment), this module has
    another (epoch + secret + abandon-count). They are *not* layered;
    they're alternatives. A user could call either; neither knows
    about the other.
  - The `FulfillmentCommitment` type defined here shadows the one in
    `gossip.rs` (same name, different fields, different module).
- **Open issues** — Duplicate / overlapping commit-reveal API is
  confusing. A consolidation pass would help.

---

## `delay_pool.rs` (~531 LOC)

- **Purpose** — Timing decorrelation: instead of releasing fulfillment
  reveals immediately, batch them at fixed intervals and pad with
  dummies.
- **Key types/functions**
  - `DelayPoolConfig { batch_interval_secs, min_batch_size,
    max_delay_secs, dummy_rate_per_interval }`.
  - `PoolItem = Real(FulfillmentResult) | Dummy(DummyReveal)`.
  - `DummyReveal { commitment_hash, intent_id, generated_at }` — random
    bytes, structurally identical to a real reveal until commitment
    lookup or proof verification.
  - `DelayPool::tick(now)` — injects configured number of dummies,
    releases a batch if interval elapsed and ≥`min_batch_size`, or if
    any item exceeded `max_delay_secs`.
- **Notable design choices**
  - Defaults: 30s interval, min batch 3, 120s failsafe timeout, 1
    dummy per interval.
  - Failsafe ensures one stuck real reveal eventually flushes even if
    not enough other items arrive.
- **Integration status** — `node/src/state.rs` constructs
  `pyana_intent::delay_pool::DelayPool::new(DelayPoolConfig::default())`
  per session — so the node *does* hold a delay pool. Whether it's
  actually `tick`ed and the released batch broadcast is something the
  node-side audit would have to confirm; the intent crate only
  provides the type.
- **Surprises** — `DummyReveal::commitment_hash` is just random bytes.
  At the gossip layer it's indistinguishable from a real commitment
  reference, but it carries no MAC and no proof. The verifier
  silently discards on commitment-not-found. This is by design (the
  comments are explicit) — the privacy property is "observer sees N
  reveals leave the node per interval and can't tell which are real."
- **Open issues** — No throttling on cumulative dummy bandwidth across
  epochs.

---

## `sse.rs` (~905 LOC)

- **Purpose** — Searchable Symmetric Encryption: encrypted intent
  headers with searchable tokens, so fulfillers can do a coarse
  capability match without seeing the cleartext body.
- **Key types/functions**
  - `generate_search_token(keyword, epoch) -> [u8;32]` —
    BLAKE3-derived from keyword + epoch.
  - `tokens_for_matchspec(&MatchSpec, epoch) -> Vec<[u8;32]>`.
  - `extract_sse_keywords(&MatchSpec) -> Vec<String>`
    (`action:<name>`, `resource:<pat>`, `service:<svc>`, etc.).
  - `capability_matches_tokens(capability_keywords, tokens, epoch)
    -> bool` — coarse filter.
  - `EncryptedIntent` (the one referenced by `node/src/state.rs`):
    `ciphertext + sse_tokens + commitment + expiry + ephemeral_pk`.
  - X25519 sealed-box: ephemeral keypair, shared-secret via DH,
    BLAKE3-XOF keystream XOR plaintext.
- **Notable design choices**
  - "Keyword-as-secret": anyone who knows the keyword can produce the
    token. Weaker than true SSE (no shared secret distribution
    required); explicitly acknowledged as such in the header.
  - Epoch rotation: same as stake nullifiers — cross-epoch token
    linkability is broken.
- **Integration status** — `node/src/api.rs` accepts
  `Json<EncryptedIntent>` POSTs and stores them in
  `encrypted_intent_pool`. The node never invokes the SSE matcher
  (no `capability_matches_tokens` callsites outside this module and
  its tests).
- **Surprises** — The SSE matcher is fully implemented but unused.
  Nodes accept and store encrypted intents but never serve them to
  fulfillers via SSE-token query. The encrypted intent pool is, at
  present, a write-only sink.
- **Open issues** — The node has no SSE query endpoint or
  fulfiller-side SSE polling. The crypto exists; the wire protocol
  doesn't.

---

## `pir.rs` (~1767 LOC)

- **Purpose** — Private Information Retrieval over the intent pool's
  inverted index, so a wallet can ask "show me intents tagged
  `action:read`" without revealing the tag.
- **Key types/functions**
  - `PirMode = TwoServer | DownloadAll { max_db_size } |
    SingleServerPadded`.
  - `PirQuery { query_vector: Vec<BabyBear> }`,
    `PirResponse { response: Vec<BabyBear> }`.
  - `BatchPirQuery` / `BatchPirResponse`.
  - `SingleServerQuery` / `SingleServerResponse` (with blinding).
  - `EncryptedDatabase` for download-all.
  - `IntentIndex { tags: Vec<String>, entries: Vec<Vec<BabyBear>> }`
    — built from a pool or directly from an intent slice.
  - `MAX_INTENTS_PER_TAG=64`, `ELEMENTS_PER_ID=32`,
    `ROW_WIDTH=MAX*ELEMENTS_PER_ID=2048`.
  - `compute_pir_response`, `combine_pir_responses`, `decode_pir_row`.
- **Notable design choices**
  - 2-server additive IT-PIR over BabyBear (since GF(2) XOR doesn't
    play well with the field). Information-theoretically secure
    against either single server.
  - Power-of-2 padding hides database size.
  - Each intent ID encoded byte-per-field-element (lossless).
- **Integration status** — `node/src/api.rs` rebuilds an
  `IntentIndex::build_from_intents(&intents)`, caches it as
  `pir_index_cache`, and exposes a `compute_pir_response` endpoint.
  So PIR is partially wired into the production node (the
  two-server variant; the other modes aren't surfaced).
- **Surprises**
  - It's a real implementation, not a stub — `build`,
    `compute_pir_response`, `combine_pir_responses` all do the
    matrix-vector arithmetic.
  - 2-server requires non-colluding servers. The node API doesn't
    enforce or document a server-pairing protocol; the client is
    trusted to query two independent nodes.
- **Open issues** — Server-pairing protocol unspecified. The other
  PIR modes are typed but not surfaced through any API.

---

## `generalized.rs` (~1200 LOC)

- **Purpose** — Heterogeneous-asset generalized solver: ring trades
  where each leg can be assets, capability grants, service
  invocations, storage, or namespace entries.
- **Key types/functions**
  - `ExchangeItem = Asset { id, amount } | Capability { actions,
    resource, duration_epochs } | Service { endpoint, invocations }
    | Storage { queue_id, bytes, duration_epochs } | Name { namespace,
    entry }`.
  - `GeneralizedExchange { offering: Vec<ExchangeItem>, wanting:
    Vec<ExchangeItem> }`.
  - `GeneralizedIntentNode { intent_id, exchange, creator, expiry,
    zone: Option<String> }` — note the `zone` field for DFA routing.
  - `item_satisfies(offered, wanted) -> bool` (per-type rules).
  - `can_satisfy(&[offer], &[want]) -> Option<f64>` — greedy distinct
    matching, returns `satisfied_count / wanted.len()`.
  - `GeneralizedIntentGraph { nodes, edges }`.
  - `GeneralizedSolver { max_ring_size, min_edge_score, max_results,
    require_full_satisfaction }` with `strict(max_ring_size)`
    convenience constructor.
- **Notable design choices**
  - Subjective valuation: no global pricing. A participant just
    declares "I offer X+Y, I want A+B." Cross-type equivalence is
    expressed by listing the items, not inferred by the solver.
  - DFA-zone hint on the node is present (`zone`) but the solver
    itself doesn't filter by zone — the DFA routing layer is supposed
    to shard the input. **See §5/§6.**
- **Integration status** — Used by `app-framework/src/ring_trade.rs`
  and exposed through preflight. The trustless engine accepts only
  `RingTrade` (asset-only) from `solver.rs`, not
  `GeneralizedRingTrade`. So generalized rings cannot today flow
  through the trustless settlement pipeline.
- **Surprises** — The solver supports the heterogeneous case but the
  trustless engine doesn't accept its output. There's a type-level
  gap between `solver::RingTrade` (what `SolverSubmission.solution`
  holds) and `generalized::GeneralizedRingTrade`.
- **Open issues** — Generalized output isn't lowerable through
  trustless. Either lift trustless to accept either ring type or
  unify behind a common settlement schema.

---

# Synthesis

## §1. The Intent system, high-level

An **intent** in pyana is a content-addressed declaration of a
capability *shape* — what someone needs, offers, or queries — broadcast
to a gossip network, matched locally by wallets, and (if matched)
fulfilled through a verifiable artifact (macaroon, STARK proof, or
both). Two distinct `Intent` types exist in the crate:

1. `crate::Intent` (in `lib.rs`) — the **discovery-time** intent. A
   `MatchSpec` + creator commitment + expiry + optional stake + optional
   fill constraints. Content-addressed via canonical postcard + BLAKE3.
2. `crate::lowering::Intent` — the **executable** intent. Variants
   `Pay`, `RingSettlement`, `Custom`. This is the input to the 4-layer
   lowering tower. Header comment explicitly notes these are "unrelated."

End-to-end flow:

```
authoring               matching                       lowering           execution
─────────               ────────                       ────────           ─────────
wallet builds                                                             executor
  MatchSpec ──postcard──> Intent (discovery) ──gossip──>
                                                ├─ IntentPool.receive_intent_checked
                                                │   (validation, stake, rate, nullifier)
                                                ├─ matcher::match_intent (local)
                                                └─ commit_reveal_fulfillment
                                                    or fulfillment::fulfill
                                                       │
                                                       │ Trusted: attenuated macaroon
                                                       │ Private:  STARK proof
                                                       ▼
                                                   verify_fulfillment
                                                       │
                                                       ▼ payment turn
                                                   create_fulfillment_turn → ConditionalTurn
                                                       ▼
                                                   TurnExecutor runs

OR for batched fair matching (intended but unwired):
  TrustlessIntentEngine: submit_encrypted → close_batch → threshold decrypt
                       → submit_solution (SolverSubmission with RingTrades)
                       → challenge window → finalize → lowering::Intent::RingSettlement
                       → lower → seal_plan_uniform → SealedTurn → Turn
```

The relationship between intents and Effects/Turns is one-way:
**intents lower to effects bundled in turns**. The lowering layer is
the seam. An intent is *declarative* ("transfer 100 from A to B");
the Turn is *imperative* (an `Action` with `Effect::Transfer { from,
to, amount }`, an authorization, preconditions, and a target cell).

## §2. Solver

The asset-only ring solver works as follows:

1. **Graph build** (`RingSolver::build_graph`, `solver.rs:138`):
   O(n²) scan of all intent pairs. An edge `i→j` exists if intent `i`'s
   `offer_asset == j`'s `want_asset` and `i.offer_amount >=
   j.want_min_amount`. Edge score = `want_min / offer` clamped to 1.0
   (encourages exact matches).

2. **Cycle enumeration** (`IntentGraph::find_cycles`, `solver.rs:462`):
   bounded DFS from each starting node, with `max_len` cap. Each
   discovered cycle is canonicalized (rotate so smallest index leads)
   and deduplicated.

3. **Ring construction**: each cycle becomes a `RingTrade` with
   participant intent IDs, per-leg settlements (asset = offerer's
   asset, amount = `min(offer, want_min)`), and an aggregate score.

4. **Validation** (`RingSolver::validate_ring`, `solver.rs:230`):
   - No self-loop (same creator twice).
   - All intents valid at time `now`.
   - Asset types match cyclically (`offerer.offer_asset ==
     receiver.want_asset`).
   - Quantity sufficient.
   - Rate bounds (`min_rate`, `max_rate`) respected when specified.

5. **Solve strategies**:
   - `solve_best`: return the highest-scoring ring.
   - `solve_greedy`: repeatedly take the best ring, mark participants
     used, re-solve until no more rings exist or `max_results` reached.

Constraint shape: per-leg asset-equality and amount-sufficiency.
Matching algorithm: graph cycle search bounded to a small constant
(3–5 typical). Performance: O(n²) per graph build, bounded DFS
cycle search; test at 100 nodes / max_ring_size=4 / max_results=10
runs in well under 5 seconds.

The cleanest API entry point is `solve_best(intents: &[IntentNode],
now: u64) -> Option<RingTrade>` (cited from `solver.rs:354`). It
filters expired intents, builds the graph, runs `find_rings`,
returns the top.

The matcher (capability-side, `matcher.rs`) is a separate concern:
it doesn't do cycle detection at all. It evaluates whether a single
held capability satisfies an intent's MatchSpec. The "matcher"
(structural / boolean / per-intent) and the "solver" (graph /
multi-party) are orthogonal subsystems, both lowered through the
same lowering layer when settlement is required.

## §3. Trustless intent engine

The privacy audit's finding is **confirmed and quantified**:

The `trustless.rs` module implements a 7-layer state machine and the
*protocol structure* is real — `submit_encrypted` → `close_batch`
→ `contribute_decrypt_share` (counts shares) → `set_decrypted_intents`
(cleartext side-channel) → `submit_solution` (mock-verified) →
`challenge` (score comparison) → `finalize` (lowers through real
4-layer tower, produces real `SealedTurn`).

But the trust-critical primitives are stubbed:

| Layer | Documented | Actually implemented |
|---|---|---|
| 1. Submit | threshold-encrypted ciphertext | opaque `Vec<u8>`; no key handling |
| 2. Batch  | consensus-determined | `current_height` + monotone counter (in-process) |
| 3. Decrypt | t-of-n threshold ceremony with verification | count distinct `validator_index` values; `share: [u8;32]` unused; `share_mac: [u8;32]` unverified |
| 4. Solve  | open solver competition | accept any `SolverSubmission` |
| 5. Prove  | STARK validity proof | `MockProofVerifier` does structural checks only; trait has no real impl |
| 6. Select | challenge window + bond slashing | challenge window real; **bond slashing absent** |
| 7. Settle | atomic compound turn | real `SealedTurn` via lowering tower |

**What `DecryptionShare` is**: a 32-byte placeholder with
`validator_index`, `batch_id`, and an unverified `share_mac`. The
engine's only use of it is `contribute_decrypt_share`, which
increments a counter and transitions state when
`decrypt_shares.len() >= decrypt_threshold`. The bytes are never
combined, hashed, or fed into any decryption routine.

**Who would hold the threshold**: the validator set of a
federation (intended). `num_validators` is engine config;
`validator_index` is `1..=num_validators`. No DKG, no key
distribution, no validator-set evolution.

**Committee design**: not present in the trustless module. The
federation crate (`federation/src/threshold_decrypt.rs`) has its
own working threshold scheme (Shamir over GF(256) + ChaCha20-Poly1305,
with real `combine_shares`), but it operates on **turn ciphertexts**,
not intent ciphertexts, and the two crates are **not bridged**.
Each defines its own `DecryptionShare` struct with different fields
(`batch_id` vs `ciphertext_id`) and there's no adapter.

**Intended trustless flow** (per the header docstring):
1. Submitter encrypts `Intent` to the federation's threshold public
   key (derived from validator shares via DKG; the public key is
   stable per epoch).
2. Submitter publishes `EncryptedIntent` to gossip.
3. Federation runs blocklace consensus to determine batch boundaries.
4. After boundary, each validator broadcasts a decryption share
   `DecryptionShare` that's a *partial decryption* (not a key share)
   bound to the ciphertext's batch_id.
5. Anyone with t of n shares can reconstruct the plaintext intents
   for that batch.
6. Solvers (anyone, not just validators) build solutions, post
   `SolverSubmission { solution, total_score, validity_proof, bond }`
   to gossip. The validity proof is a STARK certificate that the
   solution is correct given the decrypted intent set.
7. Best-scoring proven solution wins. Anyone with a higher-scoring
   solution can challenge during the window; successful challenges
   slash the loser's bond.
8. After the window, the winning solver's `RingSettlement` is
   lowered to a `SealedTurn` and committed.

**Actually implemented**: the state machine, the structural checks,
the lowering integration. The cryptography and the economic
mechanisms are missing. There are also **zero production callers** —
`TrustlessIntentEngine` is invoked only from its own tests. The node
maintains an `encrypted_intent_pool` separately and never invokes the
engine.

## §4. Lowering

The four-layer tower (per `lowering.rs` header and confirmed in
`trustless::finalize`):

1. **`lowering::Intent`** — variants `Pay`, `RingSettlement`,
   `Custom`. This is the "what the user / solver wants" layer.
2. **`EffectPlan`** — flat `Vec<PendingAction>`, each carrying typed
   `Effect`s and an `AuthHint`. No authorization attached. Optional
   `ValidityWitness` carrying solver_id + proof_hash for
   ring-settlement provenance.
3. **`SealedTurn`** — every `PendingAction` becomes an
   `Action` with a real `Authorization` (never `Unchecked`). The
   wrapping `SealedTurn { turn }` newtype enforces the invariant in
   debug builds.
4. **`pyana_turn::Turn`** — the runtime executable consumed by
   `TurnExecutor`.

For a `RingSettlement`:
- `lower` iterates rings in input order, settlements within each ring
  in original order, producing one `PendingAction` per leg with
  `target = leg.from`, `caller = anchor`, `method = "settle_ring_leg"`,
  `effects = [Effect::Transfer { from, to, amount }]`,
  `auth_hint = Signed`.
- The `ValidityWitness` (solver_id, proof_hash) is preserved at the
  `EffectPlan` level.
- `seal_plan_uniform(plan, agent: CellId, nonce: u64, auth:
  Authorization)` applies `auth` to every action and packages them
  in a single `TurnBuilder`. The validity witness is embedded as a
  human-readable memo on the Turn (truncated solver_id + proof_hash).

In `trustless::finalize`:
- `anchor = CellId::from_bytes(winner.solver_id)`.
- `Intent::RingSettlement { rings: winner.solution.clone(), anchor,
  solver_id, validity_proof_hash: blake3(winner.validity_proof) }`.
- `lower(ring_intent, &LoweringContext::default())` → `EffectPlan`.
- `seal_plan_uniform(plan, anchor, batch_id,
  Authorization::Signature(solver_id, proof_hash))` →
  `SealedTurn`.
- Output: `SettlementOutput { batch_id, sealed, proof_hash,
  solver_id }`.

Concrete gap: the lowered `method = "settle_ring_leg"` is a string
symbol that no cell in the workspace implements. The Turn would
deserialize and dispatch but find no handler. The lowering layer
produces a *structurally* valid Turn that isn't *semantically*
executable today.

## §5. Composition with the rest of pyana

- **Intent ↔ Turn**: the seam is `lowering.rs`. Intents and turns are
  separate vocabularies; lowering is the translator. There is *no*
  direct dependency from a Turn back into an Intent — turns don't know
  their originating intent (beyond the `validity_witness` memo).

- **Intent ↔ Federation**: the trustless engine **intends** to be
  embedded in federation nodes (header: "Designed to be embedded in a
  federation node"). Today, federations don't carry intent state.
  The federation crate has its own threshold-decryption primitives
  for turns (`federation/src/threshold_decrypt.rs`), but those are
  not used by `intent::trustless`. The intent engine is currently
  federation-agnostic.

- **Intent ↔ CapTP**: intents do not flow over CapTP. Discovery uses
  gossip (Plumtree lazy-push, per the header); fulfillment is
  delivered directly (the header says "sent DIRECTLY to the intent
  creator"); the node exposes REST endpoints for intent
  post/match/PIR; encrypted intents have an X25519 sealed-box wire
  format. CapTP is for promise-pipelined cell-to-cell calls; it's
  orthogonal to intent matching.

- **Intent ↔ Slot caveats**: there's no direct overlap today.
  Intents have `predicate_requirements` (for STARK predicate-proof
  attachment); cells/turns have `preconditions`. These are
  parallel mechanisms that haven't been unified. The
  `PredicateProof` machinery (`pyana_circuit::verify_predicate`)
  is shared, but the intent layer attaches them at fulfillment time
  while turns can carry them as preconditions. A future
  consolidation could plausibly express intent predicates as a
  superset of slot caveats, but isn't done.

- **Intent ↔ DFA**: per the DFA design (referenced in the prompt),
  gossip topic filtering should be DFA-mediated, with structural
  matching unchanged. **Today it isn't.** `dfa/src/filter.rs` only
  mentions intent gossip in comments (`"intent::gossip uses a
  32-byte topic id"`) — there's no `IntentTopic`-keyed filter, no
  zone routing. The `generalized.rs` solver has a `zone:
  Option<String>` on intent nodes, suggesting *future* DFA-keyed
  sharding, but the gossip layer broadcasts all intents flat to all
  subscribers. PIR over the inverted index is the closest existing
  thing to topic-aware querying, and it goes the other direction
  (server holds everything, client privately picks a row).

## §6. Surfaced bugs / gaps

In rough severity order:

1. **`TrustlessIntentEngine` is entirely test-only**. No production
   wiring. The node maintains its own `encrypted_intent_pool`
   without invoking the engine. The privacy guarantees the engine
   promises are not delivered by any deployed path. **High priority
   to wire up or to acknowledge as unimplemented in user-facing
   docs.**

2. **Threshold decryption is stubbed** (privacy audit, confirmed).
   `DecryptionShare.share: [u8;32]` carries no cryptographic
   meaning. `set_decrypted_intents` is a cleartext side-channel.
   The two parallel `DecryptionShare` types (intent vs federation)
   should be bridged or unified.

3. **Lowered ring-settlement actions invoke `method =
   "settle_ring_leg"` which no cell implements**. The Turn is
   structurally valid but semantically dead. Either implement the
   method on a settlement cell, change lowering to emit
   bare-effect actions on the participants' cells, or document
   that ring settlement requires a dedicated settlement cell to be
   deployed.

4. **`AutoFulfillPolicy::ForPatterns` is probably buggy** (see
   `gossip.rs` Surprises). It globs whitelisted patterns against
   the *intent's pattern string*, not against the *target
   resource*. Likely never matches anything in practice.

5. **`mark_fulfilled` only fires from `gossip::reveal_fulfillment`**,
   not from the direct `fulfillment::fulfill` path or from
   `commit_reveal_fulfillment`. Replay-protection invariants depend
   on the commit-reveal path being the only fulfillment path —
   which it isn't.

6. **Two parallel commit-reveal implementations** (`gossip.rs`
   and `commit_reveal_fulfillment.rs`) with the same struct name
   `FulfillmentCommitment` but different field sets. Risk of
   confusion; opportunity for consolidation.

7. **Solver scoring is inconsistent** between `find_rings` (sum of
   edge weights) and `validate_ring` (ring length). Both produce
   `RingTrade.score` but it means different things.

8. **`solver.rs:328` has unreachable arithmetic**: `.min(want_min).
   max(want_min)` is `want_min` when `offer >= want_min`, and
   silently raises an under-funded leg back to `want_min` otherwise
   — but `validate_ring` rejects under-funded rings earlier.
   Dead but confusing.

9. **`fulfillment::create_fulfillment_turn` builds Actions with
   `Authorization::Unchecked`**. The `ConditionalTurn` wrapper
   provides gating, but the resulting Turn wouldn't pass
   `SealedTurn::from_turn`. Bypasses the seal invariant.

10. **`generalized::GeneralizedRingTrade` can't flow through the
    trustless engine** (only `solver::RingTrade` does). Either
    promote the trustless engine to accept either, or unify.

11. **`AssetRegistry` is dead code** — never consulted by the solver
    or anything else.

12. **SSE matcher is implemented but unused** — node accepts encrypted
    intents but never serves SSE queries to fulfillers. The
    `encrypted_intent_pool` is write-only.

13. **`predicate_requirements` is unvalidated** in `validate_intent`.
    No size cap, no per-string length cap.

14. **Bond is not escrowed** in `SolverSubmission`. `min_solver_bond`
    is a number-on-the-struct check only; no slashing.

15. **No DFA-routed topic filtering for intent gossip** despite the
    design pointing that direction. Flat broadcast today.

16. **`IntentPool` (the hardened, rate-limited, nullifier-tracking
    pool) is the client-side abstraction; the node maintains a
    separate, unhardened mirror** — `node::state::intent_pool:
    HashMap<[u8;32], Intent>`. The node-side path skips all the
    hardening done in `IntentPool`.

## §7. compute-exchange use case

`STARBRIDGE-APPS-PLAN.md` (§3.7) frames compute-exchange as the
integration test for temporal-predicate proofs + intent matching,
with this flow:

1. Buyer posts an encrypted intent (`MatchSpec`) describing job
   requirements (GPU class, SLA, deadline, budget).
2. The intent is encrypted to candidate sellers' stealth addresses.
3. Sellers' wallets do local SSE/PIR-based filtering, then run
   `matcher::match_intent` with `predicate_requirements`
   (temporal-predicate proofs for things like uptime over a window).
4. Buyer selects from previewed candidates.
5. Delivery uses the existing STARK delivery proof
   (`apps/compute-exchange/src/delivery_verification.rs`, 780 LOC).

What the intent crate **already provides** for this:
- `MatchSpec` with `predicate_requirements: Vec<PredicateRequirement>`.
- `FulfillmentWithPredicates` with attached `PredicateProof`s.
- `verify_fulfillment_with_predicates_and_key` enforcing
  threshold, type, freshness window.
- `FillConstraints` (already wired into
  `apps/compute-exchange/src/orderbook.rs::check_fill_amount`).
- `CommitRevealFulfiller` for front-running protection.
- `sse::EncryptedIntent` for stealth-address encrypted posting.

What the intent crate **doesn't yet provide**:
- A real flow that ties `TrustlessIntentEngine` to compute-exchange's
  auction. Today the auction is built ad-hoc on top of `partial_fill`,
  not on top of the trustless engine.
- DFA-routed gossip topics so compute-exchange intents don't broadcast
  to every wallet.
- An SSE-query endpoint on the node so encrypted intents are
  *discoverable*, not just stored.
- An integration with the temporal-predicate AIR (the AIR exists in
  `circuit/`; intent's `verify_predicate_requirement` would need a
  temporal variant).

To make compute-exchange work *in the full trustless mode*, the intent
crate would need: (a) real threshold encryption keyed to a
federation epoch; (b) the SSE→PIR pipeline served by nodes; (c) a
temporal `PredicateType`; (d) the trustless engine wired into the
node's intent flow; (e) DFA routing so the gossip floor doesn't
collapse under broadcast load.

To make compute-exchange work *in the current trusted mode*, what
exists is sufficient — and that appears to be what
`apps/compute-exchange/src/orderbook.rs` is doing now (it imports
`pyana_intent::partial_fill::{PartialFillError, check_fill_amount}`
and nothing more).

## §8. Privacy story

No `BOUNDARIES.md` exists yet (was not authored in parallel). Below
is what the intent crate's code actually delivers, in the
*current* deployed state (not the trustless-future state).

Boundaries for a pending intent (after posting, before match):

| Observer | Learns |
|---|---|
| Same federation node receiving the broadcast | Full MatchSpec (cleartext gossip); creator's `CommitmentId`; stake proof commitment bytes (not value); expiry; any optional fields |
| Wallet on the network running `match_intent` | Same as above (gossip is broadcast) |
| Network-level observer (sniffing peer connections) | Same as above + IP-level metadata; gossip-relay topology |
| Sealed-box `sse::EncryptedIntent` consumer | Encrypted blob; SSE search tokens (one per keyword in the MatchSpec) — *plus*: keyword tokens are rotated by epoch, so cross-epoch unlinkable |

Boundaries for a matched intent (after `match_intent` returns
Matched, before fulfillment delivery):

| Observer | Learns |
|---|---|
| The matcher (locally) | That the intent matches *some* token they hold; which token (index into `held_tokens`); the match's commitment-id-only `satisfier` field |
| The intent creator | Nothing yet (no message has been sent) |
| Other wallets | Nothing about this match (matches are local, not broadcast) |

Boundaries after fulfillment delivery:

| Observer | Learns |
|---|---|
| Intent creator | The `Fulfillment` (mode-dependent); `fulfiller: CommitmentId` only — **not** their cell ID; granted_actions, granted_resource, expiry; in Trusted mode, the actual attenuated macaroon; in Private/Selective, a STARK proof |
| Network observer (commit-reveal layer) | Commitment hashes, then reveals — with `delay_pool` dummies mixed in, can't easily correlate commit-to-reveal |
| Network observer (no commit-reveal) | The reveal in the clear (it's broadcast) |

Boundaries the trustless engine would deliver (if implemented):
- Pending intent: nobody learns the MatchSpec (threshold-encrypted).
- Matched intent: only the solver who finds the match learns it
  (after threshold decryption); everyone learns the
  `SolverSubmission`.
- Matched parties' identities: still commitments only.
- Matched amounts/values: visible in the `RingTrade`'s `Settlement`
  legs — these aren't hidden, just the *who* is anonymous.

Important: the creator identity is NOT revealed at any stage as long
as `CommitmentId` is fresh per intent. Multiple intents from the
same wallet are unlinkable *unless* the wallet chooses to reuse a
commitment.

## §9. Open questions for the designer

1. **Is `TrustlessIntentEngine` aspirational or in-progress?** If
   aspirational: it shouldn't live alongside production code without
   a clearer "[NOT WIRED]" marker. If in-progress: what's the
   target deployment window, and what's the missing-piece backlog?

2. **Are the two `DecryptionShare` types** (intent vs federation)
   meant to converge? Federation's is real crypto for turn-bodies;
   intent's is a counter. Bridging them — or replacing intent's
   with federation's — would be the obvious unification.

3. **The lowered "settle_ring_leg" method has no implementor.** Is
   there a missing settlement-cell module? Or should lowering emit
   bare effects on the participants' cells (with the corresponding
   authorization changes)?

4. **`AutoFulfillPolicy::ForPatterns`** — is the current behavior
   (pattern-against-pattern) intentional, or a bug? It's hard to
   imagine a use case where it would match anything.

5. **The two commit-reveal implementations** — should they be
   unified, or is the layered model (gossip-level + execution-level)
   the intent? If the latter, the docs should say so explicitly.

6. **Bond escrow** — when does the solver bond actually leave the
   solver's wallet? Today it's only a struct field. Is the
   intention to enforce on-chain escrow at submission time, with
   slashing via a follow-up turn?

7. **DFA routing for intent gossip** — the generalized solver has
   `zone: Option<String>` but the gossip layer ignores it. Is this
   waiting on a DFA topic-filter implementation, or has the design
   moved away from it?

8. **The PIR 2-server pairing protocol** — clients are trusted to
   pick two non-colluding servers; the node API doesn't enforce or
   document a pairing convention. Should there be a federation-
   advertised "PIR partner" registry?

9. **SSE-token discovery** — the SSE primitives are implemented but
   the node has no query endpoint. Is the plan for fulfillers to
   poll PIR and SSE-match locally, or for a node-side coarse-filter?

10. **`predicate_requirements` validation** — should `validate_intent`
    cap their count and string length, the same way it caps actions
    and constraints?

## §10. Recommended next steps (ranked by leverage)

1. **Either wire `TrustlessIntentEngine` into the node, or annotate
   it as unimplemented.** Right now the crate root docstring presents
   it as the target trust model. Either the node should grow a
   batch-pipeline, or the doc should be honest that no production
   path uses it. (Highest leverage: removes the largest gap between
   documentation and reality.)

2. **Bridge `intent::trustless::DecryptionShare` with
   `federation::threshold_decrypt`.** The federation crate has the
   real cryptography (Shamir + ChaCha20-Poly1305 + MAC verification).
   The intent engine needs to import that pipeline rather than
   carry its own opaque-bytes placeholder. This converts a stub into
   a working primitive with one wiring change.

3. **Implement a real `ProofVerifier`** (or document
   `MockProofVerifier` as test-only and panic in production). The
   STARK circuit for solver validity is the missing piece — it would
   prove "given the decrypted intent set, the submitted ring set is
   a valid disjoint cover with the claimed score." `pyana-circuit`
   already has the AIR machinery to build this.

4. **Implement `settle_ring_leg` on a settlement cell**, or change
   lowering to emit bare-effect actions on participants' cells. The
   current lowered Turn isn't executable on any deployed cell.

5. **Fix `AutoFulfillPolicy::ForPatterns`** to glob the intent's
   *target resource* (or the action's resource) rather than its
   resource_pattern string. Add a test that the current behavior is
   wrong (it should fail).

6. **Unify the two commit-reveal modules.** Probably promote
   `commit_reveal_fulfillment` to be the canonical one (it has the
   abandon-penalty bookkeeping and the epoch-binding fix), and
   reduce `gossip::IntentPool`'s version to a thin wrapper.

7. **Unify the `node::state::intent_pool` with
   `gossip::IntentPool`.** Right now the hardened pool with rate
   limits, nullifier tracking, validation, and stake checking only
   protects clients; the node accepts intents into its own
   unhardened mirror. The hardening should run server-side too.

8. **Add `mark_fulfilled` calls to all fulfillment exit paths**, not
   just `gossip::reveal_fulfillment`. The current path is the only
   one with replay protection.

9. **Consolidate the solver's scoring** so `find_rings` and
   `validate_ring` produce the same `RingTrade.score` semantics.
   Remove the dead `.min(...).max(...)` arithmetic in settlement
   construction.

10. **Add `predicate_requirements` validation** to `validate_intent`
    (count cap + string-length caps).

11. **Wire the SSE matcher**: add a node endpoint that serves
    SSE-matching against the `encrypted_intent_pool`, completing the
    encrypted-discovery loop.

12. **Either consume `AssetRegistry` or delete it.** Dead types
    accumulate confusion.

13. **Promote `TrustlessIntentEngine` to accept
    `GeneralizedRingTrade`**, or define a common settlement schema,
    so heterogeneous rings can flow through the trustless pipeline.

14. **Document the DFA-routing plan** for intent gossip — either
    implement zone-keyed topic filters (using
    `dfa::filter::TopicFilter`) or explicitly defer.

15. **Bond escrow** — wire `SolverSubmission.bond` through an
    actual escrow turn so slashing becomes meaningful.
