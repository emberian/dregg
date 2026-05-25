// =============================================================================
// Section 4: Zero-Knowledge Proof System
// =============================================================================

= Zero-Knowledge Proof System

== Commitment Scheme

=== 4-ary Merkle Trees

Pyana uses quaternary Merkle trees: each internal node hashes 4 children via $"Poseidon2"(c_0, c_1, c_2, c_3)$ over BabyBear (width 8, $alpha = 7$, 8 external + 22 internal rounds). The 4-ary structure halves tree height relative to binary trees.

=== Multi-Hash Roots

The reference group publishes roots under multiple commitment schemes:

$ R_"STARK" &= "Poseidon2Root"(F) \
  R_"Binius" &= "Groestl256Root"(F) \
  R_"Halo2" &= "PoseidonBN254Root"(F) $

Each proof backend references the root native to its field.

=== Fold Deltas

A _fold delta_ records a monotonic state transition: $Delta_(i -> i+1) = { f in F_i | f in.not F_(i+1) }$. The commitment to $F_(i+1)$ can be computed incrementally from $F_i$ and $Delta$---this is the structure enabling IVC.

== The Fold AIR

The STARK proves:

#quote(block: true)[
  "There exists a sequence of fact sets $F_0 supset.eq F_1 supset.eq ... supset.eq F_k$ such that $F_0$ is committed under a group-attested root, each $F_(i+1) = F_i backslash Delta_i$ for valid removal sets $Delta_i$, and evaluating the standard policy rules over $F_k$ with the given request yields `allow`."
]

The AIR has three constraint families: membership (facts are valid leaves), fold (removals are correct), and derivation (Datalog steps are valid).

== Public Inputs and Zero-Knowledge

The verifier receives: group root $R$, authorization request $(A, S, "Act")$, current time $t$, and the proof $pi$ ($tilde$24 KiB). From these, verification produces a single bit. The verifier learns nothing about chain length, intermediate delegators, other capabilities, or the issuer's identity.

All STARK proofs use real Poseidon2 constraints over BabyBear4 (degree-4 extension field, providing 124-bit security). There are no vacuous or mock constraints in the production path.

== Proof Architecture

This section precisely states what each proof in the system proves, how they compose, and the resulting security guarantees. We work over $FF_p$ where $p = 2^(31) - 2^(27) + 1$ (BabyBear) with degree-4 extension $FF_(p^4)$ providing 124-bit challenge security.

=== Poseidon2 Permutation Proof

*Public inputs:* Input state $bold(x) in FF_p^8$, output state $bold(y) in FF_p^8$.

*Private witness:* None (this is a deterministic computation proof).

*Statement:* $bold(y) = "Poseidon2"(bold(x))$ where Poseidon2 uses width 8, $alpha = 7$ (degree-7 S-box), 8 external rounds + 22 internal rounds.

*Constraints:* The AIR evaluator recomputes the full Poseidon2 permutation inside the constraint function and checks $bold(y)_i - "computed"_i = 0$ for all $i in {0, ..., 7}$, combined via random linear combination with verifier challenge $alpha$. Constraint degree: 7.

*Soundness:* A cheating prover claiming $bold(y)' != "Poseidon2"(bold(x))$ produces a nonzero constraint polynomial. The STARK quotient polynomial then has degree exceeding the expected bound, and FRI rejects with overwhelming probability.

=== Merkle Membership Proof

*Public inputs:* Leaf hash $ell in FF_p$, root $r in FF_p$.

*Private witness:* For each level $i in {0, ..., d-1}$: siblings $(s_(i,0), s_(i,1), s_(i,2)) in FF_p^3$ and position $p_i in {0, 1, 2, 3}$.

*Statement:* $exists$ authentication path from $ell$ to $r$ in a 4-ary Poseidon2 Merkle tree of depth $d$.

*Constraints (per level):*

$ &"position validity:" quad p_i (p_i - 1)(p_i - 2)(p_i - 3) = 0 \
  &"hash binding:" quad "parent"_i = "Poseidon2"_("4-to-1")(c_0, c_1, c_2, c_3) $

where children $(c_0, ..., c_3)$ are determined by Lagrange interpolation on position: the current hash occupies slot $p_i$, siblings fill the remaining slots. Chain continuity: $"parent"_i = "current"_(i+1)$, with $"current"_0 = ell$ and $"parent"_(d-1) = r$.

*Soundness:* Finding a false membership proof requires either (a) a Poseidon2 collision (finding two distinct inputs that hash to the same output), or (b) forging a valid low-degree polynomial that satisfies the degree-7 hash constraint at random evaluation points. Both reduce to collision resistance of Poseidon2 over $FF_p$.

=== Body Membership Proof

*Public inputs:* Body fact hash $h in FF_p$, state root $R_0 in FF_p$.

*Private witness:* Merkle path from $h$ to $R_0$ (siblings and positions at each level).

*Statement:* The body fact with hash $h$ is a valid leaf in the 4-ary Poseidon2 Merkle tree committed under $R_0$.

*Constraints:* Identical to the general Merkle membership proof above, instantiated with the state root as target. The body membership proof is required for every body atom in a Datalog derivation---the derivation AIR's `body_root` column must equal the public state root $R_0$ for every active row.

*Why this is separate:* Body membership was previously implicit in the derivation proof (body facts were assumed present). The explicit body membership requirement ensures that a prover cannot claim derivation from facts not committed in the state tree---closing a soundness gap where a prover could introduce phantom facts into the derivation witness.

=== Note Spending Proof

*Public inputs:* Nullifier $nu in FF_p$, Merkle root $r in FF_p$.

*Private witness:* Owner $o$, value $v$, asset type $a$, creation nonce $n$, randomness $rho$, spending key $k$, Merkle path $(bold(s)_i, p_i)$ for $i in {0, ..., d-1}$.

*Statement:* There exist $(o, v, a, n, rho, k)$ and a Merkle path such that:

$ "commitment" &= "Poseidon2"(o, v, a, n, rho) \
  nu &= "Poseidon2"("commitment", k, n) \
  &"commitment is a leaf under root" r "via the given path" $

*Constraints (5 families):*
+ _Is-Merkle binary:_ $m dot (m - 1) = 0$ where $m$ gates commitment vs. Merkle rows.
+ _Commitment preimage (row 0):_ $(1-m) dot ("commitment" - "Poseidon2"(o, v, a, n, rho)) = 0$.
+ _Nullifier derivation (row 0):_ $(1-m) dot (nu - "Poseidon2"("commitment", k, n)) = 0$.
+ _Position validity (all rows):_ $p(p-1)(p-2)(p-3) = 0$.
+ _Hash binding (Merkle rows):_ $m dot ("parent" - "Poseidon2"_("4-to-1")("children by position")) = 0$.

*Soundness:* A cheating prover cannot:
- Spend without the spending key: producing a valid $nu$ requires knowing $k$ (Poseidon2 preimage resistance).
- Spend a nonexistent note: the commitment must exist in the tree (Merkle soundness).
- Double-spend: the nullifier $nu$ is deterministic given $(k, "commitment", n)$; the verifier maintains a nullifier set and rejects duplicates.

=== Balance Range Check

*Public inputs:* None (embedded within the Effect VM conservation check).

*Statement:* The balance after a transfer is non-negative: $"balance"_"post" >= 0$.

*Constraint:* A boolean decomposition enforces non-negativity without revealing the exact value:

$ "balance"_"post" = sum_(j=0)^(30) b_j dot 2^j, quad b_j dot (b_j - 1) = 0 quad forall j $

The 31-bit decomposition with each $b_j$ constrained to ${0, 1}$ guarantees the value fits in $[0, 2^(31) - 1]$. This replaces the previous approach of checking only the high bit, which suffered from a truncation bug where negative values with the high bit clear could pass validation.

=== Multi-Step Datalog Derivation Proof

*Public inputs:* Initial state root $R_0 in FF_p$, request hash $h in FF_p$, conclusion $c in {0, 1}$, step count $N$, final accumulated hash $H_N in FF_p$.

*Private witness:* For each step $i in {1, ..., N}$: rule ID, body fact hashes, substitution $sigma$, head predicate, head terms, equal/memberof/GTE checks.

*Statement:* Starting from fact set committed under $R_0$, there exists a sequence of $N$ valid Datalog rule applications where:
- Each step's body facts have hashes present under root $R_0$
- Variable substitutions are correctly applied (selector columns enforce $sigma$)
- Equal checks hold: $sigma("lhs") = sigma("rhs")$
- MemberOf checks hold: element $in$ set
- GTE checks hold via bit decomposition (high bit = 0 ensures non-negative diff)
- The final step derives predicate $"ALLOW"$ (if $c = 1$)
- The hash chain $H_i = "Poseidon2"(H_(i-1) || "derived_hash"_i)$ commits to the full trace

*Constraints (19 families):* Binary flags, substitution application via selector one-hot vectors, equal/memberof enforcement, GTE range check (31-bit decomposition with high-bit-zero), accumulated hash chain correctness, final-step-derives-ALLOW (gated by conclusion), body roots match state root, active-monotone-decreasing.

*Constraint degree:* 4 (dominated by position validity and GTE bit binary checks).

*Soundness:* A cheating prover cannot:
- Claim ALLOW without deriving it: the constraint $c dot "is_final" dot ("head_pred" - "ALLOW") = 0$ forces the final step's predicate to be ALLOW when $c = 1$.
- Skip a rule step: the accumulated hash chain commits to every derivation step; tampering changes $H_N$.
- Use facts not in the committed set: body root constraints force $"root"_i = R_0$ for every active body atom.
- Forge a substitution: selector-sum and substitution-application constraints algebraically bind derived terms to body atoms.

=== Fold Chain (Attenuation) Proof

*Public inputs:* Old root $R_"old" in FF_p$, new root $R_"new" in FF_p$.

*Private witness:* Removed facts with predicates, terms, and Merkle membership proofs under $R_"old"$.

*Statement:* There exists a set of facts $Delta subset.eq F_"old"$ such that removing $Delta$ from the fact set committed under $R_"old"$ yields the fact set committed under $R_"new"$, and each fact in $Delta$ has a valid Merkle membership proof under $R_"old"$.

*Constraints:*
- Fact hash correct: $"hash" = "Poseidon2"("predicate", "terms")$
- Membership verified: each removed fact's hash is a valid leaf under $R_"old"$
- Root transition binding: $"transition_hash" = "Poseidon2"(R_"old" || R_"new" || "fact_hashes")$

*Soundness:* Capability amplification is impossible: the prover can only _remove_ facts from $F_"old"$ (enforced by membership proofs under $R_"old"$). Adding a fact not in $F_"old"$ requires forging a Merkle membership proof---equivalent to breaking Poseidon2 collision resistance.

=== IVC Fold Chain Accumulation

*Public inputs:* Initial root $R_0 in FF_p$, final root $R_N in FF_p$, step count $N$, accumulated hash $H in FF_p$.

*Private witness:* For each step $i$: old root, new root, fold validity flag, hash chain values.

*Statement:* There exists a sequence of $N$ valid fold steps $R_0 -> R_1 -> ... -> R_N$ where:
- Each transition is a valid fold (monotone fact removal)
- Root continuity: $R_i^"new" = R_(i+1)^"old"$
- Hash chain: $H_i = "Poseidon2"(H_(i-1) || R_i^"new" || i)$ with $H_0 = "Poseidon2"("IVC0" || R_0 || 0)$
- The final accumulated hash $H = H_N$

*Key property:* The proof is _constant size_ regardless of $N$. Growth is $O(log N)$ via FRI compression.

*Soundness:* Reordering attacks are prevented by including step count in the hash. Chain breaks (skipping a root transition) are caught by root continuity constraints. The trace commitment binds the IVC proof to actual fold computations.

=== Recursive Verification Proof

*Public inputs:* Inner proof's public inputs $pi_0, ..., pi_k$, proof commitment $C in FF_p$.

*Private witness:* The inner proof's trace commitment, constraint commitment, FRI betas, query index, query trace values, Merkle authentication paths, quotient value, FRI layer values.

*Statement:* There exists a valid STARK proof $pi$ whose public inputs are $(pi_0, ..., pi_k)$ and whose verification passes: Fiat-Shamir transcript replay produces challenges consistent with the committed data, FRI folding relations hold ($"even" + beta dot "odd" = "folded"$), and the quotient polynomial check passes at the queried point.

*Constraints:*
- Validity binary and always-one: every row passes its local check
- Section tag validity: $"tag" in {0, 1, 2, 3, 4}$
- FRI folding: $"data"_3 = "data"_0 + "data"_2 dot "data"_1$ (universal, satisfied trivially by non-FRI rows)
- Proof commitment binding (last row): $"challenge_acc" = C$ (public input)

*Soundness:* Forging a recursive proof requires either finding a valid STARK proof for a false statement (STARK soundness) or producing a verifier trace that claims valid-but-actually-isn't (caught by the constraint that validity flags must all be 1 and the FRI folding must hold algebraically). The Poseidon2 hash chain in `challenge_acc` binds all verification data, so the final commitment uniquely identifies the verified proof.

== Proof Composition

=== Full Authorization Proof

The complete authorization proof composes:

#align(center)[
#block(
  fill: luma(248),
  inset: 12pt,
  radius: 4pt,
)[
```
Full Authorization Proof =
    Derivation Proof (N rule steps -> ALLOW)
  + Body Membership Proofs (each body fact in tree under R_0)
  + Fold Chain Proof (R_issuer -> R_0 via attenuation)
  + Issuer Membership Proof (issuer in group Merkle tree)
```
]]

The binding between components uses shared public inputs:
- The derivation proof's `initial_state_root` = the fold chain's `final_root` $R_0$
- The fold chain's `initial_root` = the issuer's committed capability root
- The issuer membership proof's root = the reference group's attested root

=== Note Spending Proof

#align(center)[
#block(
  fill: luma(248),
  inset: 12pt,
  radius: 4pt,
)[
```
Note Spending Proof =
    Spending Key Knowledge (nullifier = H(commitment || key || nonce))
  + Commitment Preimage (commitment = H(owner || value || asset || nonce || rand))
  + Merkle Membership (commitment in note tree under root r)
  + Balance Range Check (post-transfer balance >= 0 via boolean decomposition)
```
]]

All sub-statements are enforced in a _single_ AIR with 12 columns. The commitment row (row 0) handles key knowledge and preimage; subsequent rows handle Merkle membership. A row-type flag gates which constraints apply. This avoids composition overhead---one proof, one FRI invocation.

=== Full Private Presentation

#align(center)[
#block(
  fill: luma(248),
  inset: 12pt,
  radius: 4pt,
)[
```
Full Private Presentation =
    Authorization Proof (conclusion = ALLOW, root, accumulated_hash)
  OR Note Spending Proof (nullifier, note_tree_root)

IVC-Compressed Presentation =
    IVC Fold Chain (constant-size, covers N attenuation steps)
  + Derivation Proof (final state -> ALLOW)
  + Body Membership Proofs (all body facts under state root)
  + Issuer Membership Proof (issuer in group)
```
]]

The verifier of a Full Private Presentation receives only: a group root $R_F$, a conclusion bit, and the proof(s). It learns nothing about delegation chain length, intermediate authorities, or the agent's other capabilities.

=== Receipt Chain with IVC

#align(center)[
#block(
  fill: luma(248),
  inset: 12pt,
  radius: 4pt,
)[
```
Receipt Chain (N turns) =
    N x State Transition (pre_hash -> post_hash, effects_hash, cost)

IVC-Compressed Receipt Chain =
    Single constant-size proof (initial_state -> final_state)
    + Nullifier non-membership proof
```
]]

Each state transition step contributes one fold to the IVC accumulator. The accumulated hash $H_N = "Poseidon2"(H_(N-1) || R_N || N)$ commits to the full history. Verification is $O(1)$: check the IVC proof, check the final state commitment, check nullifier freshness.

== Why N Proofs Instead of One

The authorization proof currently consists of N separate sub-proofs (derivation + memberships + fold + issuer) rather than a single monolithic proof. This is because:

+ *Different AIRs, different trace shapes.* The Merkle membership AIR has width 6 and depth-dependent rows. The derivation AIR has width 92 with $N$ rows. The fold AIR has width 12. Combining them into a single AIR would require a trace width of $max(6, 12, 92) = 92$ with most columns unused in most rows---wasting prover time on zero constraints.

+ *Modularity.* Each proof can be generated independently and in parallel. The Merkle proofs are embarrassingly parallel; the derivation proof depends only on the committed fact set.

+ *Incremental verification.* A verifier can reject early: if the issuer membership proof fails, it need not check the derivation.

The proofs are bound together via shared public inputs. Specifically, the derivation proof's state root $R_0$ must equal the fold chain's final root, and the fold chain's initial root must appear as a leaf in the issuer membership proof. Tampering with any binding breaks the corresponding Merkle or hash commitment.

== Path to a Single Proof

Recursive verification collapses N proofs into 1:

+ *Generate* each sub-proof (derivation, fold, memberships) independently.
+ *Recursively verify* each sub-proof inside a new STARK circuit. The recursive verifier AIR encodes Fiat-Shamir transcript replay, FRI folding checks, and constraint evaluation at queried points.
+ *Chain* the recursive proofs: the proof verifying sub-proof $k$ also verifies the recursive proof covering sub-proofs $1, ..., k-1$.
+ The final output is a single STARK proof of constant size ($tilde 24$ KiB) that transitively attests to all sub-proofs.

*Current status and the corrected aggregation architecture:* Sequential IVC chains via `build_recursive_ivc_chain` work; pairwise recursive verification via Plonky3 works for simple AIRs. STARK-in-Pickles wrapping over the Pasta curve cycle is structurally present in `circuit/src/backends/stark_in_pickles.rs` + `circuit/src/poseidon_stark*.rs` (the existing skeleton).

The earlier Stage 7-$zeta$ "Mangrove-style chunked folding" architecture turns out to be *unsound* in its proposed wrap layer (a hash chain over leaf-proof bytes is metadata, not soundness; a verifier-acceptance check must be inside the AIR). The corrected architecture, validated against SP1 v6 Hypercube, Stwo/SHARP, and RISC Zero:

```
inner proof bytes -> canonical parser ->
  verifier AIR that enforces accept = 1
    (parser + Merkle paths + challenger + FRI/openings + final accept) ->
  acceptance bit constrained to 1 ->
  recursive compression tree ->
  optional final wrapper for export
```

Hash chains are *fine as metadata after acceptance is enforced*, not as the soundness mechanism. The `plonky3_verifier_air.rs` placeholder in the existing tree is precisely what becomes functional in the generalized `plonky3_recursion_impl` (Lane Golden-Edge Block 1).

Two outer-recursive-layer paths are live in the codebase:

- *Fix the verifier AIR (transparent path)*: lift `plonky3_recursion_impl` past `P3MerklePoseidon2Air` into a real verifier-as-AIR, generic over the inner AIR shape. Stays transparent end-to-end; same field (BabyBear), same hash (Poseidon2), same toolchain.
- *Kimchi/Pickles (production-proven outer layer)*: $tilde$9.7K LOC of `circuit/src/backends/kimchi_native/` (predicate circuits) plus $tilde$5.8K LOC of `circuit/src/backends/mina/` (assisted-recursion `pickles.rs` + dual-curve step/wrap) plus the $tilde$3.2K LOC `stark_in_pickles.rs` skeleton. Mina compresses a whole chain to $tilde$22 KiB with $tilde$864-byte state proofs and $tilde$200ms verification. Loses transparency at the outer layer; gains a production-proven recursive primitive. Same overall shape as RISC Zero, with Kimchi instead of Groth16.

The DSL composition operators (`compose_and`, `compose_or`, `compose_chain`, `compose_aggregate`) provide the structural framework for proof combination with cryptographic binding via shared public inputs and VK-hash linking columns. Full composition of heterogeneous AIRs (derivation + fold + membership + Effect VM in one recursive proof) is designed and structurally supported; arbitrary-N aggregation today uses sequential chaining, with the corrected tree-shaped substrate (verifier-AIR-as-leaf) approaching the Golden Vision of folded mesh.

== Soundness Analysis

=== Per-Component Security

#figure(
  table(
    columns: (auto, auto, auto),
    align: (left, left, left),
    table.header([*Component*], [*Security Parameter*], [*Bound*]),
    [BabyBear4 extension field], [$|FF_(p^4)| approx 2^(124)$], [124-bit challenge],
    [FRI proximity (50 queries, blowup 4)], [$2^(-50) dot (1/4)^(50)$], [$tilde$100-bit soundness],
    [Poseidon2 ($alpha = 7$, width 8)], [Min($|FF_p| dot d, 2^(128)$)], [$tilde$124-bit collision],
    [BLAKE3 Merkle (trace commitment)], [256-bit output], [128-bit collision],
    [Fiat-Shamir (BLAKE3 transcript)], [256-bit state], [128-bit binding],
  ),
  caption: [Security bounds for each proof system component.],
)

=== System Security

The overall system security is the minimum across all components:

$ lambda_"system" = min(lambda_"field", lambda_"FRI", lambda_"hash", lambda_"FS") approx 100 "bits" $

The FRI soundness ($tilde$100 bits with 50 queries and blowup factor 4) is the binding constraint. This is standard for STARKs at this parameter set; production deployment would increase to 80--128 queries for 128-bit security.

=== What Composition Does Not Hide

The number of sub-proofs in a non-recursive presentation leaks the _structure_ (though not the _content_) of the authorization. Specifically:
- A 3-proof presentation reveals "there was a fold chain, a derivation, and an issuer check"
- Proof sizes reveal approximate trace lengths (hence: delegation chain length, derivation depth)

Recursive composition eliminates this leakage: the final proof is constant-size and reveals only the conclusion bit. This is why recursive verification is architecturally critical---not merely a performance optimization, but a privacy requirement.

== Cross-Cell Algebraic Binding (Stage 7-$gamma$.2) <sec-gamma-2>

The shared-PI bundle from Stage 7-$gamma$.0 (`TURN_HASH`, `EFFECTS_HASH_GLOBAL`, `ACTOR_NONCE`, `PREVIOUS_RECEIPT_HASH`) joins per-cell proofs of *one turn* into one bundle: the verifier's PI-matching loop requires all per-cell proofs to agree on these fields. That closes *"are these proofs from the same turn?"*. It does *not* close *"do these two proofs describe the same `Transfer` / `GrantCapability` / `Introduce`?"*---as soon as cells live on different federations or are shipped to a verifier weeks apart, the executor's say-so isn't reachable.

Stage 7-$gamma$.2 Phase 1 closes that gap with new PI fields whose canonical derivation is publicly computable from the bilateral effect's surface inputs. The verifier, given two `WitnessedReceipt`s, recomputes the canonical id from one side, looks it up in the other side's PI, and confirms match. The AIR binds in-trace transfer/grant/intro data to the same id, so a prover cannot emit a proof whose claimed id is unrelated to the actual amount/direction/cap-entry it wrote into the trace.

=== Canonical bilateral identifiers

Three bilateral effects each get a deterministic instance id:

$ "transfer_id" &= "Poseidon2"("pyana-transfer-id-v1" || "from" || "to" || "amount" || "ACTOR_NONCE") \
  "grant_id" &= "Poseidon2"("pyana-grant-id-v1" || "from" || "to" || "cap_entry_hash" || "ACTOR_NONCE") \
  "intro_id" &= "Poseidon2"("pyana-intro-id-v1" || "introducer" || "recipient" || "target" || "permissions_bits" || "introducer_nonce") $

`ACTOR_NONCE` is already in PI (from $gamma$.0), so the verifier can re-derive any id from the bilateral effect's surface inputs without additional witness data.

=== New PI fields

Per-cell PI grows by 35 felts to accommodate Phase 1's bilateral accumulators (post-$gamma$.2 `BASE_COUNT = 73`, up from $gamma$.0's 38):

- *Counts (7 felts)*: `OUTBOUND_TRANSFER_COUNT`, `INBOUND_TRANSFER_COUNT`, `OUTBOUND_GRANT_COUNT`, `INBOUND_GRANT_COUNT`, `INTRO_AS_INTRODUCER_COUNT`, `INTRO_AS_RECIPIENT_COUNT`, `INTRO_AS_TARGET_COUNT`. Predict the number of entries each accumulator carries.
- *Accumulators (28 felts, 7 $times$ 4)*: `OUTGOING_TRANSFER_ROOT`, `INCOMING_TRANSFER_ROOT`, `OUTGOING_GRANT_ROOT`, `INCOMING_GRANT_ROOT`, `INTRO_AS_INTRODUCER_ROOT`, `INTRO_AS_RECIPIENT_ROOT`, `INTRO_AS_TARGET_ROOT`. Each is a 4-felt Poseidon2 hash accumulating $"hash"("id" || "peer_cell_id" || "amount_lo" || "amount_hi")$ per bilateral row, with direction baked into the domain separator.

`peer_cell_id` is folded into the accumulator absorb rather than surfaced separately, to avoid leaking cross-cell topology to a public verifier when the witness is sealed.

=== Off-AIR verifier algorithm

The `pyana-verifier` standalone binary gains a `bilateral-pair <receipt_a> <receipt_b>` subcommand that verifies cross-cell consistency:

+ Parse both receipts; verify each per-cell STARK independently.
+ Recompute the canonical id (e.g., `transfer_id`) from the bilateral effect's surface inputs $(""from"", ""to"", ""amount"", ""ACTOR_NONCE"")$.
+ Walk the sender's `OUTGOING_TRANSFER_ROOT` accumulator entries; for each, locate the matching entry in the receiver's `INCOMING_TRANSFER_ROOT`.
+ Confirm direction, amount, and id agreement.
+ If any sender entry lacks a matching receiver entry (or vice versa), reject.

Sentinel handling: when a per-cell proof has no bilateral effects of a kind, the corresponding root field is `Commitment4::empty()` and the count is 0; the match loop short-circuits when both sides are sentinels.

=== Phase 2: joint aggregation AIR

Phase 1 binds via PI and an off-AIR verifier. Phase 2 lifts the match-loop *inside* an AIR: a joint aggregation circuit takes the two per-cell proofs as witness and constrains the bilateral binding algebraically. This is built atop the generalized `plonky3_recursion_impl` substrate (Lane Golden-Edge Block 1), which lifts the recursive verifier AIR past the `P3MerklePoseidon2Air` placeholder into a real verifier-as-AIR. The result: cross-cell binding becomes a single STARK that any third party verifies in one verification call.

== Sovereign-Witness AIR Teeth <sec-sovereign-witness-air>

The sovereign-witness path historically had *no AIR teeth*: `SovereignCellWitness` was a federation-side bookkeeping handshake whose only binding was the pre-image relation between `witness.cell_state.state_commitment()` and the federation's stored commitment. The Phase 1 design adds minimal AIR teeth:

- *New trace column*: `WITNESS_KEY_COMMIT` (single BabyBear felt). Computed by the prover as $"Poseidon2"("cell.owner_pubkey")$. For non-sovereign-witnessed turns, zero (sentinel).
- *New PI slots*: `SOVEREIGN_WITNESS_KEY_COMMIT` (verifier-supplied; bound to the signature key that the executor's pre-AIR check verified under) and `IS_SOVEREIGN_CELL` (boolean PI gating the teeth).
- *New boundary constraint*: when `IS_SOVEREIGN_CELL == 1`, $"WITNESS_KEY_COMMIT" == "SOVEREIGN_WITNESS_KEY_COMMIT"$ at row 0.

Phase 1 closes the "any-snooper-can-resubmit" surface (the wire malleability gap from the sovereign-witness audit §2.2)---the AIR now witnesses that the witness's signing identity matches the cell's owning key.

Phase 2 recurses into the optional `transition_proof: Option<Vec<u8>>` on the witness. When present, the AIR calls Lane Golden-Edge's recursive verifier AIR to attest that the transition itself is sound. This replaces the witness-vs-proof-carrying fork (today mutually exclusive) with a layered spectrum: witnesses always carry signature teeth (Phase 1); witnesses with `Some(transition_proof)` additionally carry algebraic-validity teeth (Phase 2).

== Proof Backend Agility: The Constraint DSL

Rather than manually implementing circuits for each proof system, Pyana provides a constraint DSL (`#[pyana_caveat]` and `#[pyana_effect]` proc macros) that compiles a single `CircuitDescriptor` into 8 code generation backends:

#figure(
  table(
    columns: (auto, auto, auto),
    align: (left, left, left),
    table.header([*Backend*], [*Output*], [*Use Case*]),
    [Rust], [Runtime evaluator function], [Trusted-mode fast path],
    [AIR], [Constraint descriptor for custom STARK], [Primary proof generation],
    [Datalog], [Rule fragment for policy evaluation], [Lightweight authorization],
    [Kimchi], [Gate descriptor for Pasta-curve circuits], [Mina-compatible recursion],
    [STARK], [Compile-time AIR impl (`StarkAir` trait)], [Custom prover integration],
    [Midnight/ZKIR v3], [Program for Midnight contracts], [Cardano/Midnight interop],
    [Plonky3], [Native `Air` trait impl for p3-uni-stark], [Production proving],
    [SP1], [RISC-V guest program for Succinct's zkVM], [EVM bridge (Groth16)],
  ),
  caption: [DSL code generation backends. All backends prove the same logical statement; the choice is made at prove-time based on deployment requirements.],
)

The DSL supports composition operators that combine multiple circuit proofs:

- `compose_and(A, B)`: Both A and B must verify; shared public inputs are linked.
- `compose_or(A, B)`: At least one verifies (with a selector column).
- `compose_chain(proofs)`: Sequential IVC chain---each step verifies the previous.
- `compose_aggregate(set)`: All verify; public inputs are merged.

Sub-proofs are cryptographically bound via VK hashes and public-input linking columns in the composed trace.

=== DSL Lookup Tables

The DSL now supports _lookup table constraints_---a column can be constrained to contain only values that appear in a committed table. Lookup tables are used for:

- *DFA routing*: Each $(q_i, c_i, q_(i+1))$ transition is checked against the committed DFA transition table.
- *Opcode dispatch*: Effect VM opcode validity is enforced via a 24-entry opcode table.
- *Permission sets*: EffectMask validation uses a lookup into the permitted effects table.
- *Predefined constants*: Round constants for Poseidon2 are committed as a lookup table rather than hardcoded in constraints.

Lookup arguments use the log-derivative technique (LogUp): the prover demonstrates that a multiset of trace values is a subset of the table via a running sum that must equal zero at the trace boundary. This adds one auxiliary column per lookup relation.

== Three Production Provers

#figure(
  table(
    columns: (auto, auto, auto, auto, auto),
    align: (left, left, center, center, center),
    table.header([*Prover*], [*Field/Curve*], [*Proof Size*], [*PQ?*], [*Recursion*]),
    [Custom STARK (BabyBear/FRI)], [$FF_(2^(31)-2^(27)+1)$ + FRI], [$tilde$24 KiB], [Yes], [Via Plonky3],
    [Plonky3 (p3-uni-stark)], [BabyBear + FRI], [$tilde$24 KiB], [Yes], [Operational],
    [Kimchi/Pickles (Pasta)], [Pallas/Vesta + IPA], [$tilde$10 KiB], [No], [Native (assisted)],
  ),
  caption: [Production proof system characteristics. The custom STARK and Plonky3 backends share the BabyBear field; Kimchi/Pickles uses the Pasta curve cycle for constant-size recursive proofs.],
)

=== STARK-in-Pickles Composition

The STARK-in-Pickles pipeline wraps a BabyBear STARK proof in a Kimchi verifier circuit (~30K gates) to produce a Pickles recursive SNARK (constant-size, Pasta curves). The pipeline:

+ Generate STARK proof over BabyBear (fast, PQ-secure, ~24 KiB).
+ Commit the STARK proof via Poseidon2 (pre-hash and post-hash binding).
+ Verify the STARK algebraically inside a Kimchi circuit (FRI folding + Fiat-Shamir replay).
+ Produce a Pickles recursive proof (constant-size, Mina-compatible).

This enables Mina-native verification of Pyana proofs and constant-size proof accumulation regardless of the number of underlying STARK proofs.

=== EVM Bridge via SP1

For Ethereum/Base settlement, the SP1 backend wraps Pyana STARKs in Groth16:

+ Pyana STARK proof (large, not EVM-friendly).
+ SP1 guest program verifies the STARK inside a RISC-V zkVM.
+ SP1 produces a Groth16 proof (~200K gas on EVM).
+ On-chain verification via Succinct's deployed SP1 Verifier Gateway.

The EVM bridge includes a VK registry with governance, an incremental Merkle tree for deposits ($O(log n)$ insertions), and frontrunning protection. *Status:* The chain crate is implemented but the guest program requires regeneration against the current Plonky3 backend (in development).

== Effect VM: The Sovereign Proof Mechanism <sec-effect-vm>

The Effect VM is the primary proof mechanism for sovereign and hosted cells alike. It is a multi-row AIR circuit that proves arbitrary turns---one STARK per cell touched in a turn, regardless of per-cell effect count. The trace is approximately *151 columns* after Stage 7-$gamma$.0 + $gamma$.2 Phase 1 + sovereign-witness Phase 1, with per-cell public inputs growing to $tilde$73 felts plus per-`Custom`-effect entries. The full instruction set spans state mutation, bilateral capability flow, CapTP, queue, and dispatch:

#figure(
  table(
    columns: (auto, auto),
    align: (left, left),
    table.header([*Effect*], [*Semantics*]),
    [SetField], [Mutate a cell state slot],
    [Transfer], [Move value between cells (conservation-checked)],
    [GrantCapability], [Delegate capability with monotonic narrowing],
    [RevokeCapability], [Remove a capability from a c-list],
    [CreateCell], [Factory-spawned cell creation],
    [DestroyCell], [Provably remove a cell],
    [NoteSpend], [Private note consumption (nullifier production)],
    [NoteCreate], [Private note minting (commitment production)],
    [EmitEvent], [Observable side-effect (logged, not state-altering)],
    [Seal], [Encrypt data under a sealer capability],
    [Introduce], [Three-party capability introduction],
    [Bridge], [Cross-chain attestation emission],
    [Invoke], [CellProgram invocation (calls DSL-generated circuits)],
    [Custom], [Dispatch to arbitrary CellProgram-defined logic],
    [Enqueue], [Push a message to a programmable queue],
    [Dequeue], [Pop a message from a programmable queue (with KZG proof)],
    [ExportSturdyRef], [Register a swiss number for CapTP export],
    [EnlivenRef], [Resolve a sturdy ref into a live reference],
    [DropRef], [Release a remote reference (GC decrement)],
    [ValidateHandoff], [Verify a three-party handoff certificate],
    [BatchGamma], [Fiat-Shamir challenge for KZG batch verification],
    [LookupAssert], [Verify a value exists in a committed lookup table],
    [QueueCommit], [Compute KZG polynomial commitment over queue state],
    [Noop], [Padding row (no state change, satisfies all constraints trivially)],
  ),
  caption: [Effect VM instruction set (24 opcodes). Each maps to a constrained state transition row in the 71-column STARK trace.],
)

Each row of the Effect VM trace encodes one effect's execution:

- Pre-state commitment (Poseidon2 hash of cell state before this effect)
- Effect opcode and operands
- Post-state commitment (Poseidon2 hash of cell state after this effect)
- Conservation accumulator (running sum of value changes)
- Authority witness (proof that the actor held permission for this effect)
- Queue polynomial state (KZG commitment for queue operations)
- Lookup auxiliary columns (LogUp running sums for table lookups)

The VM enforces:
- *State continuity*: Each effect's post-state equals the next effect's pre-state.
- *Conservation*: The final accumulator equals zero (no value created or destroyed).
- *Authority*: Each effect's EffectMask is a subset of the actor's mask.
- *Atomicity*: All effects in a turn succeed or all roll back (proven via a completion flag).
- *Queue correctness*: Enqueue/Dequeue operations maintain valid KZG polynomial commitments.

The `Custom` effect enables dispatch to DSL-generated CellProgram circuits---any application-specific logic compiled through the constraint DSL can be invoked as a single Effect VM step. IVC compression then chains multiple turn proofs into a constant-size attestation covering the cell's entire history.

=== KZG Polynomial Commitments for Queues

Queue state is committed via KZG polynomial commitments over BLS12-381:

$ C_Q = [q(tau)]_1 quad "where" quad q(x) = sum_(i=0)^(n-1) m_i dot L_i (x) $

Each queue message $m_i$ is a coefficient in the queue polynomial. Enqueue appends a term; Dequeue proves evaluation at a specific point and removes it. The KZG commitment enables:

- Constant-size queue state (one group element regardless of queue length).
- Efficient membership proofs ($O(1)$ verification via pairing check).
- Batch verification via the gamma Fiat-Shamir technique (see below).

=== Batch Gamma Fiat-Shamir (KZG Audit Fix)

KZG batch opening verification uses a random linear combination:

$ sum_(i=0)^(k-1) gamma^i dot (C_i - [y_i]_1) = [sum_(i=0)^(k-1) gamma^i dot pi_i]_1 dot [tau - z_i]_2 $

The challenge $gamma$ must be derived via Fiat-Shamir from ALL commitments and claimed evaluations---not from a subset. An audit finding identified that an earlier implementation derived $gamma$ from only the first commitment, enabling a prover to open the remaining commitments at arbitrary values. The fix: $gamma = "BLAKE3"(C_0 || ... || C_(k-1) || y_0 || ... || y_(k-1) || z_0 || ... || z_(k-1))$, binding all batch elements.

The Effect VM handles turns of arbitrary length in a single proof, eliminating the per-effect proof overhead that would otherwise make complex turns (e.g., flash-loan factory spawning, multi-party swaps) prohibitively expensive. *Status:* Implemented and tested; conservation, state-continuity, authority, and queue constraints are operational. The Effect VM is the default proof path for all sovereign cell transitions.

== Formal Verification <sec-formal-verification>

=== Typed Composition Checker

The constraint DSL includes a typed composition checker that statically verifies circuit compositions before proof generation. The checker enforces:

- *Public input compatibility*: Composed circuits must agree on shared public inputs (e.g., the fold chain's `final_root` must type-match the derivation's `initial_state_root`).
- *Width consistency*: Aggregated traces must have compatible column counts, with padding columns zeroed.
- *VK binding*: Each sub-circuit's verification key must be committed in the composition's public inputs.
- *Soundness preservation*: Composition operators cannot weaken soundness below the minimum component security.

The checker runs at compile time (via the DSL proc macros) and rejects invalid compositions before any witness generation occurs.

=== Circuit Catalog

The system maintains a catalog of 30 verified circuit descriptors, each with:

- A formal specification (what the circuit proves, expressed as a logical statement).
- Tested constraint satisfaction (positive AND negative witnesses---the circuit accepts valid traces and rejects adversarial ones).
- Cross-backend consistency (all enabled backends produce the same conclusion for the same witness).
- Security parameter documentation (field size, extension degree, FRI parameters, resulting soundness bound).

=== Cryptographic Guarantees

The proof system provides 11 formally stated cryptographic guarantees:

#figure(
  table(
    columns: (auto, auto),
    align: (left, left),
    table.header([*Guarantee*], [*Mechanism*]),
    [Capability monotonicity], [Fold chain: only fact removal, never addition (Merkle membership under old root)],
    [Conservation], [Effect VM accumulator sums to zero (no value creation/destruction)],
    [State continuity], [Hash chain: each effect's post-state = next effect's pre-state],
    [Authority confinement], [EffectMask subset check per effect (monotonic narrowing)],
    [Non-replayability], [Nullifier uniqueness (deterministic derivation + set non-membership)],
    [Issuer validity], [Issuer membership proof under group-attested root],
    [Derivation soundness], [N-step Datalog derivation with accumulated hash chain],
    [Revocation freshness], [Non-membership proof against revocation set root],
    [IVC integrity], [Root continuity + step-count binding in accumulated hash],
    [Recursive correctness], [FRI folding + Fiat-Shamir replay inside verifier circuit],
    [Cross-backend equivalence], [Same CircuitDescriptor, same logical statement, same conclusion],
  ),
  caption: [Eleven cryptographic guarantees. Each is enforced by algebraic constraints in the STARK trace, not by runtime checks.],
)

=== Trust Assumptions

The proof system operates under 7 explicit trust assumptions:

+ *Collision resistance of Poseidon2 over BabyBear*: The hash function does not admit practical collisions at the working security parameter.
+ *FRI soundness*: Low-degree testing with the configured parameters (50 queries, blowup 4) provides $tilde$100-bit soundness.
+ *Random oracle model*: Fiat-Shamir transcript hashing (BLAKE3) behaves as a random oracle.
+ *Field arithmetic correctness*: BabyBear and BabyBear4 field operations are correctly implemented.
+ *Honest verifier*: The verifier follows the protocol (does not leak challenges prematurely).
+ *Correct constraint generation*: The DSL compiler produces constraints faithful to the logical specification.
+ *Availability of group-attested roots*: Verifiers can obtain a recent attested root (for freshness anchoring).

Any violation of assumptions 1--4 would compromise soundness. Assumptions 5--7 are operational requirements. The system is designed so that assumptions 1--4 are well-studied cryptographic conjectures, not novel assumptions.

== DSL-Only Circuit Architecture

All proof logic is now defined exclusively through the constraint DSL (`circuit/src/dsl/`). The former standalone `_air.rs` files have been deleted---the DSL is the single source of truth, generating circuit implementations for all backends from `CircuitDescriptor` definitions. The production circuit library:

#figure(
  table(
    columns: (auto, auto, auto),
    align: (left, left, left),
    table.header([*Descriptor*], [*Purpose*], [*Backends*]),
    [Poseidon2], [Hash permutation verification], [All 8],
    [MerkleMembership], [4-ary Merkle path proof], [All 8],
    [BodyMembership], [Body fact existence under state root], [All 8],
    [FoldChain], [Monotonic capability attenuation], [All 8],
    [MultiStepDerivation], [N-step Datalog derivation], [All 8],
    [IvcAccumulation], [Fold chain compression (constant-size)], [STARK, Plonky3, Kimchi],
    [NoteSpending], [Private note spending + nullifier], [All 8],
    [BalanceRangeCheck], [Non-negative balance via boolean decomposition], [All 8],
    [NonRevocation], [Credential non-revocation proof], [All 8],
    [NonMembership], [Set non-membership (nullifier freshness)], [All 8],
    [RecursiveVerifier], [STARK-in-STARK recursive verification], [STARK, Plonky3],
    [Presentation], [Full private credential presentation], [All 8],
    [EffectVm], [Multi-effect turn proving (24 opcodes, 71 columns)], [STARK, Plonky3, Kimchi],
    [QueueCommitment], [KZG polynomial commitment for queue state], [STARK, Plonky3],
    [Predicate], [Arbitrary predicate evaluation], [All 8],
    [TemporalPredicate], [Time-bounded predicate proofs], [All 8],
    [ArithmeticPredicate], [Arithmetic range/comparison proofs], [All 8],
    [RelationalPredicate], [Cross-field relational constraints], [All 8],
    [CompoundPredicate], [Boolean composition of predicates], [All 8],
    [Schnorr], [Schnorr signature verification in-circuit], [STARK, Plonky3],
    [NativeSignature], [Ed25519 signature verification], [STARK, Plonky3],
    [SovereignTransition], [Sovereign cell state transition], [STARK, Plonky3, Kimchi],
    [BlockTransition], [Block state transition validity], [STARK, Plonky3],
    [TurnValidity], [Single turn state transition], [STARK, Plonky3],
    [DfaLookup], [DFA transition table lookup proof], [All 8],
    [BatchGammaVerify], [KZG batch opening Fiat-Shamir correctness], [STARK, Plonky3],
    [BlindedMembership], [Ring membership proof (issuer anonymity)], [All 8],
    [NullifierDerivation], [Deterministic nullifier computation], [All 8],
    [CapTPHandoff], [Three-party handoff certificate validation], [STARK, Plonky3],
    [IntentSatisfaction], [Intent constraint satisfaction proof], [All 8],
  ),
  caption: [DSL circuit descriptors (30 total). Each compiles to trace generators and constraint evaluators for the indicated backends via code generation. "All 8" = Rust, AIR, Datalog, Kimchi, Midnight/ZKIR, Plonky3, SP1, STARK.],
)

The Effect VM is the primary sovereign proof mechanism: a single STARK proves an entire turn regardless of effect count. The DSL descriptors above provide the component circuits that the Effect VM dispatches to via `Custom` CellProgram effects.

== Executor Honesty Audit and the Soundness Ledger <sec-honesty-audit>

The system maintains a *living threat ledger* enumerating attacks an malicious executor could attempt, the layer at which each is prevented, and the status of each defense. Defenses live at three layers in order of strength:

+ *AIR (Effect VM)*: the strongest. The prover-side STARK constrains the *transition* itself; a dishonest executor cannot produce a passing proof.
+ *Canonical-message signing*: the actor signs a domain-separated hash (`pyana-turn-v3:`) of the turn body; the executor signs a receipt hash (`executor-receipt-sig-v1:`). Any verifier with the relevant public key can detect deviation.
+ *Verifier-side replay (witnessed-receipt chain)*: a verifier replays the chain, checking each STARK against its PI and (scope-2) re-deriving post-state from inline witness data.

#figure(
  table(
    columns: (auto, auto, auto),
    align: (left, left, left),
    table.header([*Threat*], [*Defense layer*], [*Status*]),
    [T1: Reorder effects within a turn], [AIR (`EFFECTS_HASH_GLOBAL` chain)], [Closed at AIR (single-cell); multi-cell $gamma$.2],
    [T2: Invent effects the actor did not sign], [Signature (effects_hash in v3 body)], [Closed],
    [T3: Skip / omit effects from a signed turn], [AIR (`EFFECTS_HASH_GLOBAL` termination)], [Closed at AIR (single-cell); multi-cell $gamma$.2],
    [T4: Lie about pre/post state hash], [AIR (state hash columns + PI binding)], [Single-cell: pending verification of full pre/post state binding; ACTOR_NONCE row-0 binding landed],
    [T5: Reuse a nonce], [AIR (`ACTOR_NONCE` row-0 boundary)], [*Closed at AIR* via Stage 7 cont §B],
    [T6: Replay a turn from another federation], [Signature (`federation_id` in canonical message) + `KnownFederations` registry], [Closed by Lane D unification (federation_id is a commitment)],
    [T7: Forge a receipt signature], [Signature (`executor-receipt-sig-v1`)], [Closed (standard Ed25519)],
    [T8: Fake `previous_receipt_hash` link], [AIR (`PREVIOUS_RECEIPT_HASH_BASE` in PI, $gamma$.0) + verifier check], [Closed by verifier PI completeness],
    [T9: Skip sovereign-witness verification], [AIR (sovereign-witness Phase 1: `WITNESS_KEY_COMMIT` boundary)], [Phase 1 designed (Lane Hardening); Phase 2 recurses on `transition_proof`],
    [T10: Skip a permission / capability check], [AIR (per-effect Merkle membership)], [In flight: Stage 7 cont P1.C verifies CapTP variants are real Merkle, not tautological],
    [T11: Submit a stale / cached proof for a new turn], [AIR (`TURN_HASH` in PI, $gamma$.0) + verifier match], [Closed by verifier PI completeness],
    [T12: Lie about balance deltas], [AIR (`compute_balance_delta_from_effects` derives delta)], [Single-cell closed; conservation-derivation landed in builder (Stage 8 P2.D)],
    [T13: Cross-cell aliasing (same cell ID across federations)], [Signature (`federation_id` in cell ID derivation)], [Closed for normal cells; `Cell::remote_stub_with_id` escape hatch audited],
    [T14: Skip the AIR proof entirely], [Verifier (rejects receipts without valid proofs)], [Closed by `pyana-verifier` standalone binary],
    [T15: Forge `effects_hash` (prove over E' while signing E)], [AIR (in-trace `EFFECTS_HASH_GLOBAL` termination $arrow.r$ PI; verifier matches PI to signed turn)], [Closed at AIR (single-cell) via Stage 7 cont §B; multi-cell $gamma$.2],
  ),
  caption: [Executor honesty threats and current defense status. The "closed at AIR" / "closed by signature" / "closed by verifier completeness" labels are the soundness rule of thumb: AIR $>$ signature $>$ verifier. Each step down is a soundness reduction; we want as much at AIR level as we can afford.],
)

The cross-cutting open questions: (a) trace-side binding completeness for `{ACTOR_NONCE, EFFECTS_HASH_GLOBAL, TURN_HASH, PRE/POST_STATE, PREVIOUS_RECEIPT_HASH}` (Stage 7 cont addresses two; the other three are followup-pass items); (b) canonical signing message audit (T6, T13)---confirm `federation_id`, `actor_id`, `nonce`, `effects_hash`, `previous_receipt_hash` are all in `canonical_signing_message`; (c) verifier completeness---walk `verifier/src/main.rs` and confirm every PI is checked, not just deserialized; (d) `Cell::remote_stub_with_id` escape hatch (T13 tail)---what prevents arbitrary-id cell minting; (e) sovereign-witness algebraic teeth (T9 Phase 1 design lands the answer).
