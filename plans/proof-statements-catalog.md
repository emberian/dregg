# Proof Statements Catalog

Formal catalog of every proof statement in the pyana circuit system, expressed as logical propositions with composition analysis and gap identification.

---

## 1. Effect VM (EffectVmAir)

### Statement

For all verifiers V who accept proof pi with public inputs PI:

```
There EXISTS a sequence of effects E_1, ..., E_n (each from the 18-type instruction set)
and a sequence of intermediate states S_0, S_1, ..., S_n such that:
  - S_0 commits to PI[OLD_COMMIT] via Poseidon2 tree hash
  - S_n commits to PI[NEW_COMMIT] via Poseidon2 tree hash
  - For each i: S_i -> S_{i+1} is a valid effect transition per effect type
  - The net balance delta equals (PI[NET_DELTA_MAG], PI[NET_DELTA_SIGN])
  - Hash(E_1, ..., E_n) = (PI[EFFECTS_HASH_LO], PI[EFFECTS_HASH_HI])
  - For each Custom effect j: its (vk_hash, proof_commitment) appears at PI[7 + j*8 .. 7 + (j+1)*8]
```

### Public Inputs (7 + 8*custom_count elements)

- PI[0]: `old_commitment` -- Poseidon2 tree hash of initial cell state
- PI[1]: `new_commitment` -- Poseidon2 tree hash of final cell state
- PI[2]: `net_delta_magnitude` -- absolute value of net balance change
- PI[3]: `net_delta_sign` -- 0 = net credit, 1 = net debit
- PI[4]: `effects_hash_lo` -- low element of effects sequence commitment
- PI[5]: `effects_hash_hi` -- high element of effects sequence commitment
- PI[6]: `custom_effect_count` -- number of custom CellProgram dispatches
- PI[7+i*8 .. 7+(i+1)*8]: per custom effect: 4 VK hash elements + 4 proof commitment elements

### Witness (what prover knows but V does not learn)

- The full sequence of effects (types, parameters, amounts, directions)
- All intermediate cell states (balance, nonce, fields, cap_root)
- Auxiliary hash intermediates (Poseidon2 tree nodes)
- The spending_key for NoteSpend effects
- Custom program proofs (bound via commitment)

### Security Properties

- **Soundness:** The state commitment tree hash (Poseidon2 hash_4_to_1 tree) is constrained at EVERY row (constraint group 4), and boundary constraints bind first-row state_before to PI[OLD_COMMIT] and last-row state_after to PI[NEW_COMMIT]. Transition constraints enforce next_row.state_before == this_row.state_after. Forging requires breaking Poseidon2 collision resistance.
- **Zero-knowledge:** The verifier sees only the old/new commitment, net delta, effects hash, and custom VK hashes. Individual effects, balances, field values, and capability roots are hidden.
- **Binding:** Proof is bound to specific state transition via Poseidon2 commitments (collision-resistant).

### Known Gaps (documented in code)

1. **Balance limb range checks NOT in-circuit:** `balance_lo < 2^30` and `balance_hi < 2^34` are enforced by the EXECUTOR, not the STARK. A malicious prover can use field-valid but out-of-range limbs on INTERIOR rows. The boundary commitments catch inconsistency at boundaries but not mid-trace.
2. **Balance underflow NOT proven:** Subtraction wrapping around BabyBear modulus is not caught in-circuit. Defense relies on executor rejecting final balance > initial + credits.
3. **Custom effect constraints are external:** The Effect VM only binds the proof commitment; domain constraints must be verified separately.

### Composition Interface

- **PRODUCES:** `old_commitment`, `new_commitment` (consumed by FullTurnProof verifier)
- **PRODUCES:** `effects_hash` (consumed by turn executor for replay detection)
- **REQUIRES (externally):** Custom proof verification for each `custom_effect_count > 0`
- **BINDING FIELD:** `old_commitment` must equal authorization proof's `state_root` (enforced by FullTurnProof verifier)

---

## 2. Presentation Proof (PresentationAir / RealPresentationProof)

### Statement

```
There EXISTS:
  - An issuer key K in the federation Merkle tree rooted at PI[federation_root]
  - An attenuation chain (fold steps) from initial_root to final_root
  - A Datalog derivation from final_root's fact set that authorizes PI[request_predicate]
such that:
  - K is proven member of federation (Poseidon2 Merkle STARK)
  - Each fold step validly removes facts and/or adds checks
  - The derivation concludes with a fact matching the request predicate
  - presentation_tag = Poseidon2(final_root, randomness, verifier_nonce) [unlinkability]
  - composition_commitment binds all sub-proofs together (124-bit)
  - If verifier_block_height > 0 and not_after_height > 0: not_after_height >= verifier_block_height
```

### Public Inputs

- `federation_root` -- root of trust (Merkle root of issuer keys)
- `request_predicate` -- ActionBinding (4 BabyBear elements, 124-bit)
- `timestamp` -- freshness marker
- `presentation_tag` -- Poseidon2(final_root, randomness, nonce) for unlinkability
- `revealed_facts_commitment` -- WideHash of selectively disclosed facts (4 elements)
- `composition_commitment` -- WideHash binding sub-proofs (4 elements)
- `verifier_nonce` -- challenge-response replay protection
- `verifier_block_height` -- token expiry enforcement

### Witness

- Issuer key hash and full Merkle path in federation tree
- Complete fold chain (removed facts, membership proofs, added checks)
- Derivation witness (rules, substitutions, body fact hashes)
- Blinding factor (for ring membership)
- Presentation randomness (fresh per show)

### Security Properties

- **Soundness:** Issuer membership via Poseidon2 Merkle STARK (collision-resistant). Fold chain validated step-by-step. Derivation rules checked.
- **Zero-knowledge:** Verifier sees only: federation_root, request_predicate, timestamp, blinded tag. Does NOT see: issuer identity (blinded), token chain, derivation rules, intermediate states.
- **Unlinkability:** Same credential shown twice produces different presentation_tags (fresh randomness per show). Blinded issuer leaf prevents issuer correlation.
- **Replay protection:** verifier_nonce binds proof to specific challenge; composition_commitment prevents sub-proof mixing.

### Composition Interface

- **REQUIRES:** FoldProof(s) OR IvcProof for attenuation chain
- **REQUIRES:** DerivationProof for authorization conclusion
- **REQUIRES:** MerkleStarkProof for issuer membership
- **PRODUCES:** Authorization decision (Valid/Invalid) for the request_predicate
- **BINDING:** fold chain's final_root == derivation's state_root; issuer membership root == federation_root; composition_commitment covers all sub-proofs

---

## 3. Multi-Step Derivation (MultiStepDerivationAir)

### Statement

```
There EXISTS a sequence of Datalog rule applications R_1, ..., R_n such that:
  - R_1 starts from state_root (fact set commitment)
  - Each R_i correctly applies a rule: body facts exist, substitution unifies, head is derived
  - R_n derives a fact with predicate == ALLOW_PREDICATE (0xA110)
  - The accumulated hash chains all derived facts: H_n = Poseidon2(H_{n-1} || derived_hash_n)
  - policy_root = hash(rule_1_structure || ... || rule_n_structure)
```

### Public Inputs (6 elements)

- PI[0]: `initial_state_root` -- commitment to the fact database
- PI[1]: `request_hash` -- hash of the authorization request
- PI[2]: `conclusion` -- 1 (ALLOW) or 0 (DENY)
- PI[3]: `num_steps` -- number of derivation steps
- PI[4]: `final_accumulated_hash` -- commitment to derivation trace
- PI[5]: `policy_root` -- hash of all rules used (binds to specific policy)

### Witness

- Per step: CircuitRule (structure, head/body patterns), body_fact_hashes, substitution, derived predicate/terms
- not_after_height, org_id_hash, budget_remaining (expiry/scoping caveats)

### Security Properties

- **Soundness:** Each derivation step checks: head predicate matches, terms resolve correctly via substitution, body fact hashes are provided. The accumulated hash prevents step omission/reordering.
- **Gap:** Body fact hashes are prover-supplied but NOT proven to exist in the Merkle tree within this circuit alone. This gap is closed by BodyMembershipProof (separate composition).
- **Binding:** policy_root commits to the exact rules used, preventing rule substitution.

### Composition Interface

- **REQUIRES:** Body fact existence (proven by BodyMembershipProof or ValidatedIvcProof)
- **PRODUCES:** `conclusion` (ALLOW/DENY), `accumulated_hash`, `state_root`
- **CONSUMED BY:** PresentationProof (derivation's state_root == fold chain's final_root)
- **CONSUMED BY:** FullTurnProof (authorization binding)

---

## 4. Body Membership Proof (BodyMembershipProof)

### Statement

```
For each body fact hash H_i used in the derivation:
  H_i is a leaf in the Poseidon2 Merkle tree with root == state_root
AND the derivation STARK is valid (rules applied correctly, conclusion ALLOW/DENY)
```

### Public Inputs

- Per membership STARK: `[leaf_hash, state_root]`
- Derivation STARK: standard 6-element PI

### Security Properties

- **Soundness:** Each body fact's membership is proven via a separate Poseidon2 Merkle STARK. The verifier cross-checks that all membership proofs share the same state_root as the derivation proof's PI[0].
- **Closes the gap:** Without this, a malicious prover could claim arbitrary body_hash values in the derivation trace without proving they exist in the committed tree.

### Composition Interface

- **REQUIRES:** DerivationProof (shares state_root)
- **REQUIRES:** Per-fact Merkle membership STARKs
- **BINDING:** derivation PI[0] == each membership proof PI[1] == proof.state_root

---

## 5. IVC (Incrementally Verifiable Computation)

### Statement

```
There EXISTS a sequence of fold steps (root_0, root_1, ..., root_n) such that:
  - root_0 == PI[initial_root]
  - root_n == PI[final_root]
  - n == PI[step_count]
  - accumulated_hash = Poseidon2_chain(root_0, root_1, ..., root_n) == PI[accumulated_hash]
  - Each fold step's constraints are satisfied
  - n <= MAX_FOLD_DEPTH (16)
```

### Public Inputs (4 elements)

- PI[0]: `initial_root` -- root before any attenuations
- PI[1]: `final_root` -- root after all attenuations
- PI[2]: `step_count` -- number of fold steps
- PI[3]: `accumulated_hash` -- Poseidon2 hash chain commitment

### Witness

- Per step: FoldDelta (old_root, new_root, removed_facts, membership proofs, added checks)

### Security Properties

- **Soundness (STARK path):** StateTransitionAir constrains new_hash == extend_accumulated_hash(old_hash, new_root, step) per row. Boundary constraints bind first/last rows to public inputs. Step reordering requires Poseidon2 preimage.
- **Constant-size:** Proof size is O(log(n)) regardless of chain length (modeled as 128 KiB).
- **Depth cap:** MAX_FOLD_DEPTH = 16 prevents unbounded proving and degradation.

### Gap: Fold Validity

The basic IVC proves only the HASH CHAIN arithmetic. It does NOT prove that each fold step's removal was valid (fact existed in tree). This gap is closed by ValidatedIvcProof which adds per-step Merkle membership STARKs.

### Composition Interface

- **CONSUMED BY:** PresentationProof (IVC final_root == derivation state_root)
- **PRODUCES:** initial_root, final_root, accumulated_hash
- **BINDING:** Wide accumulated hash (124-bit) prevents birthday attacks

---

## 6. Fold AIR (FoldAir / DSL fold)

### Statement

```
There EXISTS a set of removed facts {F_1, ..., F_k} and added checks C such that:
  - Each F_i's hash == hash_fact(predicate_i, terms_i) [computed in-circuit]
  - Each F_i existed in the Merkle tree at old_root (membership verified)
  - root_transition_hash = Poseidon2(old_root || new_root || fact_hashes || checks_commitment)
  - total_removal_count + total_check_count >= 1 (non-empty delta)
```

### Public Inputs (6 elements)

- PI[0]: `old_root` -- state root before this fold
- PI[1]: `new_root` -- state root after this fold
- PI[2]: `total_removal_count` -- number of facts removed
- PI[3]: `total_check_count` -- number of checks added
- PI[4]: `root_transition_hash` -- binding commitment
- PI[5]: `checks_commitment_narrow` -- commitment to added checks

### Security Properties

- **Soundness:** fact_hash_correct constraint computes hash_fact in-circuit (Poseidon2). membership_root matches old_root for removal rows. root_transition_hash binds the entire delta.
- **Non-empty:** delta_nonempty constraint ensures at least one removal or check.

### Composition Interface

- **CONSUMED BY:** IVC (fold steps accumulate into hash chain)
- **CONSUMED BY:** PresentationProof (sequential fold proofs in non-IVC path)
- **BINDING:** old_root == previous step's new_root (chain continuity)

---

## 7. Non-Membership Proof (AccumulatorNonRevocationAir)

### Statement

```
For elements {h_1, ..., h_k}:
  NONE of h_i appears in the polynomial accumulator set S, where:
  - accumulator = product((alpha - s_j) for s_j in S) over BabyBear^4
  - For each h_i: quotient_i * (alpha - h_i) + remainder_i == accumulator
  - remainder_i != 0 (proves h_i not in S)
```

### Public Inputs (9 elements)

- PI[0..4]: `accumulator` -- ExtElem (4 BabyBear) polynomial accumulator value
- PI[4..8]: `alpha` -- ExtElem challenge point
- PI[8]: `num_elements` -- count of elements being checked

### Witness

- Per element: ancestor_hash, quotient (ExtElem), remainder (ExtElem)
- The full set S (for witness generation only)

### Security Properties

- **Soundness:** If h_i IS in S, then (alpha - h_i) divides the accumulator polynomial evenly, making remainder = 0. The constraint requires remainder != 0 for non-membership.
- **Cross-set binding:** SetIdentifier's domain_sep is mixed into alpha derivation, preventing proof replay across different sets.
- **Extension field:** BabyBear^4 provides 124-bit security for the accumulator.

### Composition Interface

- **CONSUMED BY:** AugmentedDerivation (authorization + non-revocation)
- **CONSUMED BY:** FullTurnProof (non-revocation component)
- **BINDING:** accumulator must match federation's published revocation state

---

## 8. Note Spending (NoteSpendingAir)

### Statement

```
There EXISTS spending_key[0..8] (248-bit), owner, value, asset_type, creation_nonce, randomness such that:
  - commitment = Poseidon2(owner, value, asset_type, creation_nonce, randomness)
  - PI[NULLIFIER] = Poseidon2(commitment, spending_key[0..8], creation_nonce)
  - commitment is a leaf in Poseidon2 Merkle tree at PI[MERKLE_ROOT]
  - PI[VALUE] == value (bound by boundary constraint)
  - PI[ASSET_TYPE] == asset_type (bound by boundary constraint)
```

### Public Inputs (4 elements)

- PI[0]: `nullifier` -- unique spend identifier (for double-spend detection)
- PI[1]: `merkle_root` -- root of the note commitment tree
- PI[2]: `value` -- note value (prevents inflation)
- PI[3]: `asset_type` -- note asset type (prevents substitution)

### Witness

- spending_key (8 BabyBear limbs = 248 bits)
- owner, value, asset_type, creation_nonce, randomness
- Merkle path (siblings + positions)

### Security Properties

- **Soundness:** Commitment and nullifier are constrained via full Poseidon2 hash computation in-circuit. Merkle path verified level-by-level with hash_4_to_1.
- **Zero-knowledge:** Verifier learns nullifier, merkle_root, value, asset_type. Does NOT learn: spending_key, owner identity.
- **Key security:** 8 BabyBear limbs = 248-bit key space (~2^248 brute-force).
- **Value binding:** Boundary constraints bind value and asset_type to public inputs, preventing inflation attacks.

### Composition Interface

- **CONSUMED BY:** Effect VM (NoteSpend effect references the nullifier)
- **BINDING:** nullifier in proof must match the Effect VM's param[0] for NoteSpend rows

---

## 9. Committed Threshold (CommittedThresholdAir)

### Statement

```
There EXISTS private_value, threshold, blinding such that:
  - private_value >= threshold (proven via 30-bit decomposition with high bit = 0)
  - Poseidon2(threshold, blinding) == PI[threshold_commitment]
  - The value is bound to token state via PI[fact_commitment]
```

### Public Inputs (2 elements)

- PI[0]: `threshold_commitment` -- Poseidon2(threshold, blinding)
- PI[1]: `fact_commitment` -- Poseidon2(fact_hash, state_root)

### Witness

- private_value, threshold, blinding
- 30-bit decomposition of (value - threshold)

### Security Properties

- **Soundness:** Bit decomposition + high-bit-zero proves diff fits in 29 bits (< p/2), i.e., non-negative. Poseidon2 hash binding prevents threshold forgery.
- **Privacy:** Third parties see only two commitments. Neither the value nor the threshold is revealed.
- **SOUNDNESS FIX:** Uses 30 bits (not 31) because BabyBear p/2 < 2^30. Previous 31-bit version was unsound.

### Composition Interface

- **CONSUMED BY:** Derivation system (as a GTE predicate check)
- **BINDING:** fact_commitment ties to a specific state via Poseidon2

---

## 10. STARK Verifier (stark.rs)

### Security Guarantees

The STARK system provides:

1. **Reed-Solomon proximity:** FRI proves that the committed polynomials are close to low-degree (constraint_degree)
2. **Boundary enforcement:** Verifier independently checks trace[row][col] == expected_value at declared boundaries
3. **Transition constraint quotient:** (constraint_polynomial / Z_T(x)) must be low-degree, proving constraints hold on ALL trace rows
4. **Fiat-Shamir:** Non-interactive via BLAKE3 transcript hashing
5. **Extension field challenges:** BabyBear^4 (124-bit) alpha for constraint composition prevents cancellation attacks

### Configuration

- Blowup factor: 8 (Reed-Solomon expansion)
- FRI queries: 28 (for ~112-bit security)
- Merkle commitments: BLAKE3

### Soundness Level

- Target: ~112 bits (from FRI query count * log(blowup))
- Extension field: 124-bit alpha prevents constraint-combination forgery
- Classification: `ProofTier::Experimental` (production uses Plonky3 backend)

---

## 11. Full Turn Proof (FullTurnProof / ComposedProof)

### Statement

```
ALL of the following hold simultaneously:
  1. State transition S_old -> S_new is valid (Effect VM proof)
  2. The actor was authorized to perform this action (Derivation proof)
  3. The capability used exists in the c-list (Membership proof) [if applicable]
  4. Value is conserved: sum(inputs) == sum(outputs) [if applicable]
  5. The token/capability has not been revoked (Non-revocation proof) [if applicable]
  6. Cross-proof bindings are consistent (shared roots match)
```

### Public Inputs (merged from sub-proofs)

- Effect VM PIs: old_commitment, new_commitment, net_delta, effects_hash
- Authorization PIs: state_root, derived_hash, not_after, org_id, budget
- Membership PIs: leaf_hash, merkle_root
- Non-revocation PIs: revocation_root

### Cross-Proof PI Bindings (ENFORCED by verifier)

- `authorization.state_root == membership.merkle_root` (same fact tree)
- `authorization.state_root == effect_vm.old_commitment` (authorization covers this specific cell)
- `effect_vm.net_delta == conservation.expected_net_delta` (value balance)
- Sub-proof hashes are embedded in the composition trace

### Security Properties

- **Soundness:** Each sub-proof is individually verified via its own StarkAir. Cross-proof bindings are checked at the verifier level (not in-circuit).
- **Completeness:** A valid turn with proper witnesses always produces a verifiable proof.
- **Replay prevention:** turn_hash binds proof to specific turn content.

### Composition Interface

- **This is the TOP-LEVEL proof** -- consumed by bridge/light-client/peer verifiers
- **REQUIRES:** Effect VM proof + Authorization proof (minimum)
- **OPTIONALLY REQUIRES:** Membership proof, Conservation proof, Non-revocation proof

---

## 12. DSL Lookup Constraints (circuit.rs)

### Statement

```
For a Lookup constraint with table T and query columns [c_0, ..., c_k]:
  The tuple (trace[row][c_0], ..., trace[row][c_k]) EXISTS in table T.entries
```

### Security Properties

- **In constraint checker:** Verified by linear search (membership test). Returns 0 if found, 1 if not.
- **In production STARK:** Would be compiled to LogUp (logarithmic derivative) or permutation argument. Currently evaluated concretely on trace values.
- **Use cases:** DFA routing tables, range check tables (2^16 for balance limbs -- TODO), bytecode dispatch tables.

---

## Composition Dependency Graph

```
FullTurnProof (TOP LEVEL -- verifier's single entry point)
  |
  +-- EffectVmProof (state transition: S_old -> S_new)
  |     Binding: PI[OLD_COMMIT], PI[NEW_COMMIT]
  |
  +-- AuthorizationProof (Datalog evaluation -> ALLOW)
  |   |   Binding: PI[state_root] == EffectVm.PI[OLD_COMMIT]
  |   |
  |   +-- BodyMembershipProof (each body fact exists in tree)
  |   |     Binding: leaf_hash for each fact, root == state_root
  |   |
  |   +-- PolicyRoot binding (rules are the declared policy)
  |
  +-- MembershipProof (capability in c-list)
  |     Binding: PI[merkle_root] == Authorization.PI[state_root]
  |
  +-- ConservationProof (value balance)
  |     Binding: EffectVm.PI[NET_DELTA] matches expected
  |
  +-- NonRevocationProof (token not revoked)
        Binding: accumulator matches federation state


PresentationProof (AUTHORIZATION -- separate from turns)
  |
  +-- FoldChain / IvcProof (attenuation chain: initial_root -> final_root)
  |   |   Binding: step-to-step root continuity; IVC accumulated_hash
  |   |
  |   +-- [ValidatedIvc]: per-step Merkle membership (fact existed at old_root)
  |
  +-- DerivationProof (final_root's facts -> ALLOW for request)
  |     Binding: derivation.state_root == fold chain's final_root
  |
  +-- IssuerMembershipProof (issuer key in federation tree)
  |     Binding: merkle_root == federation_root
  |
  +-- [optional] TemporalPredicateProof (attribute >= threshold for N blocks)
        Binding: final_state_root == presentation state_root


NoteSpendingProof (UTXO -- attached to Effect VM)
  |
  Binding: nullifier appears as Effect VM NoteSpend param
  Binding: value/asset_type match what Effect VM credits
```

---

## Gap Analysis: Assumed vs. Enforced Bindings

### ENFORCED (cryptographically):

| Binding | Where Enforced | Mechanism |
|---------|---------------|-----------|
| Effect VM old/new commitment | Boundary constraints | STARK verifier checks trace[0][STATE_COMMIT] == PI[OLD_COMMIT] |
| State commitment = hash of state columns | Per-row constraint (group 4) | Poseidon2 tree hash computed in-circuit |
| Fold fact_hash = hash_fact(pred, terms) | FoldAir constraint | Poseidon2 computed in-circuit |
| IVC hash chain | StateTransitionAir boundary + per-row | extend_accumulated_hash at each row |
| Issuer in federation | Poseidon2 Merkle STARK | Full Merkle path verified in-circuit |
| Note spending key knowledge | NoteSpendingAir | Nullifier = hash(commitment, key, nonce) in-circuit |
| Presentation unlinkability | Tag computation | presentation_tag = Poseidon2(final_root, randomness, nonce) |
| composition_commitment | Appended as PI to issuer STARK | Sub-proofs cannot be mixed across presentations |

### ASSUMED (executor-enforced, not in-circuit):

| Binding | Risk | Impact if Violated |
|---------|------|-------------------|
| Balance limb range (lo < 2^30, hi < 2^34) | Malicious prover uses out-of-range interior limbs | Could create phantom value on interior rows; boundaries catch final state |
| Balance underflow (amount <= balance) | Wrap-around in BabyBear modular arithmetic | Could credit unlimited value; boundaries + executor catch at final state |
| NoteSpend nullifier uniqueness | Double-spend | Executor maintains nullifier set; not enforced by STARK |
| Obligation existence for FulfillObligation | Fulfilling non-existent obligation | Executor tracks obligation set |
| Custom effect external proof validity | Custom program's proof_commitment is NOT verified by Effect VM | Executor or separate verifier must check custom proofs |

### CROSS-PROOF BINDINGS (enforced at verifier level, not in-circuit):

| Binding | Enforced By | Gap Risk |
|---------|-------------|----------|
| auth.state_root == membership.merkle_root | FullTurnProof verifier code | If verifier skips this check: proof splicing attack |
| auth.state_root == effect_vm.old_commitment | FullTurnProof verifier code | If verifier skips: authorize for cell A, mutate cell B |
| derivation.state_root == fold.final_root | PresentationProof.verify() | If skipped: attach unrelated derivation to fold chain |
| Body fact hashes exist in tree | BodyMembershipProof composition | Without composition: prover fabricates body facts |
| IVC fold validity | ValidatedIvcProof | Basic IVC only proves hash chain, not fold correctness |

### POTENTIAL ATTACKS if cross-proof binding is not checked:

1. **Proof splicing (FullTurnProof):** Take a valid auth proof for cell A and a valid Effect VM proof for cell B. Without the `auth.state_root == effect_vm.old_commitment` check, a verifier would accept unauthorized mutation of cell B.

2. **Body fact fabrication (Derivation):** Without BodyMembershipProof, the derivation prover supplies arbitrary body_hash values. The derivation STARK only checks that rules are applied correctly TO those hashes -- it does not verify the hashes correspond to actual facts.

3. **Fold chain bypass (IVC):** Basic IVC proves `initial_root -> final_root` via hash chain but does NOT prove each intermediate fold was valid. An attacker could claim any final_root by fabricating intermediate roots. ValidatedIvcProof closes this by requiring per-step Merkle membership proofs.

4. **Cross-set replay (Non-membership):** Without set_id domain separation in alpha derivation, a non-revocation proof for set A could be replayed against set B. The SetIdentifier.domain_sep prevents this.

5. **Stale revocation state:** The non-revocation proof proves non-membership against a SPECIFIC accumulator value. If the accumulator has since been updated (new revocations added), the proof is stale. The verifier must check the accumulator matches the CURRENT federation state.

---

## Summary of Proof Tiers

| Circuit | In-Circuit Soundness | Relies on Executor | Composition Required |
|---------|---------------------|-------------------|---------------------|
| Effect VM | State commitment tree hash | Balance range + underflow | Custom proofs external |
| Presentation | Issuer membership, fold hash, derivation | None (self-contained) | Fold + Derivation + Membership |
| Multi-Step Derivation | Rule application, hash chain | None | Body Membership for fact existence |
| Body Membership | Merkle paths + derivation STARK | None | Shares state_root with derivation |
| IVC (basic) | Hash chain arithmetic | Fold validity assumed | Does NOT prove folds valid |
| IVC (validated) | Hash chain + per-step Merkle | None (self-contained) | Closes fold validity gap |
| Fold AIR | Fact hash, membership, transition | None | Individual fold steps |
| Non-Membership | Polynomial accumulator algebra | Accumulator freshness | Accumulator from federation |
| Note Spending | Commitment + nullifier + Merkle | Nullifier uniqueness tracking | Consumed by Effect VM |
| Committed Threshold | Range proof + hash binding | None | Consumed by derivation GTE |
| Full Turn Proof | Each sub-STARK individually | Cross-proof binding at verifier | ALL sub-proofs composed |

---

## 13. Poseidon2 AIR (Poseidon2Air)

### Statement

```
There EXISTS an input state S[0..7] and output state O[0..7] such that:
  - O == Poseidon2_permute(S)
  - S matches PI[0..7]
  - O matches PI[8..15]
```

### Public Inputs (16 elements)

- PI[0..7]: `input_state` -- the 8-element Poseidon2 input
- PI[8..15]: `output_state` -- the 8-element Poseidon2 output (= permute(input))

### Witness

- None beyond the trace itself (this is a deterministic computation proof)
- The AIR recomputes the full permutation inside the constraint evaluator

### Security Properties

- **Soundness:** The constraint evaluator computes the REAL Poseidon2 permutation and checks `claimed_output == computed_output`. Any deviation produces a non-zero constraint caught by FRI.
- **Degree:** 7 (from Poseidon2 S-box exponentiation)
- **Use case:** Sub-circuit for validating hash computations in larger proofs

### Composition Interface

- **CONSUMED BY:** Any circuit needing verified Poseidon2 hash computation
- **PRODUCES:** Binding between input and output via the permutation relation

---

## 14. Merkle Poseidon2 AIR (MerklePoseidon2Air / MerklePoseidon2StarkAir)

### Statement

```
There EXISTS a leaf_hash and a Merkle path (siblings, positions) such that:
  - Iterating hash_4_to_1 from leaf to root using the path yields root
  - Each level's parent is computed as Poseidon2 hash of 4 children (including current)
  - PI[0] == leaf_hash
  - PI[1] == root
```

### Public Inputs (2 elements)

- PI[0]: `leaf_hash` -- the leaf value being proven as member
- PI[1]: `root` -- the Merkle tree root

### Witness

- Per level: position (0-3) within the 4-ary node, 3 sibling hashes
- The full Merkle path from leaf to root

### Security Properties

- **Soundness:** Each level's hash is computed in-circuit via Poseidon2 `hash_4_to_1`. Position validity is constrained via degree-4 polynomial `pos*(pos-1)*(pos-2)*(pos-3)==0`. Hash binding uses Lagrange interpolation to select correct child ordering.
- **Collision resistance:** Forging membership requires finding a Poseidon2 collision (~2^124 work)
- **Two variants:** Round-by-round AIR (depth*TOTAL_ROUNDS rows, verifies every round) and simplified AIR (1 row per level, computes full hash in constraint)

### Composition Interface

- **CONSUMED BY:** PresentationProof (issuer membership), BodyMembershipProof (fact existence), NoteSpendingProof (UTXO set)
- **BINDING:** leaf_hash at row 0, root at last row

---

## 15. Blinded Merkle Poseidon2 AIR (BlindedMerklePoseidon2StarkAir)

### Statement

```
There EXISTS a leaf_hash, blinding_factor, and Merkle path such that:
  - leaf_hash is a member of the tree with root PI[1]
  - blinded_leaf = hash_2_to_1(leaf_hash, blinding_factor) == PI[0]
  - The leaf_hash is NOT revealed (zero-knowledge ring membership)
```

### Public Inputs (2 elements)

- PI[0]: `blinded_leaf` -- hash_2_to_1(leaf_hash, blinding_factor)
- PI[1]: `root` -- Merkle tree root (e.g., federation root)

### Witness

- leaf_hash (the actual issuer key hash -- PRIVATE)
- blinding_factor (fresh random per presentation)
- Merkle path (siblings + positions)

### Security Properties

- **Soundness:** Same as MerklePoseidon2StarkAir (Poseidon2 hash binding + position validity), plus blinding constraint: `col[7] == hash_2_to_1(col[0], col[6])` verified on every row.
- **Zero-knowledge:** Row 0 col 0 (leaf_hash) is NOT bound to any public input. Only the blinded version appears publicly.
- **Unlinkability:** Same issuer with different blinding_factor produces different PI[0] values. Verifier cannot correlate presentations of the same credential.

### Composition Interface

- **CONSUMED BY:** PresentationProof (unlinkable issuer membership in federation)
- **BINDING:** blinded_leaf at row 0 col 7, root at last row col 5

---

## 16. Garbled Evaluation AIR (GarbledEvaluationAir)

### Statement

```
There EXISTS a sequence of gate evaluations G_1, ..., G_n such that:
  - For each G_i: output_label == table_entry - Poseidon2(left_label || right_label || gate_index)
  - circuit_commitment == PI[0..3] (124-bit WideHash binding to specific garbled circuit)
  - output_label_hash == PI[4..7] (124-bit WideHash of final output)
```

### Public Inputs (8 elements)

- PI[0..3]: `circuit_commitment` -- WideHash of all garbled tables (binds to specific circuit)
- PI[4..7]: `output_label_hash` -- WideHash of the evaluation output label

### Witness

- Per gate: left_label[8], right_label[8], gate_index, hash_output[8], table_entry[8], output_label[8]
- The garbled tables themselves (bound via circuit_commitment)
- The evaluator's input labels (obtained via oblivious transfer)

### Security Properties

- **Soundness:** Decryption correctness constraint (`output = table_entry - hash_output`) is checked per row. Circuit commitment binding ensures the proof covers the correct garbled circuit. The verifier checks output_label_hash against known true/false label hashes.
- **Privacy (from garbling):** The verifier sees only the circuit commitment and output hash. Input labels (which encode private input bits) are never revealed.
- **Binding:** 124-bit WideHash prevents circuit/output substitution

### Composition Interface

- **CONSUMED BY:** Gallery Vickrey auction (proves correct bid comparison evaluation)
- **CONSUMED BY:** Any two-party computation requiring verifiable garbled circuit evaluation
- **REQUIRES:** Oblivious Transfer for input label delivery (external to circuit)

---

## 17. Temporal Predicate AIR (TemporalPredicateDsl / TemporalPredicateAir)

### Statement

```
There EXISTS a sequence of values v_0, ..., v_{n-1} such that:
  - For each step i: predicate(v_i, threshold) holds
    (e.g., GTE: v_i >= threshold, proven via 30-bit decomposition with high bit = 0)
  - The accumulator increments from 1 to n (no steps skipped)
  - n == PI[num_steps] (padded trace length)
```

### Public Inputs (1 element)

- PI[0]: `num_steps` -- padded trace length (power of 2)

### Witness

- Per step: value, threshold, diff = value - threshold (or inverse depending on predicate type)
- 30-bit decomposition of diff (proves non-negative)
- State roots at each step (binding to receipt/IVC chain, stored in proof metadata)

### Security Properties

- **Soundness:** Per-row constraints enforce: diff == value - threshold (C1), bit decomposition sums to diff (C3), high bit is zero proving diff < 2^30 < p/2 (C4). Transition constraints enforce accumulator continuity (T1, T2). Boundary constraints bind first-row accumulator = 1 and last-row accumulator = num_steps.
- **Duration binding:** The verifier checks `proof.num_steps` against the temporal requirement's `min_duration_steps`. A 3-step proof cannot verify as a 10-step proof (boundary constraint mismatch).
- **State binding:** initial_state_root and final_state_root in the proof metadata bind to the receipt/IVC chain (checked at verification time, not in-circuit).

### Composition Interface

- **CONSUMED BY:** PresentationProof (temporal attribute predicate)
- **CONSUMED BY:** Intent system (TemporalPredicateRequirement satisfaction)
- **BINDING:** initial/final state roots tie to specific chain of state transitions

---

## 18. Quantified Absence -- Chunk AIR (ChunkAbsenceAir)

### Statement (Approach A: IVC-chained chunks)

```
For each element e_i in a chunk of set S:
  - predicate(e_i) == 0 (the predicate does NOT hold for this element)
  - element_hash == Poseidon2(e_i, domain_sep)
  - The chunk accumulator chains correctly from initial_acc to final_acc
```

### Public Inputs (5 elements)

- PI[0]: `chunk_index` -- position in the IVC chain
- PI[1]: `chunk_size` -- number of real elements in this chunk
- PI[2]: `initial_acc` -- running accumulator before this chunk
- PI[3]: `final_acc` -- running accumulator after this chunk
- PI[4]: `predicate_id` -- hash identifying which predicate is being tested

### Witness

- Per element: the element value, predicate evaluation result (must be 0), element hash
- Running accumulator hash values

### Security Properties

- **Soundness:** C1 constrains `predicate_result == 0` (absence). C2 constrains correct hash computation. Boundary constraint binds last-row accumulator to `final_acc`. Chain continuity (chunk[i].final_acc == chunk[i+1].initial_acc) is verified externally.
- **Set binding:** The IVC hash chain commits to all processed elements. `set_commitment` is independently recomputable.
- **Composition:** Multiple chunk proofs are chained via accumulator continuity to cover arbitrary set sizes.

### Composition Interface

- **CONSUMED BY:** QuantifiedAbsenceIvcProof (chains multiple chunks)
- **BINDING:** initial_acc/final_acc chain between chunks; predicate_id binds to specific property

---

## 19. Quantified Absence -- Quotient Accumulator AIR (QuotientAccumulatorAir)

### Statement (Approach B: polynomial accumulator)

```
Given accumulator Acc_all = product(alpha - h_i) for all h_i in S:
  - Acc_satisfying == ONE (no elements satisfy the predicate)
  - For each element h_i: w_i * (alpha - h_i) + v_i == Acc_all
    (polynomial division identity -- proves h_i contributes to Acc_all)
```

### Public Inputs (9 elements)

- PI[0..3]: `Acc_all` -- ExtElem (BabyBear^4) polynomial accumulator over full set
- PI[4..7]: `alpha` -- ExtElem challenge point (derived from set + predicate binding)
- PI[8]: `num_elements` -- count of elements

### Witness

- Per element: element hash (ExtElem), quotient w (ExtElem), remainder v (ExtElem), diff (alpha - elem), product (w * diff), sum (product + v)

### Security Properties

- **Soundness:** Constraints enforce: diff == alpha - elem (C1), prod == w * diff (C2, degree 2), sum == prod + v (C3). Boundary constraints enforce sum == Acc_all for each active row. If Acc_satisfying != ONE, the proof cannot be generated (returns None).
- **Extension field security:** BabyBear^4 provides 124-bit security for the accumulator.
- **Predicate binding:** Alpha is derived from element hashes + predicate_id via domain-separated Poseidon2, preventing cross-predicate replay.

### Composition Interface

- **CONSUMED BY:** Authorization checks requiring "for all X in S, property P does NOT hold"
- **USE CASE:** Proving no element in a set satisfies a revocation condition, a fraud condition, etc.

---

## 20. Accumulator Non-Revocation AIR (AccumulatorNonRevocationAir)

### Statement

```
For each ancestor hash h_i (up to MAX_ANCESTORS=8) in a capability's derivation path:
  - w_i * (alpha - h_i) + v_i == Acc (polynomial division identity)
  - v_i != 0 (proves h_i is NOT a root of the accumulator polynomial)
  Therefore: NONE of the ancestor hashes appear in the revocation set.
```

### Public Inputs (9 elements)

- PI[0..3]: `Acc` -- ExtElem (BabyBear^4) polynomial accumulator of the revocation set
- PI[4..7]: `alpha` -- ExtElem challenge point
- PI[8]: `num_ancestors` -- number of active ancestor rows

### Witness

- Per ancestor: ancestor_hash (BabyBear, embedded in ExtElem), quotient w_i (ExtElem), remainder v_i (ExtElem), v_inverse (ExtElem)
- The full revocation set (for witness generation only)

### Security Properties

- **Soundness:** If h_i IS in the revocation set, then (alpha - h_i) divides Acc evenly, making v_i = 0. The constraint `check == v * v_inv == ONE` forces v_i != 0 (boundary constraint). Extension-field multiplication is degree 2.
- **O(1) verification:** Proof size is constant (8 rows, 32 columns) regardless of revocation set size. Compare: sorted-Merkle approach requires 72 rows.
- **Cross-set binding:** Alpha is derived via domain-separated hash of the revocation set, preventing proof replay across different epochs.

### Composition Interface

- **CONSUMED BY:** PresentationProof, FullTurnProof (non-revocation component)
- **BINDING:** Accumulator value must match federation's published revocation state at the current epoch

---

## 21. Poseidon STARK Verifier Circuit (PoseidonStarkVerifierCircuit)

### Statement

```
There EXISTS a valid PoseidonStarkProof P such that:
  - P.trace_commitment matches PI_kimchi[0]
  - P.constraint_commitment matches PI_kimchi[1]
  - For each query: Merkle path verification succeeds (via Poseidon node hashing)
  - For each query: BabyBear constraint evaluation matches the committed quotient polynomial
  - FRI folding checks pass for all layers
  I.e., the STARK proof P is VALID, proven inside a Kimchi (Pickles) circuit.
```

### Public Inputs (Kimchi level: 2 Fp elements)

- PI[0]: `trace_commitment` -- Poseidon-based Merkle root of the STARK trace
- PI[1]: `constraint_commitment` -- Poseidon-based Merkle root of constraint polynomial

### Witness (Kimchi level)

- The full PoseidonStarkProof (query values, Merkle paths, FRI layers)
- Intermediate Poseidon hash states (for each gadget)
- BabyBear arithmetic intermediate values (quotients, remainders for modular reduction)

### Security Properties

- **Recursive soundness:** The Kimchi proof attests that the STARK verification algorithm accepted. If the STARK proof is invalid, the Kimchi witness will not satisfy the circuit gates.
- **Compression:** ~48 KiB STARK proof is compressed to ~5 KiB Kimchi proof (IPA commitment).
- **BabyBear-in-Vesta:** BabyBear modular multiplication is implemented with 3 Generic gates (mul + reduce + range_check) -- 2x cheaper than ForeignFieldMul gates.
- **Gate count:** 1 query = ~225 rows, 80 queries = ~18,500 rows (fits in Kimchi domain 2^15).
- **Feature-gated:** Requires `feature = "mina"` (Kimchi/Pasta/Pickles dependencies)

### Composition Interface

- **CONSUMED BY:** Mina bridge (STARK-in-Pickles wrapping for L1 verification)
- **REQUIRES:** A valid PoseidonStarkProof (any AIR using Poseidon-committed STARK)
- **PRODUCES:** A Kimchi proof verifiable by Pickles/Mina infrastructure

---

## 22. IVC State Transition AIR (StateTransitionAir / IvcAir)

### Statement

```
There EXISTS a sequence of fold steps (delta_1, ..., delta_n) such that:
  - initial_root -> delta_1.new_root -> ... -> delta_n.new_root == final_root
  - For each step i: new_hash_i == Poseidon2(old_hash_{i-1} || new_root_i || step_count_i)
  - accumulated_hash_n == PI[3]
  - Each fold step's constraints are individually satisfied (fold_valid == 1)
  - step_count increments by 1 each row
  - n == PI[2]
```

### Public Inputs (4 elements)

- PI[0]: `initial_root` -- root before any attenuations
- PI[1]: `final_root` -- root after all attenuations
- PI[2]: `step_count` -- number of fold steps in the chain
- PI[3]: `accumulated_hash` -- Poseidon2 hash chain commitment

### Witness

- Per step: FoldDelta containing the fold witness (removals, checks, root transition)
- Intermediate accumulated hash values
- Per-step fold validity (verified via FoldAir constraint checking)

### Security Properties

- **Soundness (STARK path):** Boundary constraints bind first-row old_root to PI[initial_root] and last-row new_root to PI[final_root]. Per-row constraints enforce `new_hash == extend_accumulated_hash(old_hash, new_root, step)`. Root continuity: row[i].new_root == row[i+1].old_root (transition constraint).
- **Constant-size:** Proof size is O(log(n)) regardless of chain length.
- **Depth cap:** MAX_FOLD_DEPTH = 16 prevents unbounded proving cost.
- **Wide hash (124-bit):** AccumulatedHash uses 4 BabyBear elements for birthday-attack resistance (~2^62 vs ~2^15.5 with single element).

### Composition Interface

- **CONSUMED BY:** PresentationProof (IVC final_root == derivation state_root)
- **PRODUCES:** initial_root, final_root, accumulated_hash
- **BINDING:** Wide accumulated hash (124-bit) prevents birthday attacks on chain forgery

---

## 23. MerkleStarkAir (Basic Merkle Membership)

### Statement

```
There EXISTS a leaf value and a Merkle path such that:
  - parent == current + sib0 + sib1 + sib2 + position (linear hash, NOT Poseidon2)
  - position * (position-1) * (position-2) * (position-3) == 0
  - Path chains from leaf_hash (row 0, col 0) to root (last row, col 5)
```

### Public Inputs (2 elements)

- PI[0]: `leaf_hash` -- the value at the leaf
- PI[1]: `root` -- the tree root

### Witness

- Per level: current hash, 3 siblings, position (0-3), computed parent

### Security Properties

- **WARNING:** This uses a LINEAR hash (addition-based), NOT Poseidon2. It is the test/development AIR for the STARK infrastructure. For production use, prefer `MerklePoseidon2StarkAir` which uses collision-resistant Poseidon2 hashing.
- **Soundness (limited):** Position validity is degree-4. The linear "hash" provides NO collision resistance -- it exists only to validate the STARK machinery.
- **Classification:** `ProofTier::Experimental`

### Composition Interface

- **CONSUMED BY:** Test infrastructure, STARK verifier development
- **NOT FOR PRODUCTION** -- use Poseidon2 variants instead

---

## 24. Compute Delivery AIR (ComputeDeliveryAir -- DSL descriptor)

### Statement

```
There EXISTS a sequence of compute steps s_0, ..., s_{n-1} such that:
  - Total FLOPS accumulated >= contracted_flops (PI[0..1] as split u64)
  - Duration (step count) <= max_duration (PI[2])
  - Average quality >= min_quality threshold (PI[3])
  - Step indices increment monotonically from 0 to num_steps-1
  - All diff values are non-negative (30-bit decomposition with high bit = 0)
```

### Public Inputs (5 elements)

- PI[0]: `contracted_flops_lo` -- lower 31 bits of required FLOPS
- PI[1]: `contracted_flops_hi` -- upper bits of required FLOPS
- PI[2]: `max_duration` -- maximum allowed time units
- PI[3]: `min_quality` -- minimum quality in basis points
- PI[4]: `num_steps` -- trace length (padded to power of 2)

### Witness (41 columns per row)

- flops_acc, duration_acc, quality_acc, step_index
- flops_delta, quality_delta (per-step contributions)
- diff + 30-bit decomposition (range proof)
- Auxiliary columns: step_plus_one, flops_acc_next, quality_acc_next, duration_acc_next

### Security Properties

- **Soundness:** Transition constraints enforce monotonic accumulation (T1-T4). Range proof (30-bit decomposition + high bit = 0) proves non-negative differences. Boundary constraints bind step_index to 0 at start and num_steps at end.
- **SLA binding:** Public inputs are derived by the VERIFIER from settlement data (not from the proof). A malicious provider cannot claim different SLA parameters.
- **Prior vulnerability (fixed):** Previously, delivery "verification" only checked proof format. Now calls `stark::verify()` with correct circuit descriptor.

### Composition Interface

- **CONSUMED BY:** Compute exchange settlement (proves work was actually performed)
- **BINDING:** Public inputs derived from on-chain settlement SLA parameters by the verifier

---

## 25. Match Proof (MatchProofDescriptor -- DSL descriptor)

### Statement

```
There EXISTS a maker_limit, maker_remaining, and identity witnesses such that:
  - Price satisfaction: fill_price >= maker_limit (if sell) or fill_price <= maker_limit (if buy)
    (proven via non-negative price_diff with correct sign encoding based on maker_side)
  - No overfill: fill_amount <= maker_remaining
    (proven via non-negative amount_diff = maker_remaining - fill_amount)
  - Conservation: total_payment == fill_price * fill_amount
    (multiplication constraint)
  - No self-trade: maker_id != taker_id
    (proven via non-zero id_diff with inverse witness: id_diff * id_diff_inv == 1)
```

### Public Inputs (6 elements)

- PI[0]: `fill_price` -- the execution price
- PI[1]: `fill_amount` -- the fill quantity
- PI[2]: `total_payment` -- price * amount (conservation binding)
- PI[3]: `maker_side` -- 0=Buy, 1=Sell
- PI[4]: `maker_id_elem` -- truncated hash of maker identity
- PI[5]: `taker_id_elem` -- truncated hash of taker identity

### Witness (13 columns)

- maker_limit (private limit price), maker_remaining (private remaining amount)
- price_diff, amount_diff (range proof witnesses)
- id_diff, id_diff_inv (non-zero proof witnesses)
- always_on selector (constant 1)

### Security Properties

- **Soundness:** Conservation via degree-2 multiplication constraint. Price satisfaction via polynomial encoding that correctly inverts sign based on maker_side (binary-constrained). Self-trade prevention via ConditionalNonzero (degree 3): selector * value * inverse.
- **Privacy:** Maker's limit price and remaining amount are private witness values. Only the fill parameters are public.
- **ID collision risk:** maker_id_elem uses first 4 bytes of hash modulo p (1-in-2^31 collision probability -- negligible, and prover rejects on collision).

### Composition Interface

- **CONSUMED BY:** Orderbook settlement (proves matching engine operated fairly)
- **BINDING:** Public inputs match the fill record; pre/post queue root hashes (in metadata) bind to state

---

## 26. CDP Circuit (CdpCircuitDescriptor -- Stablecoin)

### Statement

```
There EXISTS collateral_amount, price such that:
  - collateral_value = collateral_amount * price
  - debt_threshold = debt_amount * ratio_bps
  - scaled_collateral = collateral_value * 10000
  - diff = scaled_collateral - debt_threshold >= 0
    (proven via diff_high_bit == 0, enforcing diff < p/2)
  - oracle_commitment binds price to an attested oracle value
  - position_id binds proof to a specific CDP position
```

### Public Inputs (7 elements)

- PI[0]: `position_id_0` -- lower hash of position identifier
- PI[1]: `position_id_1` -- upper hash of position identifier
- PI[2]: `oracle_commitment` -- hash(price, timestamp, oracle_pk)
- PI[3]: `debt_amount` -- outstanding stablecoin debt
- PI[4]: `ratio_bps` -- minimum collateral ratio (e.g., 15000 = 150%)
- PI[5]: `price_timestamp` -- when price was attested
- PI[6]: `max_age` -- maximum staleness allowed

### Witness (14 columns)

- collateral_amount (private), price (bound to oracle)
- collateral_value, debt_threshold, scaled_collateral (intermediate products)
- diff, diff_high_bit (range proof for non-negativity)
- position_id, oracle_commitment, timestamps

### Security Properties

- **Soundness:** Three multiplication constraints verify the ratio arithmetic. The non-negativity check (`diff_high_bit == 0`) proves `scaled_collateral >= debt_threshold`, i.e., the position meets its collateral requirement.
- **Oracle binding:** oracle_commitment ties the price to an externally attested value (signature verification is executor-side).
- **Position binding:** position_id prevents proof reuse across different CDPs.
- **Staleness check:** price_timestamp and max_age are public inputs -- the verifier enforces freshness.

### Composition Interface

- **CONSUMED BY:** Stablecoin minting/borrowing (proves healthy collateral ratio before issuing debt)
- **DEPLOYED AS:** CellProgram via ProgramRegistry (custom effect in Effect VM)

---

## 27. Health Factor Circuit (Lending)

### Statement

```
There EXISTS collateral_value, debt_amount, threshold_bps such that:
  - lhs = collateral_value * threshold_bps
  - rhs = debt_amount * BPS_SCALE (10000)
  - diff = lhs - rhs >= 0 (proven via diff_high_bit == 0)
  Therefore: the lending position is solvent.
```

### Public Inputs (3 elements)

- PI[0]: `collateral_value` -- total value of all collateral assets (scaled)
- PI[1]: `debt_amount` -- total debt value (scaled)
- PI[2]: `threshold_bps` -- liquidation threshold in basis points

### Witness (7 columns)

- collateral_value, debt_amount, threshold_bps
- lhs (product), rhs (product), diff, diff_high_bit

### Security Properties

- **Soundness:** Multiplication constraint (C1) and polynomial scaling (C2) compute the comparison correctly. Non-negativity enforced via `diff_high_bit == 0`. Multi-asset collateral is pre-aggregated into a single scaled value.
- **Simplicity:** Single-row proof (2 rows padded). No hash computation -- purely arithmetic range proof.

### Composition Interface

- **CONSUMED BY:** Lending protocol borrow/withdraw operations (proves position remains healthy)
- **DEPLOYED AS:** CellProgram via ProgramRegistry

---

## 28. Interest Accrual Circuit (Lending)

### Statement

```
There EXISTS a sequence of balance states b_0, ..., b_n such that:
  - b_0 == PI[start_balance]
  - b_n == PI[end_balance]
  - For each step i: interest_i = (balance_i * rate) / RATE_PRECISION
  - For each step i: b_{i+1} = b_i + interest_i
  - Rate is constant across all steps and matches PI[rate]
  - n == PI[num_blocks]
```

### Public Inputs (4 elements)

- PI[0]: `start_balance` -- balance before accrual
- PI[1]: `end_balance` -- balance after compound interest
- PI[2]: `rate` -- per-block rate numerator (denominator = 10^9)
- PI[3]: `num_blocks` -- number of compounding periods

### Witness (5 columns per row)

- block_index, balance, rate, interest, next_balance

### Security Properties

- **Soundness:** Polynomial constraint (C1) enforces `next_balance == balance + interest`. Transition constraint (C2) chains `balance[i+1] == next_balance[i]`. Boundary constraints bind first-row balance to start_balance and last-row next_balance to end_balance.
- **Compound interest:** The iterated structure naturally computes compound interest (each row uses the updated balance from the previous row).
- **Deterministic:** Given start_balance, rate, and num_blocks, the end_balance is uniquely determined.

### Composition Interface

- **CONSUMED BY:** Lending protocol interest settlement (proves correct accrual over a period)
- **DEPLOYED AS:** CellProgram via ProgramRegistry

---

## 29. Garbled Vickrey Auction (Gallery -- private_vickrey.rs)

### Statement

```
There EXISTS input labels (obtained via OT) and a gate evaluation trace such that:
  - The Vickrey tournament circuit was correctly evaluated gate-by-gate
  - The output labels decode to (winner_index, second_price)
  - circuit_commitment matches the pre-published garbled tables
  - A STARK proof (GarbledEvaluationAir) attests to correct evaluation
```

### Public Inputs (at the STARK level)

- `circuit_commitment` (WideHash, 4 elements) -- binds to specific garbled circuit
- `output_label_hash` (WideHash, 4 elements) -- binds to specific auction outcome

### Witness

- Per-bidder input labels (obtained via oblivious transfer)
- Gate evaluation records (left_label, right_label, gate_index, hash, table_entry, output)
- The garbled tables themselves (committed pre-auction)

### Security Properties

- **Privacy (Phase 1 -- semi-trusted):** Auctioneer learns bid ORDERING (who beat whom) but NOT bid magnitudes (OT hides label selection). Public learns only winner_index and second_price.
- **Privacy (Phase 2 -- federation-mediated):** No single party sees labels. Federation nodes contribute XOR-shared randomness. Threshold cooperation required for output decoding.
- **Verifiability:** GarbledEvaluationAir STARK proof demonstrates correct evaluation. Verifier checks output_label_hash against known outcome labels.
- **Circuit design:** Tournament-style comparison network. N bidders require N-1 comparisons. Each comparison: 31-bit subtraction-borrow chain.

### Composition Interface

- **CONSUMED BY:** Gallery auction settlement (proves correct winner determination)
- **REQUIRES:** Oblivious Transfer protocol (external, for input label delivery)
- **PRODUCES:** VickreyResult with winner_index, second_price, and evaluation_proof

---

## 30. Dispute State Machine Circuit (DisputeDsl)

### Statement

```
There EXISTS a valid state transition (old_state -> new_state) such that:
  - The transition follows the dispute protocol state machine:
    Created(0)->Claimed(1): always valid
    Claimed(1)->Finalized(3): block_height >= deadline AND no_challenger
    Claimed(1)->Disputed(2): block_height < deadline AND has_challenger
    Disputed(2)->Finalized(3): resolution == provider_wins AND arbiter_signed
    Disputed(2)->Slashed(4): resolution == challenger_wins AND arbiter_signed
  - All other transitions produce non-zero constraints (rejected)
  - Binary flags are consistent: no_challenger + has_challenger == 1
```

### Public Inputs (8 elements)

- PI[0]: `old_state` -- state before transition (0-4 enum)
- PI[1]: `new_state` -- state after transition (0-4 enum)
- PI[2]: `block_height` -- current block height (executor-provided)
- PI[3]: `deadline` -- dispute deadline
- PI[4]: `provider_stake` -- provider's locked stake
- PI[5]: `challenger_stake` -- challenger's locked stake (0 if none)
- PI[6]: `resolution` -- arbiter's decision (0=pending, 1=provider_wins, 2=challenger_wins)
- PI[7]: `arbiter_signed` -- 1 if executor verified arbiter signature

### Witness (12 columns)

- old_state, new_state, block_height, deadline, provider_stake, challenger_stake
- resolution, arbiter_signed, height_minus_deadline, deadline_minus_height
- no_challenger, has_challenger

### Security Properties

- **Soundness:** PI bindings (C1) prevent the prover from lying about state/params. Binary constraints (C2) ensure flags are 0 or 1. Complementary constraint (C3) ensures exactly one of no_challenger/has_challenger. Polynomial encoding of transition rules catches all invalid transitions.
- **Executor trust:** Signature verification and block height oracle are executor-verified (bound via public inputs, not proven in-circuit).
- **State exhaustiveness:** All 5 states and their valid transitions are encoded. Any undefined transition (e.g., Created->Slashed) violates the polynomial constraint.

### Composition Interface

- **CONSUMED BY:** Optimistic settlement protocol (proves dispute lifecycle transitions are valid)
- **BINDING:** Public inputs must match executor-verified on-chain/in-state data

---

## Full Circuit Inventory

Complete map of all circuits in the pyana system, organized by location.

### Core Circuits (`circuit/src/`)

| File | Circuit/AIR | One-Line Description |
|------|-------------|---------------------|
| `effect_vm.rs` | EffectVmAir | State transition proof for the 18-type effect instruction set |
| `presentation.rs` | PresentationAir | Credential presentation: issuer membership + fold + derivation + unlinkability |
| `multi_step_air.rs` | MultiStepDerivationAir | Datalog rule application chain with hash accumulation |
| `body_membership.rs` | BodyMembershipProof | Proves each body fact hash exists in Poseidon2 Merkle tree |
| `ivc.rs` | IvcAir / StateTransitionAir | N-step fold chain accumulated into single hash-chain proof |
| `fold_air.rs` | FoldAir | Single fold step: fact removal + check addition with root transition |
| `accumulator_air.rs` | AccumulatorNonRevocationAir | O(1) polynomial non-membership proof for revocation checking |
| `note_spending_air.rs` | NoteSpendingAir | UTXO spend: nullifier + commitment + Merkle membership |
| `committed_threshold.rs` | CommittedThresholdAir | Private value >= threshold via bit decomposition |
| `poseidon2_air.rs` | Poseidon2Air | Single Poseidon2 permutation correctness |
| `poseidon2_air.rs` | MerklePoseidon2Air | Round-by-round Merkle membership with Poseidon2 |
| `poseidon2_air.rs` | MerklePoseidon2StarkAir | Simplified Merkle membership (1 row/level, full hash in constraint) |
| `poseidon2_air.rs` | BlindedMerklePoseidon2StarkAir | Unlinkable ring membership (blinded leaf) |
| `garbled_air.rs` | GarbledEvaluationAir | Correct garbled circuit evaluation (Poseidon2-based) |
| `temporal_predicate_dsl.rs` | TemporalPredicateDsl / TemporalPredicateAir | Predicate held continuously for N steps |
| `quantified_absence.rs` | ChunkAbsenceAir | Per-chunk "no element satisfies P" (IVC approach) |
| `quantified_absence.rs` | QuotientAccumulatorAir | Polynomial quotient proof of universal absence |
| `poseidon_stark_verifier_circuit.rs` | PoseidonStarkVerifierCircuit | Kimchi circuit verifying a Poseidon-committed STARK (STARK-in-Pickles) |
| `stark.rs` | MerkleStarkAir | Basic (linear hash) Merkle membership -- test/development only |
| `derivation_air.rs` | DerivationAir | Single-step Datalog derivation with rule/substitution checking |
| `chunked_derivation.rs` | ChunkedDerivationAir | Derivation split into chunks for large rule sets |
| `predicate_air.rs` | PredicateAir | Generic predicate evaluation (GTE, LTE, range) |
| `arithmetic_predicate_air.rs` | ArithmeticPredicateAir | Arithmetic comparison predicates with range proofs |
| `relational_predicate_air.rs` | RelationalPredicateAir | Multi-column relational predicates |
| `compound_predicate_air.rs` | CompoundPredicateAir | AND/OR composition of predicate sub-circuits |
| `temporal_predicate_air.rs` | (legacy) TemporalPredicateAir | Hand-written temporal predicate (superseded by DSL version) |
| `non_membership.rs` | NonMembershipAir | Sorted-Merkle non-membership (superseded by accumulator) |
| `schnorr_air.rs` | SchnorrSignatureAir | Schnorr signature verification in-circuit |
| `native_signature_air.rs` | NativeSignatureAir | Native curve signature verification |
| `merkle_air.rs` | MerkleAir | Generic Merkle path verification |
| `block_transition_air.rs` | BlockTransitionAir | Block-level state transition proof |
| `cross_state_derivation.rs` | CrossStateDerivationAir | Derivation across multiple state roots |
| `plonky3_prover.rs` | (Plonky3 backend) | Production STARK prover via Plonky3 |
| `plonky3_verifier_air.rs` | P3VerifierAir | Plonky3-native verifier AIR |
| `plonky3_recursion.rs` | (recursion) | Recursive STARK composition via Plonky3 |
| `poseidon_stark.rs` | PoseidonStark | STARK with Poseidon Merkle commitments (for Kimchi bridge) |
| `xmss.rs` | XMSS circuit | Post-quantum hash-based signature support |

### Application Circuits (`apps/`)

| App | File | Circuit | One-Line Description |
|-----|------|---------|---------------------|
| compute-exchange | `delivery_verification.rs` | ComputeDeliveryAir | Proves provider computed contracted FLOPS within duration/quality bounds |
| orderbook | `circuit.rs` | MatchProofDescriptor | Proves fair matching: price satisfaction + no overfill + conservation + no self-trade |
| stablecoin | `circuit.rs` | CdpCircuitDescriptor | Proves CDP collateral ratio >= minimum (with oracle price binding) |
| lending | `circuit.rs` | HealthFactorCircuit | Proves lending position solvency: collateral * threshold >= debt * scale |
| lending | `circuit.rs` | InterestAccrualCircuit | Proves correct compound interest computation over N blocks |
| gallery | `private_vickrey.rs` | VickreyCircuit + GarbledEvaluationAir | Privacy-preserving Vickrey auction via garbled circuits + STARK proof |

### DSL Test Circuits (`pyana-dsl-tests/src/`)

| File | Circuit | One-Line Description |
|------|---------|---------------------|
| `dispute_dsl.rs` | DisputeDsl | Dispute state machine: valid transitions with deadline/stake/arbiter enforcement |

### Backend Circuits (`circuit/src/backends/`)

| Backend | Key Files | Description |
|---------|-----------|-------------|
| Kimchi/Mina | `kimchi_native/` | Native Kimchi gates for derivation, fold, IVC, non-membership, predicates, presentation |
| Mina/Pickles | `mina/` | IPA verifier, step/wrap verifiers, GLV endomorphism, Pickles integration |
| Plonky3 | `backends/plonky3.rs` | Production STARK backend with Poseidon2 commitments |
| SP1 | `backends/sp1.rs` | SP1 zkVM backend |
| Binius | `backends/binius.rs` | Binary-field STARK backend |
| STARK-in-Pickles | `backends/stark_in_pickles.rs` | Bridge: verify custom STARK inside Pickles proof |
