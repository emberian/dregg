//! GOLD endgame: a continuous whole-chain IVC accumulator over **finalized turns**.
//!
//! ## What this is
//!
//! [`ivc`](dregg_circuit::ivc) accumulates an *attenuation* fold-chain (delegation
//! depth) into one proof. [`joint_turn_recursive`](crate::joint_turn_recursive)
//! folds the N **per-cell** proofs of a *single* shared turn (the hyperedge
//! apex) into one recursive proof. Neither is the whole-chain accumulator.
//!
//! This module is that accumulator: it folds the sequence of *finalized turn*
//! proofs — in the exact order the node's `tau`/blocklace finality produces
//! (`node::blocklace_sync::poll_finalized_blocks` -> `FinalizedBlock`) — into
//! ONE running recursive proof attesting:
//!
//!   "all turns 1..K executed correctly **and** the finalized state root
//!    advanced correctly from the genesis root to the final root, in that
//!    order."
//!
//! It is the sequential dual of the joint-turn (which is cross-cell at one
//! instant). Here the binding is *temporal*: turn N's post-state root must be
//! turn N+1's pre-state root (`prev.NEW_COMMIT == next.OLD_COMMIT`) — the
//! happened-before chain over the *finalized* order, exactly the property the
//! node's tau ordering establishes.
//!
//! ## The two pieces
//!
//! 1. **Lean-emitted `dregg-turn-chain-binding-v2` descriptor** (one row per folded
//!    position): binds the sequential chain AND the running ordered-history digest.
//!    Each row carries `[old_root, new_root, acc_in, acc_out, idx, is_real,
//!    real_count]`; its Poseidon2 relation is served by the shared chip lookup, with
//!    constraints emitted by Lean for:
//!      - chain continuity: `new_root[i] == old_root[i+1]` (the temporal tooth);
//!      - first row `old_root == genesis_root` (public input);
//!      - last row `new_root == final_root` (public input);
//!      - **running digest `acc_out == hash_4_to_1([acc_in, old_root, new_root,
//!        idx])` ENFORCED in-circuit** (the genuine round-by-round Poseidon2 of
//!        [`poseidon2_permute_expr`], NOT a free witness column), first row
//!        `acc_in == 0`, last row `acc_out == chain_digest` (public);
//!      - `idx` is a positional counter (`0,1,2,…`) so the digest is positionally
//!        bound;
//!      - `num_turns` (public) is pinned to `real_count[last]`, the cumulative
//!        count of the non-padding (`is_real`) rows.
//!
//!    Rust builds only the chip-lane witness and interprets that descriptor. A trace
//!    whose turns are reordered, or that drops/inserts a turn, breaks continuity and
//!    is UNSAT; a forged `chain_digest` has no satisfying Poseidon2 witness; a forged
//!    `num_turns` mismatches the real-row count — those are the load-bearing rejections.
//!
//! 2. **The recursion tree (Gold) — REAL leaves.** Each finalized turn's leaf
//!    is the **ROTATED multi-table `Ir2BatchProof`** (`transferVmDescriptor2R24` &c) carried on
//!    `participant.rotated`, re-proven recursion-compatibly and wrapped in its own **in-circuit
//!    verifier layer** by [`prove_descriptor_leaf_rotated`] (the inner IR-v2 FRI engine —
//!    `ir2_config`, log_blowup 6 / 19 queries — is kept as-is; only the recursion verifier's
//!    params are retargeted to match it, and the leaf-wrap OUTPUT is a standard recursion-config
//!    log_blowup 3 / 38-query proof). The retired v1 `prove_descriptor_leaf` (the 186-column
//!    `EffectVmDescriptorAir` uni-STARK over a `FinalizedTurn::base_trace`) is DELETED —
//!    `FinalizedTurn` no longer carries that trace. All batch leaves are pairwise
//!    aggregated up a binary tree (`build_and_prove_aggregation_layer`, chained via
//!    [`BatchOnly`]) to ONE root batch-STARK proof. The Lean-emitted turn-chain proof
//!    is carried alongside and verified directly; the root's ordered segment remains
//!    the in-circuit link to the executed leaves. Verification cost is independent of K.
//!
//! ## What the leaf wrap proves (the statement-equality argument)
//!
//! The production turn artifact is a `p3-batch-stark` proof of
//! `EffectVmDescriptorAir(desc)` over `(extend_vm_trace(base_trace), dpis)`,
//! where `dpis` is the descriptor PI prefix (carrying the chain roots at
//! [`pi::OLD_COMMIT`] / [`pi::NEW_COMMIT`]). The recursion fork's in-circuit
//! verifier consumes uni-STARK proofs under the recursion `StarkConfig`, while
//! the production proof is a batch proof under the audited prover config — two
//! FRI engine instantiations of the SAME constraint set. The fold therefore
//! re-proves the IDENTICAL statement — same AIR (`EffectVmDescriptorAir::eval`,
//! config-agnostic), same extended trace ([`descriptor_recursion_matrix`] =
//! the same `extend_vm_trace` surface `prove_vm_descriptor` uses), same PI
//! prefix — as a recursion-compatible uni-STARK, and THAT proof is verified
//! in-circuit by the wrap layer. A claimed `(old_root, new_root)` with no
//! satisfying execution trace has no satisfying leaf under EITHER config (the
//! descriptor's hash sites force `NEW_COMMIT` to be the genuine Poseidon2
//! post-state commitment), so a prover that skips the host-side gate still
//! CANNOT produce a verifying root for a forged turn — that is the tooth
//! `ungated_prover_with_forged_post_commit_cannot_produce_a_root` bites on.
//!
//! ## What the verifier checks (three teeth, in order)
//!
//! [`verify_turn_chain_recursive`] takes the proof AND a caller-held trust
//! anchor (a [`RecursionVk`] — the root circuit's verifier-key fingerprint,
//! obtained once from an honest setup fold, distributed exactly like any
//! SNARK VK) and refuses unless ALL of:
//!
//!   1. **VK pin** — the root proof's verifier-reconstruction inputs (table
//!      shapes, packing, NPO manifest shape, and the preprocessed Merkle
//!      commitment binding the root verifier circuit's op-list) fingerprint
//!      to the anchor. This closes the from-scratch-prover route through
//!      `verify_recursive_batch_proof`'s reconstruct-from-the-proof
//!      discipline: a root proof of a DIFFERENT circuit no longer verifies
//!      "as if" it were the chain fold. (Guarantee, precisely: under blake3
//!      collision resistance + MMCS binding, the accepted root is a valid
//!      batch-STARK of the SAME root verifier-circuit structure the anchor
//!      was extracted from.)
//!   2. **Lean-descriptor attestation** — the carried turn-chain descriptor proof
//!      (`WholeChainProof::binding_proof`) is verified against its exact four PIs. Its scalar
//!      genesis/final/count must match the head-lane projection of the carried wide claim; its own
//!      sequential digest remains bound by the descriptor. The distinct wide ordered-segment digest
//!      is attested by tooth 4 below.
//!   3. **The root** — `verify_recursive_batch_proof` on the single root.
//!
//! ## CRITICAL HOLES #1/#2/#6 — CLOSED by the ordered SEGMENT ACCUMULATOR (2026-06-24)
//!
//! A cross-model adversarial review (`metatheory/docs/CODEX-IVC-SOUNDNESS-REVIEW.md` +
//! `CODEX-IVC-REVIEW-2.md`) found a forged whole-chain claim the verifier ACCEPTS: a
//! root that EXECUTED history A paired with a whole-chain CLAIM for a different history
//! B. The root cause was that the chain claim came from a separate hand-authored binding AIR
//! leaf attesting a hash-chain over CLAIMED roots — never tied in-circuit to the
//! descriptor leaves' ACTUAL roots — so the binding leaf (and its claim) could be swapped
//! or built for a different history than the one the descriptor leaves executed.
//!
//! **THE FIX (codex's ordered segment-accumulator).** The separate binding leaf is GONE
//! from the soundness path. Every DESCRIPTOR leaf carries a constant-size ordered SEGMENT
//! `[first_old, last_new, count, acc]`, exposed through the `expose_claim` table and BOUND
//! IN-CIRCUIT:
//!   - **leaf** ([`prove_descriptor_leaf_rotated_with_segment`]): `first_old`/`last_new`
//!     are the descriptor proof's verified rotated roots (PI `V1_PI_COUNT`/`+1`, read off
//!     the child's `air_public_targets`), `count = 1`, `acc = H(first_old, last_new)`. So
//!     the segment is tied to the ACTUAL execution this leaf re-proves — a prover cannot
//!     expose endpoints that differ from the descriptor it folded.
//!   - **aggregation combine** ([`aggregate_tree`]): both children expose a segment; the
//!     combine constrains STATE CONTINUITY (`L.last_new == R.first_old`), COUNT additivity
//!     (`count = L.count + R.count`), and the ORDERED DIGEST fold (`acc = H(L.acc, R.acc)`,
//!     left≠right ⇒ order-sensitive), then re-exposes the parent segment — up to the root.
//!   - **root + host check** ([`verify_turn_chain_recursive_from_parts`], the SEGMENT
//!     tooth): the root's exposed segment `[first_old, last_new, count, acc]` is the
//!     whole-chain claim derived BY CONSTRUCTION from the real descriptor leaves; the host
//!     checks it equals the carried `[genesis_root, final_root, num_turns, chain_digest]`,
//!     fail-closed. There is NO swappable binding leaf — a root that executed A cannot
//!     expose B's endpoints, so a B-claim against an A-execution is REJECTED.
//!
//! The executable witness `mixed_root_forgery_executes_A_claims_B`
//! (`circuit-prove/tests/ivc_turn_chain_rotated.rs`) asserts the forgery is REJECTED
//! (`is_err`) — the close. The out-of-band swap witness
//! `carried_binding_proof_unlinked_to_root_is_rejected` and the #2 digest/num_turns forge
//! teeth (`binding_descriptor_forged_digest_unsat` /
//! `binding_descriptor_forged_num_turns_unsat`) all
//! still reject. The whole fix is dregg-side — it reuses the EXISTING recursion-fork
//! `expose_claim` channel + the aggregation expose hook (which exposes the
//! `air_public_targets` AND lets the combine add cross-child constraints) + the in-circuit
//! poseidon2 challenger perm; NO fork change was needed.
//!
//! ## The honest residual floor (named, not hidden)
//!
//! - **Engine soundness** (`recursive_sound`): the wrap layer's in-circuit FRI
//!   verifier and the root batch-STARK verifier are the plonky3 recursion
//!   fork's; their soundness is the named crypto carrier, as everywhere else.
//!   This is the SAME standard FRI/STARK soundness assumption every recursive
//!   STARK chain carries (Mina/Plonky3-style) — it is NOT a dregg-specific gap
//!   and is not provable in Lean. With the two fork follow-ups below CLOSED,
//!   recursion soundness rests on this assumption ALONE: nothing app-specific
//!   is left un-pinned.
//! - **Segment digest — a multi-felt Poseidon2 commitment** ([`seg_poseidon_commit`],
//!   codex re-review #3, CLOSED). The ordered-history `acc` is a genuine
//!   [`SEG_DIGEST_WIDTH`]-felt Poseidon2 sponge over the recursion config's
//!   `BABY_BEAR_D4_W16` challenger permutation (the SAME full-round arithmetization the
//!   FRI challenger uses, CTL-bound against the Poseidon2 AIR), matched host-side by
//!   [`seg_poseidon_commit_host`]. This REPLACED the prior one-felt quadratic fold
//!   `a*M1 + b*M2 + a*b*M3`, which was algebraically broken (a given middle root had a
//!   directly-solvable colliding partner, plus degeneracy roots that made it ignore an
//!   operand). The multi-felt commitment has no algebraic shortcut and ~124-bit collision
//!   resistance, so a same-genesis/same-final/same-count history B with a different middle
//!   now mismatches the root digest. The ONLINE [`crate::accumulator`] is scoped OUT (it
//!   keeps the single-felt binding-leaf carrier, zero-padded to the new lane width — codex
//!   #4 mixed-root weakness for that path is unchanged).
//! - **Child-circuit identity under the VK pin — ⚑ RETRACTED, THEN CLOSED FOR REAL (2026-07-30).**
//!
//!   ⚑ **READ THIS FIRST; the whole bullet below it describes a substrate that no longer exists.**
//!   Fork rev `fc3c6df` (`emberian/plonky3-recursion`, pinned in the root `Cargo.toml`) moved a
//!   constant's VALUE into `ConstAir`'s preprocessed row — `[ext_mult, out_idx, value[0..D]]`,
//!   width `D + 2`, was `[ext_mult, out_idx]` — and added `D` degree-1 constraints
//!   `main.value[i] == prep.value[i]`. That is exactly the repair sketched under "THE REPAIR,
//!   DESIGNED" further down, which said it must not be taken. It WAS taken, deliberately, on an
//!   explicit substrate call: `ConstAir` is a **p3 primitive AIR in a fork this repo maintains**,
//!   with no Lean authoring path short of replacing p3; dregg's own circuit logic — the effect VM,
//!   the descriptors, the gadgets, `air_accepts` — stayed Lean-authored and was not touched. The
//!   change is one column block plus one equality and adds no dregg semantics to a p3 primitive.
//!   ⚑ `circuit-prove/tests/law1_enforcement_gate.rs` scores that edit at 1 authored symbolic site
//!   and its RATCHET DELTA IS ZERO, because the gate cannot see the fork at all; that blindness is
//!   now written down in the gate's own "what this gate CANNOT see" list.
//!
//!   CONSEQUENCES, each MEASURED at the new rev by inverting the probe that had asserted the
//!   opposite (opposite claim written and re-run; construction and controls byte-unchanged):
//!   * `const_pin_probe.rs` — k = 7 and k = 9 now mint DIFFERENT fingerprints
//!     (`b2c625d1…3b80` vs `a1b0c130…1bcb`), so an anchor from one REFUSES the other's proof.
//!   * `vk_pin_lever_a_probe.rs` (A) — two children differing only in a const present DIFFERENT
//!     caps, so the deployed pin can discriminate a const-level lie at all.
//!   * `vk_pin_lever_a_probe.rs` (B) — **horn 2 is closed.** Baking a foreign cap MOVES the parent's
//!     preprocessed commitment (`[1233588605, …]` vs `[1128576629, …]`) while every SHAPE field
//!     `recursion_vk_fingerprint` hashes stays identical: instances
//!     `[(6,7), (2,6), (59,13), (24,11), (2,12)]`, `public_flat_len = 51`. The separation runs
//!     through the commitment itself, not through a row count. (`(6, 7)` is the Const table at its
//!     new `2 + D` width.)
//!   * `vk_spine_forgery_probe.rs` — the const-swapped child now MOVES the whole-chain anchor
//!     (`c206d0f7…e3ab` honest vs `c3464e4e…2d2f` const-swapped), holding the root fingerprint
//!     FIXED on both sides so the movement is attributable to the spine alone.
//!
//!   ⚑ **AND THEREFORE HORN 1 IS NO LONGER THE ONLY DOOR** — see the horn bullets below, whose
//!   "MEASURED INVISIBLE" verdict on horn 2 is superseded.
//!
//!   ---
//!
//!   The retraction that stood here, kept because it is the record of how the hole was found:
//!   the bullet before it claimed this hole was closed by [`aggregate_tree`] folding every
//!   child through the fork's `into_recursion_input_pinned`, baking each child's own preprocessed
//!   commitment as a CONSTANT. Two probes on `main` MEASURED that claim false at its load-bearing
//!   half. A comment claiming a closed hole is worse than the hole, so it was retracted rather
//!   than softened.
//!
//!   * `circuit-prove/tests/const_pin_probe.rs` (`63ffb1a08`) — two circuits differing ONLY in an
//!     `alloc_const` value both verify and present the SAME `recursion_vk_fingerprint`
//!     (`65c5643c…7413f88c` at both k = 7 and k = 9; 39154 vs 39083 proof bytes, so they are
//!     genuinely different artifacts, and `const_pool` was measured NOT to fold 7 with 9). An
//!     anchor extracted from the k = 7 circuit ACCEPTS the k = 9 proof.
//!   * `circuit-prove/tests/vk_pin_lever_a_probe.rs` (`bb42f9800`) — on the deployed pin path,
//!     building the parent verifier circuit over ONE child with the honest cap baked and with a
//!     perturbed cap baked yields an IDENTICAL parent preprocessed cap (`[1901438425, …]`) and
//!     identical `Const degree_bits` (7). The positive control — drop the pin entirely
//!     (`expected_preprocessed_commit: None`) — DOES move both (`[439113501, …]`, degree_bits 6),
//!     so the instrument is not blind to the op-list and the verdict is attributable.
//!
//!   MECHANISM, read: `pin_preprocessed_commit` emits `alloc_const(v)` + `connect(target, const)`.
//!   `ConstAir`'s preprocessed row is `[ext_mult, out_idx]` — wiring only; the VALUE lives in the
//!   constraint-free MAIN trace (its own header: "The AIR has no constraints"). So the parent's
//!   op-list records THAT a constant sits at that slot, never WHICH — and `recursion_vk_fingerprint`
//!   hashes shape + preprocessed commitment. The retracted bullet's second horn ("bake the foreign
//!   commitment and the parent op-list changes, so the ROOT preprocessed commitment changes") is
//!   therefore FALSE as measured. Compounding it, [`batch_to_pinned_input`] and
//!   [`merge_two_segment_proofs`] read the expected cap OFF THE CHILD PROOF
//!   (`child.stark_common.preprocessed.commitment`) — the pin is self-referential.
//!
//!   CONSEQUENCE: a prover substitutes ANY circuit with a matching table manifest that does no
//!   descriptor verification at all, and the parent re-verifies it, because the parent reconstructs
//!   the child's AIRs from SHAPE alone. Every sentence in this module, in `lightclient`, and in the
//!   K-fold tests reading "the root VK pin TRANSITIVELY certifies the whole tree's leaf-circuit
//!   identity" is UNSUPPORTED. `plonky3_recursion_impl.rs`'s "does NOT (cannot, harness-side) pin
//!   the **child** proofs' circuit identity" is the correct comment; this one was not.
//!
//!   THE TWO HORNS, each at its own resolution:
//!   * **Horn 1 — bake the HONEST cap, fold a FOREIGN child.** The cap targets are not merely
//!     transcript-observed: the fork pushes them as a commitment ROUND of the in-circuit PCS check
//!     (`recursion/src/verifier/batch_stark.rs`, `coms_to_verify.push((global.commitment.clone(),
//!     pre_round))`), so a child whose real preprocessed commitment differs has no satisfying
//!     opening — UNSAT under MMCS binding. READ, not measured, and it is a restatement of
//!     `recursive_sound` rather than an independent tooth. The one test that looks like evidence,
//!     `ivc_turn_chain_rotated::pinned_leaf_identity_rejects_foreign_child_in_band`, exercises the
//!     DUAL (honest child, FOREIGN cap) and asserts only `is_err()`; on that path the honest witness
//!     generator is handed two different values for one `connect`-shared slot, so the error is
//!     PREDICTED to be a runner `WitnessConflict` — a refusal by the honest prover, which an
//!     adversarial prover simply does not perform.
//!     ⚑ **THAT PREDICTION IS NOW MEASURED, AND IT WAS RIGHT.** Run with `--ignored --nocapture`:
//!     `Circuit(WitnessConflict { witness_id: WitnessId(478), existing: 1588400913,
//!     new: 1588400914, expr_ids: [ExprId(32947), ExprId(221911)] })` — a delta of exactly 1, the
//!     `roots[0][0] += ONE` the test applies. So the test is the honest prover declining to write a
//!     trace, NOT the in-circuit opening being UNSAT, and it is **not evidence for horn 1**.
//!     Horn 1 itself remains READ, not measured.
//!   * **Horn 2 — bake the FOREIGN cap.** ⚑ **CLOSED at fork rev `fc3c6df` — the "MEASURED
//!     INVISIBLE, twice" verdict this bullet carried is SUPERSEDED.** The baked cap is
//!     `alloc_const` material, and const values are now preprocessed columns, so baking a foreign
//!     cap moves the parent's preprocessed commitment and hence the root fingerprint. Re-measured
//!     by `vk_pin_lever_a_probe.rs` (B), inverted deliberately. This was the horn a forger took for
//!     free; it now costs them the root anchor.
//!
//!   So the two horns no longer share a single unguarded door. A prover substituting a child must
//!   either bake the foreign cap — and be refused by verify tooth (1), MEASURED — or keep the honest
//!   cap and be refused by horn 1, which is READ and still UNMEASURED. ⚑ Horn 1 is the residual;
//!   it is no longer the *only* thing standing between a forger and the anchor.
//!
//!   ### THE REPAIR, DESIGNED — "the exposed VK spine" (⚑ BUILT, `e1d8ab9bc`)
//!
//!   The obvious fix — put const values in `ConstAir`'s PREPROCESSED trace and constrain
//!   `main.value == prep.value` — is a change to a Rust AIR in the p3 fork. This paragraph used to
//!   say that under this repo's standing law it IS the drift, not the fix, and that it was named
//!   here so the next reader would not take it.
//!   ⚑ **THAT READING WAS OVER-BROAD AND IS CORRECTED (2026-07-30).** Law #1 governs DREGG's
//!   circuit logic — the effect VM, the descriptors, the gadgets, `air_accepts` — and every one of
//!   those is Lean-authored and stayed so. `ConstAir` is a **p3 primitive** in a fork this repo
//!   already maintains, and there is no Lean authoring path for it short of replacing p3, so a
//!   minimal local change there is not the drift the law is aimed at. The fix was taken at fork rev
//!   `fc3c6df`, kept to one column block and one equality, with no dregg semantics added to the
//!   primitive. What the law's caution DID buy is real and should be kept in view: a Rust AIR is
//!   debt, and this change enlarges the un-ratcheted surface by one authored site that
//!   `law1_enforcement_gate.rs` structurally cannot see.
//!
//!   The rest of this section — the spine over `expose_claim` — is still the right shape and is
//!   BUILT. The const binding does not replace it: the spine binds a child's PROGRAM, the const
//!   binding binds the VALUES inside a fixed program, and they close different halves. The
//!   sentence below about wiring-only preprocessed columns was true when written and is now true of
//!   `PublicAir` and `AluPrepLaneCols` only — `ConstAir` carries its value as a preprocessed
//!   IMMEDIATE, deliberately, while `PublicAir` deliberately does NOT (a public input's value is
//!   per-execution data and must stay out of circuit identity).
//!
//!   What stays out of the AIR is the `expose_claim` channel this module already runs the segment
//!   over — and it has teeth the const pin lacks:
//!
//!     * `ExposeClaimAir`'s per-lane PREPROCESSED columns are `[witness_idx, read_mult]`, so WHICH
//!       witness a lane surfaces IS circuit identity (inside the preprocessed commitment, hence
//!       inside the root fingerprint). A const's value never is.
//!     * its per-lane constraint is `active * (public_value[lane] − v_0) == 0`, and
//!       `verify_all_tables` feeds `proof.non_primitives[].public_values` straight into
//!       `verify_batch` as that AIR's public values — so the host-readable lane is bound to the
//!       committed main trace, not a free scalar a forger edits in the proof struct.
//!     * `v_0` is RECEIVED on the `WitnessChecks` bus at that preprocessed `witness_idx`, against
//!       the slot's single CREATOR. `connect` is one shared witness slot per class
//!       (`ConnectDsu::alloc_witness`), and the fork demotes every later writer of an
//!       already-defined slot to a bus reader (`circuit/src/circuit.rs`: `Op::Public` with
//!       `is_dup` ⇒ `increment_ext_reads`, multiplicity −1); constants are emitted before publics
//!       (`emit_constants` then `emit_publics`), so the cap class has EXACTLY ONE send. One send
//!       tuple against N reads forces every read to that tuple — which is precisely why an exposed
//!       lane carries the same value the child's preprocessed-trace opening consumed, rather than a
//!       second independently-chooseable copy. (Had the class two creators, a forger could feed the
//!       exposure one value and the FRI check another, and this design would be broken. It does
//!       not, and that is the load-bearing reading.)
//!
//!   So: EXPOSE the pinned cap and check it against a CALLER-HELD anchor. Concretely —
//!
//!   1. **fork plumbing, no AIR change.** `VerifierCircuitResult` gains
//!      `child_vk_cap_targets() -> Vec<Target>` (returning
//!      `common_data.preprocessed_commit_observation_targets()`), and `AggExposeHook` /
//!      `NextLayerExposeHook` widen to pass the left/right cap targets alongside
//!      `air_public_targets`. Already-allocated Targets only; zero new constraints in any AIR.
//!   2. **the spine, in [`segment_combine_expose`] and its two window siblings.** Each node appends
//!      a `VK_SPINE_WIDTH` (= 8) lane block to its exposed claim:
//!      `vk_spine = seg_poseidon_commit(L.cap8 ‖ L.vk_spine8 ‖ R.cap8 ‖ R.vk_spine8)`, over the SAME
//!      isolated `BABY_BEAR_D4_W24` sponge the ordered digest already runs on. A leaf
//!      ([`prove_descriptor_leaf_rotated_with_segment`]) exposes
//!      `vk_spine = seg_poseidon_commit([VK_SPINE_LEAF_TAG])`; a leaf's own identity IS its cap,
//!      which its parent absorbs, so the leaf sentinel need not itself be identity-bound.
//!
//!      ⚑ **THAT LIST WAS SHORT BY THE WHOLE CARRIER FAMILY, and the deployed custom turn broke on
//!      the omission.** Every segment carrier owes the fold a spine, not just the three merge
//!      nodes: the DUAL-EXPOSE leaf minters ([`prove_descriptor_leaf_dual_expose_at`],
//!      [`prove_descriptor_leaf_expose_segment_and_claims`]) expose the leaf seed at
//!      [`SEG_VK_SPINE_FIRST`] with their claim slices pushed out to [`SEG_SPINE_WIDTH`], and the
//!      ~14 `*_segmented` carrier BINDING NODES re-expose `[segment ‖ vk_spine]` via
//!      [`binding_node_segment_and_spine`]. Those nodes are asymmetric — the leg child is a
//!      segment carrier, the sub-proof child is a bare LEAF — so the right operand of their fold is
//!      the leaf base case, which is the design answer and not a fork ([`combine_vk_spine_parts`]).
//!      Until they moved, every carrier turn minted a 25-lane parent and
//!      [`exposed_board_window`] refused it as a pre-spine artifact.
//!   3. **the anchor.** [`RecursionVk`] is joined by an 8-felt `VkSpine`, minted by the SAME honest
//!      setup fold (`WholeChainProof::root_vk_fingerprint` gains a `root_vk_spine` sibling), and
//!      verify tooth (1) compares BOTH, fail-closed. ⚑ This costs the client nothing
//!      asymptotically, because the whole-chain anchor is ALREADY per-shape — see
//!      `WholeChainProof::root_vk_fingerprint`'s own caveat ("an anchor pins one accepted window
//!      shape; a client accepting several window shapes holds one anchor per shape"). The spine
//!      rides exactly that existing shape-specificity; it adds no new class of client burden.
//!   4. **shape arithmetic.** [`exposed_board_window`] derives the combine mode from a child's
//!      claim width; it becomes `SEG_WIDTH + VK_SPINE_WIDTH + 2W` and REFUSES anything else, so
//!      every artifact minted before the spine fails to fold — loudly, at the existing fail-closed
//!      branch, not silently truncated.
//!
//!   WHAT A FORGER MUST DO AFTER THIS. Substituting any node circuit — leaf or interior — changes
//!   that node's cap; its parent absorbs the changed cap into `vk_spine`; the change propagates to
//!   the root. So the forger must either find a Poseidon2 collision on the 8-felt sponge (~124-bit,
//!   the SAME carrier the ordered-history digest already rests on), or make an exposed lane differ
//!   from the bus-read witness (refuted by the single-creator reading above). The only remaining
//!   route is horn 1: fold a foreign child while baking the HONEST cap, which requires breaking the
//!   in-circuit MMCS opening — i.e. `recursive_sound`. That is the intended shape: the app-specific
//!   escape is gone and what is left is the named crypto carrier. ⚠ The design ROUTES AROUND horn 1;
//!   it does not close it.
//!   ⚑ The sentence that stood here — "after the repair horn 1 matters MORE, because it is the only
//!   door left" — was written when horn 2 was measured invisible. At fork rev `fc3c6df` horn 2 is
//!   measured CLOSED, so horn 1 is no longer the only door: a forger who bakes a matching foreign
//!   cap is refused by the root fingerprint, and only a forger who keeps the honest cap reaches
//!   horn 1. Horn 1 is still the residual and is still unmeasured; it is no longer load-bearing
//!   alone.
//!
//!   WHAT THE SPINE DOES NOT DO. It binds the tree's circuit identities to ONE anchor value per fold
//!   SHAPE. It does not make the anchor K-independent. That needs canonical shape normalization —
//!   `p3_recursion::recursion::{CanonicalShapeSpec, check_canonical_shape, inject_canonical_fillers}`
//!   exists in the fork and is referenced NOWHERE in this tree — so that one fixed-point merge
//!   circuit verifies any child; with it, every interior cap collapses to one value and the sponge
//!   fold degenerates to a `connect`. That is the follow-on, and it is the SAME follow-on the
//!   existing per-shape `RecursionVk` anchor already needs, not a new debt the spine creates.
//!
//!   THE FLAG DAY (greenfield: a rebuild, not a migration — stated so it is findable). Landing the
//!   spine changes every fold node's op-list, so EVERY `RecursionVk` in this tree re-emits.
//!   Re-emit `ugc-dregg/tests/fixtures/whole_history_proof.bin` + `whole_history_anchor.hex` via
//!   `produce_history_envelope`, plus the three checked-in copies of that anchor
//!   (`portal/dist/history.json`, `site/light-client/history.json`,
//!   `site/dist/light-client/history.json`). Re-pin `circuit-prove/src/bin/root_fri_instance.rs`'s
//!   `EXPECTED_DEGREE_BITS` and the Mina-side degree-bits / VK-prefix pins in
//!   `bridge/mina-zkapp/scripts/root-air-real.ts` and `root-air-fullchain.ts`. Bump
//!   [`WHOLE_CHAIN_PROOF_ENVELOPE_V1`] and `pg-dregg`'s INDEPENDENT
//!   `WHOLE_CHAIN_PROOF_TRANSPORT_V1` to carry the spine anchor. `DREGG_APEX_RECURSION_VK` +
//!   `chain/gnark/settlement_circuit.go` + `chain/gnark/fixtures/apex_vk_identity.json` move only if
//!   the apex/shrink circuit is itself folded through a spine node. WHAT REFUSES TO LOAD: every
//!   pre-spine recursion artifact — [`exposed_board_window`]'s width check refuses to fold it, and
//!   the envelope version gate refuses to decode it.
//! - **Leaf public values re-exposed at the root (fork follow-up — CLOSED).** Each child is fed
//!   with its GENUINE per-table public inputs threaded up (`into_recursion_input_pinned` calls
//!   `genuine_table_public_inputs`, not the empty-vector legacy path), so a child's exposed
//!   segment publics are re-verified IN-CIRCUIT at the next layer instead of left as
//!   unconstrained target slots. Combined with the ordered SEGMENT accumulator, the
//!   whole-chain `[genesis_root, final_root, num_turns, chain_digest]` is re-exposed at the
//!   root (the `expose_claim` table) and host-checked by verify tooth 3 — the carried claim is
//!   in-band linked to the REAL descriptor leaves folded inside the root.
//!
//! ## K-fold vs unbounded
//!
//! [`prove_turn_chain_recursive`] folds an arbitrary *finite* K into one proof.
//! This is genuine IVC for a bounded window: the verifier checks one
//! constant-cost root proof for the whole window.
//!
//! The fully *unbounded* online accumulator — where a single running proof is
//! re-folded with each newly-finalized turn forever, with the previous running
//! proof verified in-circuit so memory stays O(1) — needs the recursion fork's
//! `into_recursion_input::<BatchOnly>` chaining to be driven as a *fold* rather
//! than a *tree*. The 2-step inductive core of that loop is [`fold_two_turns`]
//! (`running ∘ next_turn -> new_running`); see its docs for what the unbounded
//! driver still needs.
//!
//! ## Prover memory: the resident tree vs the streaming fold
//!
//! The K-fold has two SCHEDULES over the SAME balanced tree (same DAG ⇒ same root segment /
//! chain digest — the ordered digest is shape-sensitive, so shape identity is load-bearing):
//!
//!   * **RESIDENT** (default): mint all K leaf proofs, then fold ([`aggregate_tree`], or the
//!     parallel merge-pool scan-state driver under `DREGG_MERGE_WORKERS`). Peak resident
//!     recursion proofs O(K) — latency-optimal for a prover farm, pathological in RAM on a
//!     long chain.
//!   * **STREAMING** ([`prove_turn_chain_recursive_streaming`], or `DREGG_STREAM_FOLD_WINDOW`
//!     for the default entries): interleave leaf proving with folding through a window + a
//!     binary-counter carry stack ([`aggregate_tree_streaming`]). Peak resident proofs
//!     O(W + log2(K/W)), independent of K; the root exposes the identical segment and verifies
//!     via the unchanged [`verify_turn_chain_recursive`].

use p3_baby_bear::BabyBear as P3BabyBear;
use p3_field::{PrimeCharacteristicRing, PrimeField32};
use p3_recursion::{
    BatchOnly, ProveNextLayerParams, RecursionInput, RecursionOutput, build_and_prove_next_layer,
    build_and_prove_next_layer_with_expose,
};

use crate::gpu_backend::{
    prove_recursion_aggregation_auto_with_expose, prove_recursion_layer_auto_with_expose,
};
use crate::joint_turn_aggregation::{
    CarrierWitness, DescriptorParticipant, verify_descriptor_participant,
};
use crate::plonky3_recursion_impl::recursive::{
    DreggRecursionConfig, create_recursion_backend, recursion_layer_over, recursion_vk_fingerprint,
    verify_recursive_batch_proof_with_config,
};
use dregg_circuit::descriptor_by_name::descriptor_by_name;
use dregg_circuit::descriptor_ir2::{
    DreggStarkConfig, Ir2BatchProof, MemBoundaryWitness, prove_vm_descriptor2,
    verify_vm_descriptor2,
};
use dregg_circuit::field::BabyBear;
use dregg_circuit::turn_chain_witness::{TURN_CHAIN_BINDING_NAME, turn_chain_binding_witness};

// Re-exported so chain consumers (the light client) name the trust-anchor type
// from the module that defines the verification discipline around it.
pub use crate::plonky3_recursion_impl::recursive::RecursionVk;

const D: usize = 4;

/// The BabyBear prime modulus `2^31 - 2^27 + 1`. The `count` / `num_turns` chain claim is a
/// BabyBear field element, so a faithful (non-wrapping) count requires `num_turns < p`
/// (codex re-review #5).
const BABY_BEAR_MODULUS: u32 = 0x7800_0001;

/// The recursion config's challenge (extension) field — the field the verifier
/// circuit (and every expose/combine hook) builds over.
type RecursionChallenge = <DreggRecursionConfig as p3_uni_stark::StarkGenericConfig>::Challenge;

/// **The segment digest width** — the multi-felt Poseidon2 commitment carried as the
/// ordered-history `acc`. Codex re-review #3 replaced the algebraically-broken one-felt
/// quadratic fold with a genuine collision-resistant commitment; the FAITHFUL-FLOOR lift
/// (`.docs-history-noclaude/FAITHFUL-STATE-COMMITMENT.md`, `docs/deos/COMMITMENT-WAIST-CENSUS.md` #1) widened it
/// from 4 lanes (~62-bit) to **8** lanes ⇒ ~124-bit collision resistance, MATCHING the
/// per-turn leg's 8-felt faithful floor. The host's tooth compares all eight; the
/// commitment is a real full-round Poseidon2 sponge ([`seg_poseidon_commit`] squeezes exactly
/// `SEG_DIGEST_WIDTH` DISTINCT lanes, no zero-pad) — there is no algebraic shortcut and no
/// degeneracy root (the quadratic fold's weakness).
pub const SEG_DIGEST_WIDTH: usize = 8;

/// The number of exposed chain claims: `[first_old8(8), last_new8(8), count(1),
/// acc_0..acc_{W-1}(W)]` where `W = SEG_DIGEST_WIDTH`. The host verifier's segment tooth reads
/// these directly, comparing against `[genesis_root8, final_root8, num_turns, chain_digest_0..]`.
/// The FAITHFUL-FLOOR lift widened the state endpoints from single felts (~15-bit birthday) to
/// the 8-felt (~124-bit) anchors the per-turn legs already publish.
pub const NUM_CHAIN_CLAIMS: usize = SEG_DIGEST_FIRST + SEG_DIGEST_WIDTH;

/// The number of base-field lanes in a state-commit anchor exposed by a segment — the 8-felt
/// (~124-bit) faithful commit. The state endpoints (`first_old8`/`last_new8`) each occupy this
/// many lanes; a WIDE / wide-welded leg sources them genuinely, a narrow leg broadcasts its
/// single rotated commit felt across all eight (no entropy gain, structural type-compat only).
pub const SEG_ANCHOR_WIDTH: usize = 8;

/// **THE WIDE CUSTOM LEG's EXPOSED FIELD-OCTET WIDTH (the app-root weld leg-emit).** The wide
/// custom descriptor (`customVmDescriptor2R24`) publishes the cell's committed `fields[0..8]`
/// octet — the faithfully-carried limbs the `new8` commitment absorbs — as 8 PIs positioned
/// ahead of the post-fields-root octet and the 16 wide anchors; see
/// [`custom_leg_field_octet_lo`] for the exact position (it is NOT immediately before the
/// anchors — the `withAfterFieldsRootPins` octet sits between). The app-root arm reads
/// `field[binding.field_key]` from this octet and the fold connects it to the sub-proof's
/// published root `R`. Pinned to the Lean `customFieldKExposure` emit / the Rust
/// `generate_rotated_custom_wide` field exposure.
pub const CUSTOM_APP_FIELD_OCTET_LEN: usize = 8;

/// The native-eight post-state fields-map root published immediately after the
/// Custom app-field octet and immediately before the 16 wide state anchors.
/// Lean source: `EffectVmEmitRotationV3.withAfterFieldsRootPins`; Rust witness
/// source: `trace_rotated::FIELDS_ROOT_GROUP` (non-contiguous rotated columns).
pub const CUSTOM_POST_FIELDS_ROOT_LEN: usize = 8;

/// **WHERE THE WIDE CUSTOM LEG PUBLISHES THE COMMITTED `fields[0..8]` OCTET — the ONE derivation.**
///
/// The deployed wide custom member is
/// `wideAppend (withAfterFieldsRootPins (withAfterOctetPins (withDfaRcPins customV3) 4))`
/// (Lean `EmitWideRegistryProbe`, key `customVmDescriptor2R24`), and every wrapper APPENDS its
/// pins to the PI tail. So the leg's PI vector ends, in emit order,
///
/// ```text
///   [ … base pins … ‖ fields[0..8] octet (8) ‖ post-state fields-root (8) ‖ old8 (8) ‖ new8 (8) ]
/// ```
///
/// and the octet therefore starts `CUSTOM_APP_FIELD_OCTET_LEN + CUSTOM_POST_FIELDS_ROOT_LEN +
/// 2*SEG_ANCHOR_WIDTH` felts before the end — currently `n - 32` (measured: at the deployed
/// `public_input_count = 91` the octet is PIs 59..67; those were 98 / 66..74 before the
/// 2026-08-07 seven-slot PI compaction). `None` iff the leg is too short to carry
/// that tail at all (i.e. it is not the wide app-root-weldable member).
///
/// EVERY reader of the octet — the deployed app-root arm below, the entity/braid fold, and the
/// test probes — must go through THIS function. The offset was previously open-coded at each
/// site; when `withAfterFieldsRootPins` was inserted between the octet and the anchors it moved
/// the octet by 8 and a stale hand-written `n - 24` silently started reading the fields-root
/// instead of the fields.
#[inline]
pub fn custom_leg_field_octet_lo(pi_len: usize) -> Option<usize> {
    pi_len.checked_sub(
        2 * SEG_ANCHOR_WIDTH + CUSTOM_POST_FIELDS_ROOT_LEN + CUSTOM_APP_FIELD_OCTET_LEN,
    )
}

/// Faithful custom-wide ABI: all eight canonical program-VK felts are trace-carried
/// and pinned at the eight slots after the `custom_proof_commitment` block (low4 params + four
/// exact VK teeth). Derived from `CUSTOM_COMMIT_PI_LO` — it was the literal `54` until the
/// 2026-08-07 seven-slot PI compaction moved the rotated tail down by seven.
pub const CUSTOM_PROGRAM_VK_PI_LO: usize = crate::joint_turn_recursive::CUSTOM_COMMIT_PI_LO
    + crate::joint_turn_recursive::CUSTOM_COMMIT_LEN;
pub const DEPLOYED_CUSTOM_PROGRAM_VK_PI_LEN: usize = 8;
pub const DIRECT_IR2_VK8_REFUSAL: &str =
    "direct-IR2 custom fold requires an exact 8-felt leg-to-leaf program-VK correlation";

/// The exact correlation boundary the future full-width binding node consumes.
/// Length is checked before equality so a low4 prefix can never masquerade as
/// a faithful program identity.
pub(crate) fn require_direct_ir2_leg_vk8(
    leg_program_vk: &[BabyBear],
    direct_leaf_program_vk: [BabyBear; 8],
) -> Result<(), String> {
    let leg_program_vk: [BabyBear; 8] = leg_program_vk
        .try_into()
        .map_err(|_| DIRECT_IR2_VK8_REFUSAL.to_string())?;
    if leg_program_vk != direct_leaf_program_vk {
        return Err(
            "direct-IR2 custom fold: leg program VK8 differs from the anchored direct leaf VK8"
                .to_string(),
        );
    }
    Ok(())
}

/// Segment field lanes (the order they are exposed in the `expose_claim` table). The two
/// 8-felt state anchors come first, then the count, then the multi-felt digest.
pub const SEG_FIRST_OLD: usize = 0;
pub const SEG_LAST_NEW: usize = SEG_ANCHOR_WIDTH;
pub const SEG_COUNT: usize = 2 * SEG_ANCHOR_WIDTH;
/// First lane of the multi-felt digest block (`acc_0`); the digest occupies
/// `[SEG_DIGEST_FIRST .. SEG_DIGEST_FIRST + SEG_DIGEST_WIDTH]`.
pub const SEG_DIGEST_FIRST: usize = 2 * SEG_ANCHOR_WIDTH + 1;
/// A segment is exactly [`NUM_CHAIN_CLAIMS`] base-field lanes.
pub const SEG_WIDTH: usize = NUM_CHAIN_CLAIMS;

/// **THE VK SPINE** — the block of lanes every K-fold node exposes, carrying the circuit identity
/// of everything folded beneath it. `SEG_DIGEST_WIDTH` wide because it is a
/// [`seg_poseidon_commit`] squeeze, exactly like the ordered-history digest.
pub const VK_SPINE_WIDTH: usize = SEG_DIGEST_WIDTH;

/// The spine sits immediately AFTER the segment in an exposed claim, and before any board window.
pub const SEG_VK_SPINE_FIRST: usize = SEG_WIDTH;

/// A K-fold exposed claim is `[segment(SEG_WIDTH) ‖ vk_spine(VK_SPINE_WIDTH) ‖ IN(W) ‖ OUT(W)]`.
/// This is the plain (`W = 0`) width, and the base [`exposed_board_window`] recovers `W` from.
pub const SEG_SPINE_WIDTH: usize = SEG_WIDTH + VK_SPINE_WIDTH;

/// The number of base-field elements in a child's preprocessed-commitment cap (its VK-identity
/// core) at the recursion config's `cap_height = 0`: ONE digest of `DIGEST_ELEMS = 8`.
///
/// Asserted rather than assumed at every absorb site: a cap of a different length would silently
/// change what the spine commits to.
pub const VK_CAP_TARGET_LEN: usize = 8;

/// Domain tag absorbed at a LEAF, where there is no child cap to absorb: `"VKL1"` as a BabyBear.
/// A leaf's own identity is its cap, which its PARENT absorbs — so this sentinel only needs to be
/// domain-separated from an interior node's absorb, not itself identity-bound.
const VK_SPINE_LEAF_TAG: u32 = 0x564B_4C31 % 0x7800_0001; // "VKL1" mod BabyBear

/// **THE LEAF SPINE SEED.** `commit([VK_SPINE_LEAF_TAG])` — the base case of the spine fold.
///
/// Deliberately NOT identity-bound: a foreign leaf can emit any value here, and it does not matter,
/// because the leaf's PARENT absorbs the leaf's real preprocessed cap (which a foreign leaf cannot
/// choose). Making this a constant keeps every honest leaf's seed identical so the root spine is a
/// function of the tree's circuit identities and shape alone.
pub(crate) fn leaf_vk_spine(
    cb: &mut p3_circuit::CircuitBuilder<RecursionChallenge>,
) -> [p3_recursion::Target; VK_SPINE_WIDTH] {
    let tag = cb.define_const(RecursionChallenge::from_u32(VK_SPINE_LEAF_TAG));
    seg_poseidon_commit(cb, &[tag])
}

/// Host-side dual of [`leaf_vk_spine`] — the eight lanes an honest leaf's spine block holds.
///
/// A host that hand-builds a `[segment ‖ vk_spine ‖ claims]` row (the stand-in leg leaves the
/// carrier adapters' teeth mint through [`prove_descriptor_leaf_with_pi_slice_expose`]) must fill
/// the spine block with THIS value, or its row is a shape mirror carrying a lie in the lanes a
/// parent folds.
pub fn leaf_vk_spine_host() -> [BabyBear; VK_SPINE_WIDTH] {
    seg_poseidon_commit_host(&[BabyBear::new(VK_SPINE_LEAF_TAG)])
}

/// **THE SPINE FOLD — the one place a child's circuit identity enters the parent's claim.**
///
/// `vk_spine = commit(L.cap8 ‖ L.vk_spine8 ‖ R.cap8 ‖ R.vk_spine8)`, over the SAME isolated
/// `BABY_BEAR_D4_W24` sponge [`seg_poseidon_commit`] already runs the ordered-history digest on
/// (so no new gadget, no new op-type, no AIR change).
///
/// `l_cap`/`r_cap` are the children's preprocessed-commitment cap TARGETS, handed over by the
/// fork's widened expose hook (`VerifierCircuitResult::child_vk_cap_targets`). They are the same
/// targets the child's preprocessed-trace opening is checked against inside this circuit, and —
/// because `connect` gives the class ONE shared witness slot whose single creator is the pin's
/// `Op::Const` (later writers are demoted to bus readers) — the value absorbed here is the value
/// that opening consumed. That is what makes the spine bind rather than restate the prover's
/// choice.
///
/// L is absorbed before R, so the spine is order-sensitive in the same way the history digest is.
pub(crate) fn combine_vk_spine(
    cb: &mut p3_circuit::CircuitBuilder<RecursionChallenge>,
    l: &[p3_recursion::Target],
    r: &[p3_recursion::Target],
    l_cap: &[p3_recursion::Target],
    r_cap: &[p3_recursion::Target],
    spine_first: usize,
) -> [p3_recursion::Target; VK_SPINE_WIDTH] {
    let need = spine_first + VK_SPINE_WIDTH;
    assert!(
        l.len() >= need && r.len() >= need,
        "both children must expose a segment AND a VK spine ({need} lanes); got {} and {} — a \
         pre-spine artifact cannot be folded",
        l.len(),
        r.len()
    );
    combine_vk_spine_parts(
        cb,
        l_cap,
        &l[spine_first..spine_first + VK_SPINE_WIDTH],
        r_cap,
        &r[spine_first..spine_first + VK_SPINE_WIDTH],
    )
}

/// **THE SPINE FOLD, over EXPLICIT spine blocks** — the core [`combine_vk_spine`] reads its two
/// blocks out of segment-carrying claims at a fixed offset.
///
/// Split out because a SEGMENT-PRESERVING BINDING NODE has an asymmetric pair: its LEFT child is a
/// dual-expose leg leaf (a segment carrier, so its spine sits at [`SEG_VK_SPINE_FIRST`]) while its
/// RIGHT child is a bare sub-proof LEAF whose `expose_claim` is the claim alone — a commitment, a
/// `child_vk`, a `key_commit` — with no segment and therefore no spine lane to read. That child IS
/// a leaf, so its spine is the leaf base case [`leaf_vk_spine`]: the design answer, not a fork of
/// the fold. Its own identity still enters the parent, through its cap.
pub(crate) fn combine_vk_spine_parts(
    cb: &mut p3_circuit::CircuitBuilder<RecursionChallenge>,
    l_cap: &[p3_recursion::Target],
    l_spine: &[p3_recursion::Target],
    r_cap: &[p3_recursion::Target],
    r_spine: &[p3_recursion::Target],
) -> [p3_recursion::Target; VK_SPINE_WIDTH] {
    assert_eq!(
        l_cap.len(),
        VK_CAP_TARGET_LEN,
        "left child exposes {} VK-cap target(s), expected {VK_CAP_TARGET_LEN} — a child with no \
         preprocessed commitment has no circuit identity to fold and must be refused upstream, \
         not absorbed as an empty cap",
        l_cap.len()
    );
    assert_eq!(
        r_cap.len(),
        VK_CAP_TARGET_LEN,
        "right child exposes {} VK-cap target(s), expected {VK_CAP_TARGET_LEN}",
        r_cap.len()
    );
    assert_eq!(l_spine.len(), VK_SPINE_WIDTH, "left spine block width");
    assert_eq!(r_spine.len(), VK_SPINE_WIDTH, "right spine block width");
    let mut inputs = Vec::with_capacity(2 * (VK_CAP_TARGET_LEN + VK_SPINE_WIDTH));
    inputs.extend_from_slice(l_cap);
    inputs.extend_from_slice(l_spine);
    inputs.extend_from_slice(r_cap);
    inputs.extend_from_slice(r_spine);
    seg_poseidon_commit(cb, &inputs)
}

/// **THE PARENT CLAIM OF A SEGMENT-PRESERVING BINDING NODE** — `[segment(SEG_WIDTH) ‖
/// vk_spine(VK_SPINE_WIDTH)]`, i.e. exactly [`SEG_SPINE_WIDTH`] lanes, the shape
/// [`exposed_board_window`] reads as a plain (window-0) segment carrier.
///
/// Single-sourced because ~14 carrier binding nodes (custom / state / app-root / sovereign /
/// factory / hatchery / membership / blinded-membership / presentation / caveat-admission / deco /
/// note-spend ×2 / whole-turn cohort) all owe the fold the same two things and must not drift:
///
///   1. the leg's segment lanes `[0 .. SEG_WIDTH)`, carried through verbatim, and
///   2. a REAL spine over BOTH children — the leg's own spine block folded with the sub-proof
///      leaf's constant leaf seed, under both children's caps.
///
/// Before this existed each node re-exposed the bare 25-lane segment, and [`exposed_board_window`]
/// refused every one of them as a pre-spine artifact — which is what the deployed custom turn hit.
pub(crate) fn binding_node_segment_and_spine(
    cb: &mut p3_circuit::CircuitBuilder<RecursionChallenge>,
    leg_claim: &[p3_recursion::Target],
    leg_vk_cap: &[p3_recursion::Target],
    subproof_vk_cap: &[p3_recursion::Target],
) -> Vec<p3_recursion::Target> {
    assert!(
        leg_claim.len() >= SEG_SPINE_WIDTH,
        "the leg leaf must expose a segment AND a VK spine ({SEG_SPINE_WIDTH} lanes); got {} — a \
         pre-spine dual-expose leaf cannot be bound",
        leg_claim.len()
    );
    let subproof_spine = leaf_vk_spine(cb);
    let vk_spine = combine_vk_spine_parts(
        cb,
        leg_vk_cap,
        &leg_claim[SEG_VK_SPINE_FIRST..SEG_VK_SPINE_FIRST + VK_SPINE_WIDTH],
        subproof_vk_cap,
        &subproof_spine,
    );
    let mut parent = Vec::with_capacity(SEG_SPINE_WIDTH);
    parent.extend_from_slice(&leg_claim[..SEG_WIDTH]);
    parent.extend_from_slice(&vk_spine);
    debug_assert_eq!(parent.len(), SEG_SPINE_WIDTH);
    parent
}

fn to_p3(v: BabyBear) -> P3BabyBear {
    P3BabyBear::from_u64(v.0 as u64)
}

/// The Poseidon2 challenger perm config the segment-digest sponge runs over —
/// `BABY_BEAR_D4_W16`, the SAME permutation the recursion FRI challenger uses (enabled by
/// `prepare_circuit_for_verification`). Reusing it means the sponge is a genuine, already
/// CTL-soundly-arithmetized Poseidon2, not a new gadget.
fn seg_poseidon_config() -> p3_circuit::ops::Poseidon2Config {
    // The ISOLATED segment-digest permutation: `BABY_BEAR_D4_W24` is a DISTINCT op-type
    // (`poseidon2_perm/baby_bear_d4_w24`) from the FRI challenger's `BABY_BEAR_D4_W16`.
    // Sharing nothing — chain-state, CTL bus, op-type — means the digest sponge's perm I/O
    // can never be transitively aliased into the verifier's shared `ExprId::ZERO` witness
    // class (the cross-op connect-DSU collapse that produced the `WitnessId(0)` conflict when
    // the digest reused the challenger's W16 perm). Enabled in
    // `DreggRecursionConfig::prepare_circuit_for_verification`.
    p3_circuit::ops::Poseidon2Config::BABY_BEAR_D4_W24
}

/// Sponge rate (in ext limbs) for the segment digest: `rate_ext` of `BABY_BEAR_D4_W24`
/// = 4. Each absorb adds up to 4 base-field-embedded inputs into the rate limbs; each
/// squeeze reads the 4 CTL-verified rate-output limbs.
const SEG_SPONGE_RATE: usize = 4;

/// Width (in ext limbs) of the sponge state for `BABY_BEAR_D4_W24` = `width_ext` = 6
/// (rate 4 + capacity 2).
const SEG_SPONGE_WIDTH: usize = 6;

/// A base-field domain-separation tag absorbed first, so the digest is a *keyed* sponge
/// (the empty-input / all-zero state cannot be reached by a real chain). Arbitrary fixed
/// nonzero BabyBear; not security-load-bearing on its own, only domain separation.
const SEG_DOMAIN_TAG: u32 = 0x5345_4731 % 0x7800_0001; // "SEG1" mod BabyBear

/// **The in-circuit ordered-segment digest** — a genuine multi-felt Poseidon2
/// commitment (codex re-review #3, replacing the algebraically-broken quadratic fold).
///
/// Runs a duplex sponge over the recursion config's challenger permutation
/// (`BABY_BEAR_D4_W16`, the SAME full-round Poseidon2 the FRI challenger uses, CTL-bound
/// against the Poseidon2 AIR), absorbing `inputs` (each a base-field-embedded ext scalar)
/// two-at-a-time into the rate limbs, then squeezing [`SEG_DIGEST_WIDTH`] base-field
/// lanes from the rate-output limbs. The returned targets are the digest lanes, exposed
/// through the `expose_claim` table (which reads each target's coeff-0) and matched
/// host-side EXACTLY by [`seg_poseidon_commit_host`].
///
/// Because the squeeze outputs are genuine Poseidon2 permutation coordinates, the digest
/// is collision-resistant: there is NO algebraic shortcut (the quadratic fold's `a*b`
/// solvable-collision) and no degeneracy root (the `a=-M2/M3` / `b=-M1/M3` cases that
/// made the old fold ignore an operand). A same-genesis/same-final/same-count history B
/// with a different middle now yields a different digest with ~124-bit security.
///
/// Used (i) at the descriptor leaf to seed `acc = commit([first_old, last_new])`, and
/// (ii) at each aggregation node to fold `parent.acc = commit(L.acc ++ R.acc)` — an
/// order-sensitive tree commitment (left≠right because L.acc is absorbed before R.acc).
///
/// `pub` so the executable witness test (`ivc_turn_chain_rotated.rs`) can mirror the lib's
/// EXACT segment combine when it reconstructs the fold from the public building blocks.
pub fn seg_poseidon_commit(
    cb: &mut p3_circuit::CircuitBuilder<RecursionChallenge>,
    inputs: &[p3_recursion::Target],
) -> [p3_recursion::Target; SEG_DIGEST_WIDTH] {
    let config = seg_poseidon_config();
    // IV/pad constant: a NONZERO domain tag. We deliberately AVOID feeding the shared zero
    // constant (`ExprId::ZERO` == `WitnessId(0)`) into the permutation — in the assembled
    // recursion verifier circuit a perm input/output that touches the shared zero-witness
    // trips a `WitnessConflict { WitnessId(0) }` (the all-zero double-creator class). Seeding
    // every state/pad lane with a nonzero IV keeps the sponge off WitnessId(0) entirely.
    let tag = cb.define_const(RecursionChallenge::from(P3BabyBear::from_u64(
        SEG_DOMAIN_TAG as u64,
    )));

    // Capacity IV seed (the `SEG_SPONGE_WIDTH - SEG_SPONGE_RATE` capacity limbs) for the
    // FIRST permutation; on it the capacity is CTL-bound to this `Const`, keeping the bus
    // balanced. On EVERY SUBSEQUENT permutation the capacity is chained OFF the bus (the
    // perm AIR inherits the previous row's capacity output) — see
    // `add_poseidon2_perm_sponge_step`. This is what makes the digest sponge's
    // `WitnessChecks` global cumulative balance: feeding the full previous state (capacity
    // included) as fresh CTL inputs each perm left every chained perm's capacity RECEIVE
    // unmatched (a perm only sends its rate outputs), so the aggregation child's lookup bus
    // did not balance to zero.
    let cap_seed: Vec<p3_recursion::Target> = vec![tag; SEG_SPONGE_WIDTH - SEG_SPONGE_RATE];

    // The rate lanes carried across permutations (seeded with the nonzero IV). The capacity
    // is held internally by the perm chain, not in this array.
    let mut rate: Vec<p3_recursion::Target> = vec![tag; SEG_SPONGE_RATE];

    // The padded absorb stream: the input length (so different arities can't collide) then
    // the inputs. Pad to a multiple of the rate with the nonzero IV.
    let len_tag = cb.define_const(RecursionChallenge::from(P3BabyBear::from_u64(
        inputs.len() as u64
    )));
    let mut stream: Vec<p3_recursion::Target> = Vec::with_capacity(inputs.len() + 1);
    stream.push(len_tag);
    stream.extend_from_slice(inputs);
    while stream.len() % SEG_SPONGE_RATE != 0 {
        stream.push(tag);
    }

    // Absorb: add each rate-block into the rate limbs, then permute. The first step seeds +
    // CTL-binds the capacity IV; subsequent steps chain the capacity off the bus. The result
    // is byte-identical to the full-state sponge (`seg_poseidon_commit_host`): the AIR
    // computes over the same rate + (inherited) capacity, only the bus bookkeeping differs.
    let mut first = true;
    for block in stream.chunks(SEG_SPONGE_RATE) {
        for (lane, &inp) in block.iter().enumerate() {
            rate[lane] = cb.add(rate[lane], inp);
        }
        rate = cb
            .add_poseidon2_perm_sponge_step(config, first, &rate, &cap_seed)
            .expect(
                "segment-digest poseidon2 sponge step builds (perm op enabled by the \
                     recursion config's prepare_circuit_for_verification)",
            );
        first = false;
    }

    // Squeeze SEG_DIGEST_WIDTH base lanes from the rate-output limbs. A squeeze that needs
    // more than the rate re-permutes WITHOUT absorbing (capacity still chained off-bus).
    let mut digest: Vec<p3_recursion::Target> = Vec::with_capacity(SEG_DIGEST_WIDTH);
    loop {
        for &r in rate.iter().take(SEG_SPONGE_RATE) {
            if digest.len() == SEG_DIGEST_WIDTH {
                break;
            }
            digest.push(r);
        }
        if digest.len() == SEG_DIGEST_WIDTH {
            break;
        }
        rate = cb
            .add_poseidon2_perm_sponge_step(config, false, &rate, &cap_seed)
            .expect("segment-digest poseidon2 squeeze step builds");
    }
    digest
        .try_into()
        .expect("digest collected exactly SEG_DIGEST_WIDTH lanes")
}

/// Host-side dual of [`seg_poseidon_commit`]: the SAME duplex sponge over the SAME native
/// Poseidon2 permutation (`default_babybear_poseidon2_16`, which the recursion config
/// enables in-circuit), so the prover computes the EXACT digest lanes the root proof will
/// expose. The state is the 16 base lanes (4 ext limbs × 4 coeffs); a base input is added
/// into coeff-0 of a rate limb (base lane `4*lane`); the squeeze reads coeff-0 of the rate
/// limbs (base lanes 0 and 4).
///
/// `pub` so the executable witness test can assert host/in-circuit agreement (the digest
/// the prover carries == the digest the root proof exposes).
pub fn seg_poseidon_commit_host(inputs: &[BabyBear]) -> [BabyBear; SEG_DIGEST_WIDTH] {
    use p3_baby_bear::default_babybear_poseidon2_24;
    use p3_symmetric::Permutation;

    let perm = default_babybear_poseidon2_24();
    let iv = to_p3(BabyBear::new(SEG_DOMAIN_TAG));

    // 24 base lanes = 6 ext limbs × D(=4) coeffs. Lane `4*limb + coeff`. coeff-0 of limb i
    // is lane `4*i` — the squeeze/absorb point that mirrors the in-circuit base-embedding.
    // Initial state mirrors the circuit's `[tag; 6]`: coeff-0 of every limb = the IV, rest 0.
    let mut state = [P3BabyBear::ZERO; 24];
    for limb in 0..SEG_SPONGE_WIDTH {
        state[limb * D] = iv;
    }

    let mut stream: Vec<BabyBear> = Vec::with_capacity(inputs.len() + 1);
    stream.push(BabyBear::new(inputs.len() as u32));
    stream.extend_from_slice(inputs);
    while stream.len() % SEG_SPONGE_RATE != 0 {
        stream.push(BabyBear::new(SEG_DOMAIN_TAG));
    }

    for block in stream.chunks(SEG_SPONGE_RATE) {
        for (lane, &inp) in block.iter().enumerate() {
            // add into coeff-0 of rate limb `lane` == base lane `4*lane`.
            state[lane * D] += to_p3(inp);
        }
        state = perm.permute(state);
    }

    let mut digest: Vec<BabyBear> = Vec::with_capacity(SEG_DIGEST_WIDTH);
    loop {
        for lane in 0..SEG_SPONGE_RATE {
            if digest.len() == SEG_DIGEST_WIDTH {
                break;
            }
            // squeeze coeff-0 of rate limb `lane` == base lane `4*lane`.
            digest.push(BabyBear::new(state[lane * D].as_canonical_u32()));
        }
        if digest.len() == SEG_DIGEST_WIDTH {
            break;
        }
        state = perm.permute(state);
    }
    digest
        .try_into()
        .expect("host digest collected exactly SEG_DIGEST_WIDTH lanes")
}

/// Find the instance index of the `expose_claim` non-primitive table in a batch
/// proof, in the same instance order the in-circuit verifier allocates
/// `air_public_targets` (primitive tables first, then non-primitives in order).
///
/// Returns `None` if the proof carries no exposed-claim table.
pub(crate) fn expose_claim_instance_index(
    proof: &p3_circuit_prover::BatchStarkProof<DreggRecursionConfig>,
) -> Option<usize> {
    let num_primitive = p3_circuit_prover::batch_stark_prover::NUM_PRIMITIVE_TABLES;
    proof
        .non_primitives
        .iter()
        .position(|e| e.op_type.as_str() == "expose_claim")
        .map(|pos| num_primitive + pos)
}

/// **THE WHOLE-CHAIN TRUST ANCHOR — tooth 1's compared value, and what the light client holds.**
///
/// `blake3("dregg-whole-chain-anchor-v1" ‖ recursion_vk_fingerprint(root) ‖ root vk-spine lanes)`.
///
/// The first input is the root circuit's SHAPE + preprocessed binding. That half is deliberately
/// content-independent — it must be, or the anchor could not be reused across histories — and it
/// is exactly why it cannot see a child's identity: a `define_const` puts its VALUE in `ConstAir`'s
/// constraint-free main trace, so two children differing only in a pinned cap fingerprint
/// identically (MEASURED: `circuit-prove/tests/const_pin_probe.rs`).
///
/// The second input is the root's exposed VK SPINE — `commit(L.cap ‖ L.spine ‖ R.cap ‖ R.spine)`
/// folded from the leaves up, so it commits to the circuit identity of EVERY node in the tree. It
/// is host-readable and FRI-bound: the `expose_claim` lane is constrained
/// `active * (public_value − v_0) == 0` against public values the verifier feeds from the proof,
/// and `v_0` is bus-read at a PREPROCESSED `witness_idx` from the class's single creator — the
/// same slot the child's preprocessed-trace opening consumed.
///
/// So substituting a node's PROGRAM — a leaf that does no descriptor verification, an interior
/// node that skips a check, a node wired to check the wrong quantity — moves this value, and the
/// caller-held anchor refuses it. The raw [`recursion_vk_fingerprint`] does NOT move on a
/// same-shape substitution, and must not; the anchor is the observable that binds.
///
/// ## ⚑ WHAT THIS DOES NOT BIND — measured, not predicted
///
/// A child's CONSTANT VALUES. `ConstAir` commits a constant's value in its constraint-free MAIN
/// trace and only `[ext_mult, out_idx]` in preprocessed, so two circuits differing ONLY in a
/// constant have IDENTICAL preprocessed traces, hence an identical cap, hence an identical spine
/// and an identical anchor. MEASURED at `circuit-prove/tests/vk_spine_forgery_probe.rs`: the
/// `k = 7` and `k = 9` children agree on all four.
///
/// This is the ORIGINAL hole, pushed one level down: from "which circuit was folded" to "which
/// constants sit inside a fixed circuit". It matters, because a constant is an operand of a
/// constraint — zeroing a coefficient weakens what that constraint says. Reaching it requires
/// const values in the PREPROCESSED trace, which is an AIR change, which under this repo's
/// standing law is not ours to hand-write in Rust. It is NAMED here and NOT closed.
pub fn whole_chain_anchor(
    root_proof: &p3_circuit_prover::BatchStarkProof<DreggRecursionConfig>,
) -> Result<RecursionVk, TurnChainError> {
    let exposed = root_exposed_claims(root_proof).ok_or_else(|| {
        TurnChainError::ClaimedPublicsUnattested {
            reason: "root proof carries no exposed claim table, so it carries no VK spine — \
                     refused fail-closed rather than anchored on shape alone"
                .to_string(),
        }
    })?;
    if exposed.len() < SEG_SPINE_WIDTH {
        return Err(TurnChainError::ClaimedPublicsUnattested {
            reason: format!(
                "root exposes {} claim lane(s), fewer than the {SEG_SPINE_WIDTH} a segment + VK \
                 spine needs — this is a PRE-SPINE artifact and its subtree's circuit identity is \
                 uncertified; refused",
                exposed.len()
            ),
        });
    }
    let mut h = blake3::Hasher::new();
    h.update(b"dregg-whole-chain-anchor-v1");
    h.update(&recursion_vk_fingerprint(root_proof).0);
    for lane in &exposed[SEG_VK_SPINE_FIRST..SEG_VK_SPINE_FIRST + VK_SPINE_WIDTH] {
        h.update(&lane.as_u32().to_le_bytes());
    }
    Ok(RecursionVk(*h.finalize().as_bytes()))
}

/// Read the `expose_claim` table's public values from a batch proof (the 4 chain
/// claims, host-readable and bus-bound to the verified history). Returns `None`
/// if there is no exposed-claim table.
fn root_exposed_claims(
    proof: &p3_circuit_prover::BatchStarkProof<DreggRecursionConfig>,
) -> Option<Vec<BabyBear>> {
    let entry = proof
        .non_primitives
        .iter()
        .find(|e| e.op_type.as_str() == "expose_claim")?;
    Some(
        entry
            .public_values
            .iter()
            .map(|&v| BabyBear::new(v.as_canonical_u32()))
            .collect(),
    )
}

// ============================================================================
// One finalized turn: a whole-turn descriptor proof + the trace it attests +
// the (old_root, new_root) it advances.
// ============================================================================

/// A single finalized turn in the chain.
///
/// **Bucket-F (PATH-PRESERVE Phase 5a):** the `participant` carries the MANDATORY ROTATED leg —
/// the per-cell whole-turn rotated multi-table `Ir2BatchProof` (the [`RotatedParticipantLeg`])
/// plus its 38-PI vector. Host admission is [`verify_descriptor_participant`] (the rotated proof
/// verified standalone + selector-bound). The chain roots are read from the ROTATED commitments
/// (PI 34/35); the in-circuit leaf is the rotated batch re-proven via
/// [`prove_descriptor_leaf_rotated_with_config`]. The legacy v1 `base_trace` (the 186-column
/// EffectVM trace the old `prove_descriptor_leaf` wrap consumed) has been DROPPED — the rotated
/// leaf needs only `leg.{descriptor, proof, public_inputs}`.
pub struct FinalizedTurn {
    /// The whole-turn rotated descriptor proof (+ PI) for this finalized turn.
    pub participant: DescriptorParticipant,
}

impl FinalizedTurn {
    /// Wrap a (rotated) descriptor participant as a finalized turn.
    pub fn new(participant: DescriptorParticipant) -> Self {
        Self { participant }
    }

    /// The pre-state root this turn consumes — the ROTATED OLD-commit (PI 34).
    pub fn old_root(&self) -> BabyBear {
        self.participant.rotated.old_root()
    }

    /// The post-state root this turn produces — the ROTATED NEW-commit (PI 35). This is the next
    /// finalized turn's required `old_root` (the temporal binding).
    pub fn new_root(&self) -> BabyBear {
        self.participant.rotated.new_root()
    }
}

// ============================================================================
// Errors
// ============================================================================

/// Why folding a finalized-turn chain failed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TurnChainError {
    /// Fewer than 2 turns — a chain fold needs at least 2.
    TooFewTurns {
        /// How many were supplied.
        count: usize,
    },
    /// **The temporal tooth.** Turn `index` does not continue the chain: its
    /// `old_root` is not the previous turn's `new_root`. The finalized order is
    /// broken (reordered / dropped / inserted turn).
    ChainBreak {
        /// The turn that breaks continuity.
        index: usize,
        /// The root the previous turn produced.
        expected_old_root: u32,
        /// The root this turn claims to consume.
        found_old_root: u32,
    },
    /// **The WIDE temporal tooth.** Turn `index` does not continue the chain at the 8-felt
    /// (~124-bit) anchor: its `wide_old_root8` is not the previous turn's `wide_new_root8`. For a
    /// WIDE welded leg the single-felt rotated commit PIs (34/35) are RETIRED to zero (the 8-felt
    /// wide commit is the sole binding), so continuity is bound at the 8-felt anchor, not the felt.
    WideChainBreak {
        /// The turn that breaks 8-felt continuity.
        index: usize,
    },
    /// A WIDE welded leg is missing its 8-felt commit anchor (PI vector too short for the wide
    /// tail) — a narrow leg presented to the wide fold. Fail-closed.
    MissingWideAnchor {
        /// The turn whose leg lacks the wide tail.
        index: usize,
    },
    /// A turn's per-cell whole-turn proof failed to verify (host admission or
    /// the in-circuit leaf re-proof).
    TurnProofInvalid {
        /// The turn whose proof failed.
        index: usize,
        /// The underlying verification error.
        reason: String,
    },
    /// A recursion layer (leaf wrap or aggregation) failed.
    RecursionFailed {
        /// What failed.
        reason: String,
    },
    /// **The VK pin refused the root.** The root proof's verifier-key
    /// fingerprint (its verifier-reconstruction inputs, incl. the
    /// preprocessed commitment binding the root circuit's op-list) does not
    /// match the caller's trust anchor — this is a proof of a DIFFERENT
    /// circuit, exactly the from-scratch-prover route the pin closes.
    VkFingerprintMismatch {
        /// The anchor fingerprint the caller expected (hex).
        expected: String,
        /// The fingerprint the presented root actually has (hex).
        found: String,
    },
    /// **The claimed chain publics are unattested.** Either the Lean-emitted binding descriptor
    /// proof failed, its scalar endpoint/count PIs disagreed with the carried wide claim, or the
    /// recursion root's exposed wide segment disagreed with that claim — a relabeled splice.
    ClaimedPublicsUnattested {
        /// The underlying verification error.
        reason: String,
    },
    /// **The byte envelope did not decode.** A serialized [`WholeChainProofBytes`]
    /// was malformed, carried an unsupported version, or its embedded proof
    /// components failed to postcard-decode into the concrete recursion proof
    /// types. Fail-closed: a non-decoding envelope is refused, never half-read.
    EnvelopeDecode {
        /// What went wrong while decoding.
        reason: String,
    },
}

impl core::fmt::Display for TurnChainError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            TurnChainError::TooFewTurns { count } => {
                write!(f, "turn chain needs >= 2 turns, got {count}")
            }
            TurnChainError::ChainBreak {
                index,
                expected_old_root,
                found_old_root,
            } => write!(
                f,
                "turn {index} breaks the finalized chain: old_root {found_old_root} != \
                 previous turn's new_root {expected_old_root} (order tampered)"
            ),
            TurnChainError::WideChainBreak { index } => write!(
                f,
                "turn {index} breaks the finalized chain at the 8-felt (~124-bit) anchor: \
                 wide_old_root8 != previous turn's wide_new_root8 (order tampered)"
            ),
            TurnChainError::MissingWideAnchor { index } => write!(
                f,
                "turn {index} leg is missing its 8-felt wide commit anchor (narrow leg in the \
                 wide fold) — refused"
            ),
            TurnChainError::TurnProofInvalid { index, reason } => {
                write!(f, "turn {index} proof invalid: {reason}")
            }
            TurnChainError::RecursionFailed { reason } => {
                write!(f, "recursion failed: {reason}")
            }
            TurnChainError::VkFingerprintMismatch { expected, found } => write!(
                f,
                "root verifier-key fingerprint {found} != trust anchor {expected} \
                 (a proof of a different circuit — refused)"
            ),
            TurnChainError::ClaimedPublicsUnattested { reason } => write!(
                f,
                "claimed chain publics are not attested by the carried binding proof \
                 (relabeled genesis/final/num_turns/digest): {reason}"
            ),
            TurnChainError::EnvelopeDecode { reason } => write!(
                f,
                "whole-chain proof byte envelope did not decode: {reason}"
            ),
        }
    }
}

impl std::error::Error for TurnChainError {}

// ============================================================================
// Trace generation for the chain binding.
// ============================================================================
//
// Bucket-F (PATH-PRESERVE Phase 5a): the v1 `generate_chain_trace` /
// `generate_chain_trace_unchecked` (which read v1 OLD/NEW_COMMIT at PI 0/4) are DELETED.
// The rotated fold builds its binding trace via `generate_chain_trace_rotated`, using PI 34/35
// for narrow legs and the deployed wide anchor's head lane when those scalar PIs are retired.

/// The scalar endpoint projection consumed by the turn-chain descriptor.
///
/// Narrow legs publish their scalar ROTATED roots at PI 34/35. Wide legs deliberately retire those
/// PIs to zero and publish genuine 8-felt anchors instead, so the descriptor consumes lane 0 of the
/// same [`turn_anchors8`] values the recursion segment binds. This keeps the scalar descriptor
/// meaningful on the deployed wide path without changing its Lean-authored constraints.
fn binding_roots(t: &FinalizedTurn) -> (BabyBear, BabyBear) {
    let (old8, new8) = turn_anchors8(t);
    (old8[0], new8[0])
}

/// The host-side mirror of one descriptor leaf / aggregation node's ORDERED SEGMENT
/// (the base-field values it exposes through the `expose_claim` table):
/// `[first_old8(8), last_new8(8), count(1), acc_0..acc_{W-1}(W)]` (`W = SEG_DIGEST_WIDTH`). The
/// prover folds these the SAME way the in-circuit combine does so it knows the root segment
/// (hence the chain claims) to carry. The FAITHFUL-FLOOR lift widened the state endpoints from
/// single felts to the 8-felt (~124-bit) anchors.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct HostSeg {
    pub first_old8: [BabyBear; SEG_ANCHOR_WIDTH],
    pub last_new8: [BabyBear; SEG_ANCHOR_WIDTH],
    pub count: BabyBear,
    /// The multi-felt Poseidon2 ordered-history digest (codex #3, widened to 8 lanes).
    pub acc: [BabyBear; SEG_DIGEST_WIDTH],
}

/// The 8-felt state anchors a finalized turn publishes, sourced the SAME way the in-circuit
/// descriptor leaf binds them (so the host root segment equals what the root proof exposes):
///   - a WIDE / wide-welded leg (descriptor carries a wide-weld suffix AND a 16-felt PI tail)
///     sources the GENUINE 8-felt `wide_old_root8`/`wide_new_root8` (~124-bit faithful anchor);
///   - a narrow leg BROADCASTS its single rotated commit felt (PI 34/35) across all eight lanes
///     (the back-compat fallback — no entropy gain, structural type-compat only; the in-circuit
///     leaf replicates the SAME bound PI target across the eight lanes, matching this host value).
pub(crate) fn turn_anchors8(
    t: &FinalizedTurn,
) -> ([BabyBear; SEG_ANCHOR_WIDTH], [BabyBear; SEG_ANCHOR_WIDTH]) {
    let leg = &t.participant.rotated;
    if leg_is_wide_anchored(leg) {
        // Safe: `leg_is_wide_anchored` already confirmed the 16-felt wide tail is present.
        (
            leg.wide_old_root8().expect("wide leg carries old8"),
            leg.wide_new_root8().expect("wide leg carries new8"),
        )
    } else {
        let (o, n) = (leg.old_root(), leg.new_root());
        ([o; SEG_ANCHOR_WIDTH], [n; SEG_ANCHOR_WIDTH])
    }
}

/// Whether a leg genuinely publishes the 8-felt wide anchors at its PI tail (a WIDE / wide-welded
/// leg), as opposed to a narrow leg whose `[n-16..n]` PIs are NOT the wide commit.
///
/// **H0 DEPLOYED-WIDE FLIP:** the discriminator is now STRUCTURAL — a leg is wide-anchored iff its
/// PI vector carries the full 16-felt wide commit tail past the rotated prefix, i.e.
/// `len >= WIDE_PI_COUNT` (62). This SUPERSEDES the prior weld-suffix name check, which only
/// recognized the `-umem*-wide-welded-staged` cohort: the BARE wide registry members
/// (`generate_rotated_effect_vm_descriptor_and_trace_wide`, the deployed default the
/// `mint_*` recipes now mint) share the narrow members' NAMES — the wide-ness lives in the trace
/// geometry + the 16 appended PIs, NOT the name — so a name check cannot see them. The length check
/// is a strict superset: every wide variant (bare / single-domain-welded / multi-domain-welded /
/// cap-open-tb) appends the wide tail LAST and lands at `>= 62`, while every narrow leg (rotated
/// prefix 46, custom 50, cap-open-tb 49, grow-gate 47) stays `<= 50`. It is the SAME predicate the
/// in-circuit leaf branches on (`prove_descriptor_leaf_rotated_with_segment_config`), so host and
/// circuit agree lane-for-lane on which legs read the genuine ~124-bit anchors.
pub(crate) fn leg_is_wide_anchored(
    leg: &crate::joint_turn_aggregation::RotatedParticipantLeg,
) -> bool {
    use dregg_circuit::effect_vm::trace_rotated::WIDE_PI_COUNT;
    leg.public_inputs.len() >= WIDE_PI_COUNT
}

/// The per-turn (descriptor-leaf) segment: `first_old8`/`last_new8` are the leg's 8-felt anchors
/// ([`turn_anchors8`]), `count = 1`, `acc = commit([first_old8 ++ last_new8])` (16 inputs) — the
/// SAME seed [`seg_poseidon_commit`] computes at the leaf wrap.
pub(crate) fn leaf_seg(
    old8: [BabyBear; SEG_ANCHOR_WIDTH],
    new8: [BabyBear; SEG_ANCHOR_WIDTH],
) -> HostSeg {
    let mut inputs = Vec::with_capacity(2 * SEG_ANCHOR_WIDTH);
    inputs.extend_from_slice(&old8);
    inputs.extend_from_slice(&new8);
    HostSeg {
        first_old8: old8,
        last_new8: new8,
        count: BabyBear::ONE,
        acc: seg_poseidon_commit_host(&inputs),
    }
}

/// Combine two adjacent segments (the host mirror of the aggregation combine):
/// continuity `l.last_new8 == r.first_old8` lane-by-lane (caller-checked upstream as `ChainBreak`),
/// `first_old8 = l.first_old8`, `last_new8 = r.last_new8`, `count = l.count + r.count`,
/// `acc = commit(l.acc ++ r.acc)` (order-sensitive: l before r).
pub(crate) fn combine_seg(l: HostSeg, r: HostSeg) -> HostSeg {
    let mut acc_inputs = Vec::with_capacity(2 * SEG_DIGEST_WIDTH);
    acc_inputs.extend_from_slice(&l.acc);
    acc_inputs.extend_from_slice(&r.acc);
    HostSeg {
        first_old8: l.first_old8,
        last_new8: r.last_new8,
        count: l.count + r.count,
        acc: seg_poseidon_commit_host(&acc_inputs),
    }
}

/// Fold one LEVEL VECTOR of host segments through EXACTLY [`aggregate_tree`]'s balanced loop
/// (pair adjacent left-to-right; odd tail promoted unchanged to the END of the next level) —
/// extracted so the balanced root-segment mirror AND the streaming mirror's window fold share
/// the ONE loop shape the in-circuit tree runs.
fn fold_host_segs_balanced(mut level: Vec<HostSeg>) -> HostSeg {
    debug_assert!(!level.is_empty());
    while level.len() > 1 {
        let mut next: Vec<HostSeg> = Vec::with_capacity(level.len().div_ceil(2));
        let mut i = 0;
        while i + 1 < level.len() {
            next.push(combine_seg(level[i], level[i + 1]));
            i += 2;
        }
        if i < level.len() {
            next.push(level[i]);
        }
        level = next;
    }
    level[0]
}

/// The per-turn leaf segments in chain order — the level-0 vector both root-segment mirrors fold.
fn turn_leaf_segs(turns: &[&FinalizedTurn]) -> Vec<HostSeg> {
    turns
        .iter()
        .map(|t| {
            let (o8, n8) = turn_anchors8(t);
            leaf_seg(o8, n8)
        })
        .collect()
}

/// Fold the per-turn leaf segments into the ROOT segment using the SAME pairwise
/// left-to-right binary tree (with odd-element carry) that [`aggregate_tree`] runs
/// in-circuit — so the host-computed root `[first_old8, last_new8, count, acc]`
/// equals what the root proof exposes.
fn compute_root_segment(turns: &[&FinalizedTurn]) -> HostSeg {
    fold_host_segs_balanced(turn_leaf_segs(turns))
}

/// **THE ROOT BOARD WINDOW** — the `[first.IN ‖ last.OUT]` a board-window root will expose, and
/// the artifact's carried claim for it.
///
/// The pack the automatafl legs publish is INJECTIVE (`pack_injective_modp`, base-4 positional
/// with `packed < 4^15 < p`), so these two windows ARE the genesis and final positions: a light
/// client decodes the board in the clear and checks the win condition with no extra circuit.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BoardWindow {
    /// The FIRST turn's IN window — the state the chain started from.
    pub first_in: Vec<BabyBear>,
    /// The LAST turn's OUT window — the state the chain reached.
    pub last_out: Vec<BabyBear>,
}

/// Read a finalized turn's declared `(IN, OUT)` state windows off its custom bundle. `None` for a
/// turn that declares no window (every non-automatafl turn); `Err` for a turn whose declared
/// window its own PI vector cannot express (fail-closed — never zero-padded).
fn turn_board_window(t: &FinalizedTurn) -> Result<Option<(Vec<BabyBear>, Vec<BabyBear>)>, String> {
    use dregg_circuit::effect_vm::custom_state_binding::extract_custom_pi_board_window;
    let Some(CarrierWitness::Custom(bundle)) = &t.participant.rotated.carrier_witness else {
        return Ok(None);
    };
    let Some(binding) = bundle
        .descriptor_state_leaf
        .as_ref()
        .and_then(|src| src.board_window.as_ref())
    else {
        return Ok(None);
    };
    extract_custom_pi_board_window(&bundle.public_inputs, binding)
        .map(Some)
        .ok_or_else(|| {
            format!(
                "the declared board window {binding:?} is not expressible in the sub-proof's {} \
                 public inputs",
                bundle.public_inputs.len()
            )
        })
}

/// **THE HOST BOARD-WINDOW MIRROR** — fold the per-turn windows the way the in-circuit merge
/// will, and FAIL CLOSED before a single leaf is proven if the chain does not actually chain.
///
/// The in-circuit rule is `left.OUT == right.IN` at every node, which over a chain in order is
/// exactly `turn[i].OUT == turn[i+1].IN`; the root then exposes `[first.IN ‖ last.OUT]`. So a
/// forged mid (Leg A fed a board Leg R did not produce) or a substituted board between rounds is
/// an UNSAT node — hours of proving to discover. This mirror surfaces it in milliseconds, exactly
/// as the streaming-schedule guard does for the ordered digest.
///
/// A chain that MIXES windowed and unwindowed turns is refused: the merge cannot combine the two
/// shapes, and degrading to the plain combine would drop the seam.
/// The public face of [`compute_root_board_window`] — the HOST gate, runnable in milliseconds on a
/// chain of finalized turns without proving anything.
///
/// It is a MIRROR of the in-circuit rule, not a substitute for it: the soundness property is the
/// `connect` in the aggregation node (a disagreeing pair is UNSAT ⇒ no root ⇒ no verifying
/// artifact). This is what makes a forged mid cost milliseconds instead of hours, and what lets a
/// canary demonstrate the refusal without a full fold.
pub fn board_window_of_chain(
    turns: &[FinalizedTurn],
) -> Result<Option<BoardWindow>, TurnChainError> {
    let refs: Vec<&FinalizedTurn> = turns.iter().collect();
    compute_root_board_window(&refs)
}

/// **THE MIXED-WIDTH CLEAN-HANDOFF HOST MIRROR** — [`board_window_of_chain`] for a MULTI-ROUND
/// automatafl turn, whose chain has ONE `C_last → R` boundary where the window width changes (the
/// conflict braid's 32-lane RoundState windows hand off to the clean round's narrower `[board ‖
/// marks ‖ auto]` windows).
///
/// It mirrors the in-circuit fold EXACTLY: the conflict sub-chain folds uniformly (whole 32-lane
/// window seam), the clean sub-chain folds uniformly (whole `r_window`-lane seam), and at the single
/// width-change boundary only the leading `clean_handoff` `board ‖ marks` lanes are compared (the
/// analogue of [`board_window_clean_handoff_connects`], which connects the prefix and DROPS `locked
/// ‖ waiting ‖ auto`). The root window is the MIXED `[C_first.IN ‖ R_last.OUT]` — genesis RoundState
/// (32 lanes) and the clean round's final state (`r_window` lanes). Fail-closed at the boundary
/// exactly as the in-circuit connect is UNSAT on a `board ‖ marks` prefix disagreement — the
/// forged-mid analogue at the C→R handoff — surfaced in milliseconds instead of hours of proving.
///
/// A UNIFORM chain (no width change) is accepted too and behaves identically to
/// [`board_window_of_chain`]; MORE than one width change is refused (the mirror models a single
/// clean handoff).
pub fn board_window_of_chain_with_clean_handoff(
    turns: &[FinalizedTurn],
    clean_handoff: usize,
) -> Result<Option<BoardWindow>, TurnChainError> {
    let refs: Vec<&FinalizedTurn> = turns.iter().collect();
    compute_root_board_window_inner(&refs, Some(clean_handoff))
}

fn compute_root_board_window(
    turns: &[&FinalizedTurn],
) -> Result<Option<BoardWindow>, TurnChainError> {
    compute_root_board_window_inner(turns, None)
}

/// The host board-window mirror, generalized over the C→R clean handoff. `clean_handoff == None` is
/// the UNIFORM chain (the deployed two-leg / conflict fold — every turn's window is the same width,
/// each seam the whole window). `clean_handoff == Some(h)` allows ONE width-change boundary, where
/// only the leading `h` `board ‖ marks` lanes are compared. Both share the pure
/// [`fold_declared_windows`] core, so the mixed path is not a second implementation of the seam.
fn compute_root_board_window_inner(
    turns: &[&FinalizedTurn],
    clean_handoff: Option<usize>,
) -> Result<Option<BoardWindow>, TurnChainError> {
    let mut wins: Vec<(Vec<BabyBear>, Vec<BabyBear>)> = Vec::with_capacity(turns.len());
    let mut declared = 0usize;
    for (i, t) in turns.iter().enumerate() {
        match turn_board_window(t)
            .map_err(|reason| TurnChainError::TurnProofInvalid { index: i, reason })?
        {
            Some(w) => {
                declared += 1;
                wins.push(w);
            }
            None => wins.push((Vec::new(), Vec::new())),
        }
    }
    if declared == 0 {
        return Ok(None);
    }
    if declared != turns.len() {
        return Err(TurnChainError::RecursionFailed {
            reason: format!(
                "board-window chain: {declared} of {} turns declare a state window — a chain \
                 cannot mix board-window and plain turns (the merge has no combine for the mixed \
                 shape); refused fail-closed",
                turns.len()
            ),
        });
    }
    fold_declared_windows(&wins, clean_handoff)
        .map(Some)
        .map_err(|reason| TurnChainError::RecursionFailed { reason })
}

/// **THE PURE WINDOW-FOLD CORE** — fold the per-turn `(IN, OUT)` windows (already gathered, all
/// declared, in chain order) the way the in-circuit aggregation tree will, returning the root
/// `[first.IN ‖ last.OUT]` or the reason a seam does not chain. Shared by the uniform and
/// clean-handoff host mirrors and unit-tested directly (no leg minting), so the mixed C→R seam is
/// exercised in milliseconds.
///
///   * `clean_handoff == None` — the UNIFORM chain: every window is the same width `w` and each seam
///     is the whole-window `turn[i].OUT == turn[i+1].IN`. Byte-for-byte the pre-generalization
///     behavior (the "board-window seam broken" phrasing the deployed canaries match is preserved).
///   * `clean_handoff == Some(h)` — the MIXED chain: uniform widths EXCEPT at (at most) ONE boundary
///     (the `C_last → R` handoff), where only the leading `h` `board ‖ marks` lanes are compared —
///     `locked ‖ waiting ‖ auto` are dropped, consumed at the clean round, exactly as
///     `board_window_clean_handoff_connects` drops them in-circuit.
fn fold_declared_windows(
    wins: &[(Vec<BabyBear>, Vec<BabyBear>)],
    clean_handoff: Option<usize>,
) -> Result<BoardWindow, String> {
    // Per-turn self-consistency: a turn consumes and produces a same-width state (a conflict round is
    // 32/32, a clean round r/r). A half-empty or lopsided window cannot express the fold.
    for (i, (win_in, win_out)) in wins.iter().enumerate() {
        if win_in.is_empty() || win_out.is_empty() {
            return Err(format!(
                "board-window chain: turn {i} declares an empty window half"
            ));
        }
        if win_in.len() != win_out.len() {
            return Err(format!(
                "board-window chain: turn {i} declares a {}/{}-lane window (a turn's IN and OUT \
                 widths must agree)",
                win_in.len(),
                win_out.len()
            ));
        }
    }
    match clean_handoff {
        None => {
            let w = wins[0].0.len();
            for (i, (win_in, win_out)) in wins.iter().enumerate() {
                if win_in.len() != w || win_out.len() != w {
                    return Err(format!(
                        "board-window chain: turn {i} declares a {}/{} -lane window, chain width \
                         is {w} (a mixed-width chain needs the clean-handoff mirror)",
                        win_in.len(),
                        win_out.len()
                    ));
                }
            }
            // THE SEAM, host-side: turn i's OUT must be turn i+1's IN, lane for lane.
            for i in 0..wins.len() - 1 {
                if wins[i].1 != wins[i + 1].0 {
                    return Err(format!(
                        "board-window seam broken: turn {i}'s OUT window does not equal turn {}'s \
                         IN window. The in-circuit `connect` would be UNSAT (no root, no verifying \
                         artifact) — refusing before proving. This is the forged-mid / \
                         substituted-board case the seam exists to catch.",
                        i + 1
                    ));
                }
            }
        }
        Some(h) => {
            if h == 0 {
                return Err("clean-handoff width must be nonzero".to_string());
            }
            let mut boundaries = 0usize;
            for i in 0..wins.len() - 1 {
                let wl = wins[i].1.len();
                let wr = wins[i + 1].0.len();
                if wl == wr {
                    // A uniform seam INSIDE a side (conflict→conflict or clean→clean): whole window.
                    if wins[i].1 != wins[i + 1].0 {
                        return Err(format!(
                            "board-window seam broken: turn {i}'s OUT window does not equal turn \
                             {}'s IN window (uniform boundary inside a fold side).",
                            i + 1
                        ));
                    }
                } else {
                    // THE CLEAN HANDOFF — exactly one width change; compare the `board ‖ marks`
                    // prefix only (the C→R analogue of the mid seam).
                    boundaries += 1;
                    if boundaries > 1 {
                        return Err(
                            "board-window chain has more than one window-width change — the \
                             clean-handoff mirror models a SINGLE C->R boundary; refused fail-closed"
                                .to_string(),
                        );
                    }
                    if h > wl.min(wr) {
                        return Err(format!(
                            "clean-handoff prefix {h} exceeds the min window width {} at the C->R \
                             boundary {i}->{}",
                            wl.min(wr),
                            i + 1
                        ));
                    }
                    if wins[i].1[..h] != wins[i + 1].0[..h] {
                        return Err(format!(
                            "clean-handoff seam broken: the board||marks prefix ({h} lanes) of turn \
                             {i}'s OUT window does not equal turn {}'s IN window. The in-circuit \
                             `board_window_clean_handoff_connects` would be UNSAT — the forged-mid \
                             analogue at the C->R handoff, refused before proving.",
                            i + 1
                        ));
                    }
                }
            }
        }
    }
    Ok(BoardWindow {
        first_in: wins[0].0.clone(),
        last_out: wins[wins.len() - 1].1.clone(),
    })
}

/// The host mirror of [`aggregate_tree_streaming`]'s schedule over [`HostSeg`]s. Because the
/// streaming schedule reproduces the balanced tree's EXACT shape (witnessed exhaustively by the
/// `streaming_fold_tests`), this equals [`fold_host_segs_balanced`] — and the streaming prover
/// asserts exactly that, fail-closed, before proving a single leaf.
fn fold_host_segs_streaming(segs: &[HostSeg], window: usize) -> HostSeg {
    let folded: Result<HostSeg, core::convert::Infallible> = streaming_fold_schedule(
        segs.len(),
        window,
        |i| Ok(segs[i]),
        |buf| Ok(fold_host_segs_balanced(buf)),
        |l, r| Ok(combine_seg(l, r)),
    );
    match folded {
        Ok(seg) => seg,
    }
}

/// [`compute_root_segment`]'s streaming twin: the root segment the STREAMING fold's root will
/// expose, computed host-side through the same schedule.
fn compute_root_segment_streaming(turns: &[&FinalizedTurn], window: usize) -> HostSeg {
    fold_host_segs_streaming(&turn_leaf_segs(turns), window)
}

/// Build the Lean-emitted turn-chain descriptor witness from the scalar projection returned by
/// [`binding_roots`], rather than the retired v1 OLD/NEW_COMMIT slots (PI 0/4). Trace generation is
/// legitimate Rust; every constraint interpreted over it comes from
/// `dregg-turn-chain-binding-v2`.
fn generate_chain_trace_rotated(
    turns: &[&FinalizedTurn],
) -> Result<(Vec<Vec<BabyBear>>, Vec<BabyBear>, BabyBear), TurnChainError> {
    if turns.len() < 2 {
        return Err(TurnChainError::TooFewTurns { count: turns.len() });
    }
    for i in 1..turns.len() {
        let (_, prev_new) = binding_roots(turns[i - 1]);
        let (this_old, _) = binding_roots(turns[i]);
        if prev_new != this_old {
            return Err(TurnChainError::ChainBreak {
                index: i,
                expected_old_root: prev_new.0,
                found_old_root: this_old.0,
            });
        }
    }
    let root_pairs: Vec<(BabyBear, BabyBear)> =
        turns.iter().map(|turn| binding_roots(turn)).collect();
    let (trace, pis) = turn_chain_binding_witness(&root_pairs)
        .map_err(|reason| TurnChainError::RecursionFailed { reason })?;
    let digest = pis[3];
    Ok((trace, pis, digest))
}

// ============================================================================
// Per-turn leaf: the ROTATED descriptor batch re-proven recursion-compatibly.
// ============================================================================
//
// Bucket-F (PATH-PRESERVE Phase 5a): the v1 `prove_descriptor_leaf` (which re-proved the
// 186-column `EffectVmDescriptorAir` uni-STARK over a `FinalizedTurn::base_trace`) is DELETED.
// The mandatory per-turn leaf is the ROTATED multi-table `Ir2BatchProof` carried on
// `participant.rotated`, wrapped in-circuit by `prove_descriptor_leaf_rotated_with_config`
// below — `FinalizedTurn` no longer carries a v1 `base_trace`, so there is nothing for the v1
// leaf to consume.

/// The FRI knobs the production IR-v2 descriptor batch (`descriptor_ir2::ir2_config`) is
/// minted under: `log_blowup = 6`, `log_final_poly_len = 0`, `commit_pow = 0`,
/// `query_pow = 16` (19 queries, max_log_arity 3 — both read from the proof in-circuit, so
/// they need no entry here). The native-batch leaf-wrap's in-circuit FRI verifier is built
/// with `FriVerifierParams` matching these (via
/// [`create_recursion_config_for_inner_fri`]) so an `ir2_config` proof verifies as-is — the
/// SIDESTEP (C3 PART 2a): the inner proof keeps its production FRI engine; only the
/// recursion verifier's params are retargeted. The leaf-wrap OUTPUT is a standard
/// recursion-config (`log_blowup = 3`, 38-query) proof.
///
/// ⚑ **THESE ARE `pub` NOW, AND THAT CLOSES A HOLE IN THE PARAMS GATE.** They were private, so
/// `circuit-prove/tests/fri_params_soundness_budget.rs`'s `ir2_leaf_wrap_config` row could not read
/// the consts the config ACTUALLY reads — it reconstructed the row from `IR2_FRI_*` + `INNER_FRI_*`
/// instead. Moving `IR2_INNER_LOG_BLOWUP` alone would therefore have changed what the deployed
/// prover runs while the gate went on judging a config assembled out of other constants. A
/// soundness knob that no gate can read is not gated.
///
/// ⚑ They now LIVE in `dregg-recursion-verify::config` beside the config builder that reads
/// them, and are re-exported here so the params gate's existing `ivc_turn_chain::IR2_INNER_*`
/// paths still resolve. A verify-only consumer must be able to reach the knobs its own verify
/// runs at without linking the prover.
pub use dregg_recursion_verify::config::{
    IR2_INNER_COMMIT_POW_BITS, IR2_INNER_LOG_BLOWUP, IR2_INNER_LOG_FINAL_POLY_LEN,
    IR2_INNER_QUERY_POW_BITS,
};

/// THREAD 1 (C3 cutover) — the rotated multi-table `Ir2BatchProof` native-batch leaf-wrap.
///
/// Re-prove one rotated finalized-turn DESCRIPTOR batch (`transferVmDescriptor2R24` &c — the
/// IR-v2 multi-table `Ir2BatchProof`: main + chip + range + memory + map tables, the degree-7
/// S-box, LogUp buses) as a recursion-compatible BatchStark leaf, with the descriptor PI
/// prefix (carrying the chain roots) bound in-circuit by the wrap layer. The leaf's in-circuit
/// constraint evaluation is the REAL `Ir2Air` set's `eval_folded_circuit` per instance — NOT
/// the recursion's fixed `CircuitTablesAir[Const/Public/Alu]+NPO` reconstruction.
///
/// **How the two walls of the prior pass are crossed:**
///   1. **Proof-type wall** — `Ir2BatchProof = p3_batch_stark::BatchProof` (bare native) is
///      no longer wrapped as `RecursionInput::BatchStark` (which holds the circuit-prover
///      `BatchStarkProof` wrapper). It rides the NEW `RecursionInput::NativeBatchStark`
///      variant, whose backend arm allocates verifier inputs from the BARE batch proof
///      (`BatchStarkVerifierInputsBuilder::allocate`, which already takes
///      `&p3_batch_stark::BatchProof`) and runs the caller's `&[Ir2Air]` straight through the
///      generic `verify_batch_circuit`.
///   2. **Config wall** — the production `Ir2BatchProof` (`ir2_config`: log_blowup 6, 19
///      queries, 16 query-PoW) is verified in-circuit by a recursion config whose
///      `FriVerifierParams` are retargeted to `ir2_config`'s FRI knobs
///      (`create_recursion_config_for_inner_fri`); `num_queries` + folding arity are read
///      from the inner proof structure in-circuit, so only log_blowup / pow need matching.
///      The MMCS hash / compress / challenger / field are byte-identical between the two
///      configs already (both `PaddingFreeSponge`+`TruncatedPermutation` over Poseidon2-w16,
///      DuplexChallenger, BabyBear-deg4), which is what makes the SIDESTEP a verifier-param
///      retarget rather than a re-prove.
///
/// The wrap layer's output is a standard recursion-config batch proof (the same type the v1
/// `prove_descriptor_leaf` wrap and the aggregation tree consume), so a rotated descriptor
/// leaf now folds into the SAME `aggregate_tree` / chain machinery.
///
/// **STATUS (2026-06-13): GREEN — all three walls crossed.** This compiles, runs, builds the
/// in-circuit verifier, PASSES in-circuit FRI MMCS verification, the recursion verifier circuit's
/// own `WitnessChecks` LogUp bus BALANCES, and the wrapped root self-verifies in-circuit. The
/// final wall was the foreign-multi-table-LogUp-leaf `WitnessChecks` accounting: a descriptor
/// public input asserted equal to the zero constant put it in `ExprId::ZERO`'s connect-class, so
/// `WitnessId(0)` had TWO bus creators (the zero `Const` AND a `Public` op) → net +779 on the
/// all-zero tuple (config/arity-INDEPENDENT). The fork now demotes such a duplicate `Public` to a
/// bus READER (`p3_circuit::PreprocessedColumns::dup_public_outputs` → multiplicity −1 in
/// `get_airs_and_degrees_with_prep`), which both restores the one-creator-per-witness invariant
/// AND soundly binds the public value to the zero constant. The transfer leaf (3 instances: main
/// w=331 / 38 PV / 50 global lookups · chip w=364 / 2 global · byte w=2 / 1 global) folds GREEN;
/// the smoke test `rotation_batchstark_leaf_smoke.rs` asserts it (no longer `#[ignore]`'d).
///
/// **The inner proof is a `BatchProof<DreggRecursionConfig>` (SIDESTEP option a):** the
/// rotated prover mints the IR-v2 batch under the recursion config TYPE (with `ir2`'s FRI
/// knobs, via [`dregg_circuit::descriptor_ir2::prove_vm_descriptor2_for_config`] +
/// [`create_recursion_config_for_inner_fri`]) so the in-circuit verifier consumes it with no
/// cross-config type mismatch. `RecursionInput::NativeBatchStark.proof` is
/// `&p3_batch_stark::BatchProof<SC>` with `SC = DreggRecursionConfig`, so the inner proof and
/// the recursion pipeline share one config type. Use
/// [`ir2_airs_and_common_for_config`](dregg_circuit::descriptor_ir2::ir2_airs_and_common_for_config)
/// to obtain the matching `(airs, table_public_inputs, common)` triple.
pub fn prove_descriptor_leaf_rotated(
    desc: &dregg_circuit::descriptor_ir2::EffectVmDescriptor2,
    proof: &Ir2BatchProof<DreggRecursionConfig>,
    descriptor_pis: &[BabyBear],
) -> Result<RecursionOutput<DreggRecursionConfig>, String> {
    prove_descriptor_leaf_rotated_with_config(desc, proof, descriptor_pis, &ir2_leaf_wrap_config())
}

/// The self-consistent recursion config the rotated native-batch leaf-wrap runs at: its FRI
/// engine (StarkConfig PCS + in-circuit `FriVerifierParams`) is set to `ir2_config`'s knobs
/// (log_blowup 6, max_log_arity 3, 19 queries, 16 query-PoW), so the INNER proof is minted,
/// VERIFIED in-circuit, and the OUTPUT proven all at ONE FRI engine — the Merkle path lengths
/// the verifier circuit allocates match the siblings the inner proof carries. The inner proof
/// fed to [`prove_descriptor_leaf_rotated`] must be minted under THIS config (see
/// `descriptor_ir2::prove_vm_descriptor2_for_config`).
///
/// ⚑ The builder moved to `dregg-recursion-verify::config` with the constants it reads: a node
/// verifying a fold ROOT must run at this exact engine, and it must be able to reach it without
/// linking the prover. Re-exported here so every existing `ivc_turn_chain::ir2_leaf_wrap_config`
/// call site resolves to the SAME function — not a second one that happens to agree.
pub use dregg_recursion_verify::config::ir2_leaf_wrap_config;

/// ⚑⚑ **THE ENGINE EVERY LAYER ABOVE A TURN-CHAIN LEAF RUNS AT** — every aggregation node, the
/// root, and the native verify of that root. It is the fixed point of
/// [`recursion_layer_over`], i.e. `create_recursion_config()`.
///
/// ⚠ **This is what [`ir2_leaf_wrap_config`] used to answer, and it is no longer the same
/// object.** A leaf wrap verifies its child (the IR-v2 descriptor batch) at
/// `ir2_leaf_wrap_config`'s engine but MINTS at this one, so the child's in-circuit verification
/// is bit-for-bit unchanged while the wrap's own committed LDE falls 8×. A consumer that pins a
/// root's config must pin THIS one; `ir2_leaf_wrap_config()` names an engine that no proof in a
/// whole-chain artifact is minted under any more.
pub fn turn_chain_root_config() -> DreggRecursionConfig {
    dregg_recursion_verify::config::recursion_tower_root_config()
}

/// ⚑⚑ **THE ENGINE A BINDING / FOLD NODE RUNS AT, DERIVED — never handed in.**
///
/// [`recursion_layer_over`] is the one tower rule: a layer VERIFIES its child at the child's own
/// MINT engine and MINTS at the recursion engine. A LEAF applies it once, over the IR-v2 descriptor
/// batch (`ir2_leaf_wrap_config()`), and every leaf minter in this crate already does that
/// internally. A NODE that folds two leaves sits one layer higher again, so it applies the rule
/// TWICE — which is exactly `recursion_tower_root_config`'s own derivation, and therefore the
/// rule's fixed point ([`turn_chain_root_config`]).
///
/// ⚠ **THE DRIFT THIS EXISTS TO KILL** (opened by `c88e52cbd`, "the leaf wrap mints at its OWN
/// blowup"). Before that split a leaf VERIFIED and MINTED at one engine, so a node folding leaves
/// could be handed the same `ir2_leaf_wrap_config()` its children were built from and it worked by
/// coincidence. A leaf now EMITS at `recursion_layer_over`'s mint knobs (log_blowup 3, 38 queries),
/// so a node built at `ir2_leaf_wrap_config()` (log_blowup 6) builds a verification circuit
/// expecting FRI Merkle paths three levels longer than its children carry, and
/// `build_and_prove_aggregation_layer_with_expose` returns
/// `InvalidProofShape("Fewer siblings in proof than op_ids provided")`.
///
/// That is an OPERATIONAL fault, and it is the worst possible one to leave on this rail: on a
/// forgery tooth a bare `must_refuse` reads it as "the forgery was rejected", so an honest pole
/// goes RED while every negative pole beside it stays GREEN measuring nothing. The deployed chain
/// prover was updated at the split (it derives `fold_config` at each `prove_chain_core_*`); the
/// twenty-two standalone binding nodes and every test that calls one were not.
///
/// So the nodes DERIVE. `config` means, for a binding node exactly as for a leaf minter, *the
/// engine my children's inner IR-v2 batch was minted at* — no call site names an engine, and none
/// can be one layer off again.
pub fn fold_layer_over_leaves(ir2_batch_config: &DreggRecursionConfig) -> DreggRecursionConfig {
    recursion_layer_over(&recursion_layer_over(ir2_batch_config))
}

/// [`prove_descriptor_leaf_rotated`] under an explicit recursion config (the inner proof must
/// have been minted under the SAME config — same FRI engine). Exposed so the smoke test +
/// future chain wiring share one config object for mint + wrap + output-verify.
pub fn prove_descriptor_leaf_rotated_with_config(
    desc: &dregg_circuit::descriptor_ir2::EffectVmDescriptor2,
    proof: &Ir2BatchProof<DreggRecursionConfig>,
    descriptor_pis: &[BabyBear],
    config: &DreggRecursionConfig,
) -> Result<RecursionOutput<DreggRecursionConfig>, String> {
    // The verify-path triple under the SAME config TYPE as the inner proof: the present-table
    // `Ir2Air` set, the per-table public-input vectors (descriptor PIs on the main instance,
    // empty elsewhere), and the canonical symbolic `CommonData<DreggRecursionConfig>` (the
    // IR-v2 AIRs have NO preprocessed columns, so `common` is config-value-independent).
    let (airs, table_public_inputs, common) =
        dregg_circuit::descriptor_ir2::ir2_airs_and_common_for_config(
            desc,
            proof,
            descriptor_pis,
            config,
        )?;

    let input: RecursionInput<'_, DreggRecursionConfig, dregg_circuit::descriptor_ir2::Ir2Air> =
        RecursionInput::NativeBatchStark {
            airs: &airs,
            proof,
            common_data: &common,
            table_public_inputs,
        };

    let backend = create_recursion_backend();

    build_and_prove_next_layer::<DreggRecursionConfig, dregg_circuit::descriptor_ir2::Ir2Air, _, D>(
        &input,
        &recursion_layer_over(config),
        &backend,
        &ProveNextLayerParams::default(),
    )
    .map_err(|e| format!("rotated native-batch leaf-wrap failed: {e:?}"))
}

/// **RE-EXPOSE A CONTIGUOUS DESCRIPTOR-PI SLICE AS AN `expose_claim` CHANNEL.** Wrap an IR2
/// descriptor batch in-circuit (exactly like [`prove_descriptor_leaf_rotated_with_config`]) AND
/// re-expose its descriptor PIs `[pi_lo .. pi_lo+len)` through the `expose_claim` table so a parent
/// aggregation node can READ + `connect` them.
///
/// **Why this is necessary (the fork's PI-threading reality).** A bare leaf wrap does NOT surface
/// the inner descriptor's public inputs to a grandparent's combine hook: the in-circuit verifier
/// allocates each child PI as `circuit.public_input()` (`Op::Public`), which lands in the parent's
/// constraint-free `Public` PRIMITIVE table — and the next layer up threads child publics SOLELY
/// from each child `non_primitives[].public_values` (primitive-table values are never re-threaded).
/// So the inner PIs are CONSUMED one layer up and vanish before the combine hook ever runs. The
/// ONLY host-readable, FRI-bound scalar channel a child surfaces to its parent's
/// `air_public_targets` is a non-primitive `expose_claim` table's `public_values` — exactly what
/// [`prove_descriptor_leaf_rotated_with_segment`] uses for the chain segment. This helper does the
/// same for an arbitrary PI slice.
///
/// The deployed effect-VM custom leg (`customVmDescriptor2R24`) publishes its
/// `custom_proof_commitment` at IR2 PI slots 46..53 (the Lean `customPiExposure`, 8-felt); calling this
/// with `pi_lo = 46, len = 4` surfaces that claimed commitment as a 4-felt expose_claim the
/// per-turn fold ties to the custom sub-proof leaf's genuine in-circuit commitment (see
/// [`crate::joint_turn_recursive::prove_custom_binding_node`]).
pub fn prove_descriptor_leaf_with_pi_slice_expose(
    desc: &dregg_circuit::descriptor_ir2::EffectVmDescriptor2,
    proof: &Ir2BatchProof<DreggRecursionConfig>,
    descriptor_pis: &[BabyBear],
    config: &DreggRecursionConfig,
    pi_lo: usize,
    len: usize,
) -> Result<RecursionOutput<DreggRecursionConfig>, String> {
    if descriptor_pis.len() < pi_lo + len {
        return Err(format!(
            "PI-slice expose needs >= {} descriptor PIs to carry [{pi_lo}..{}), got {}",
            pi_lo + len,
            pi_lo + len,
            descriptor_pis.len()
        ));
    }
    let (airs, table_public_inputs, common) =
        dregg_circuit::descriptor_ir2::ir2_airs_and_common_for_config(
            desc,
            proof,
            descriptor_pis,
            config,
        )?;

    let input: RecursionInput<'_, DreggRecursionConfig, dregg_circuit::descriptor_ir2::Ir2Air> =
        RecursionInput::NativeBatchStark {
            airs: &airs,
            proof,
            common_data: &common,
            table_public_inputs,
        };

    let backend = create_recursion_backend();

    let expose = move |cb: &mut p3_circuit::CircuitBuilder<RecursionChallenge>,
                       apt: &[Vec<p3_recursion::Target>],
                       _vk_cap: &[p3_recursion::Target]| {
        let main = apt
            .first()
            .expect("descriptor leaf has a main instance carrying the descriptor PIs");
        debug_assert!(
            main.len() >= pi_lo + len,
            "main instance must carry the PI slice being re-exposed"
        );
        let claim: Vec<p3_recursion::Target> = (0..len).map(|k| main[pi_lo + k]).collect();
        cb.expose_as_public_output(&claim);
    };

    build_and_prove_next_layer_with_expose::<
        DreggRecursionConfig,
        dregg_circuit::descriptor_ir2::Ir2Air,
        _,
        D,
    >(
        &input,
        &recursion_layer_over(config),
        &backend,
        &ProveNextLayerParams::default(),
        Some(&expose),
    )
    .map_err(|e| format!("PI-slice-expose leaf-wrap failed: {e:?}"))
}

/// **THE SEGMENT-ACCUMULATOR DESCRIPTOR LEAF (the soundness-critical replacement for the
/// separate binding leaf).** Wrap one rotated finalized-turn descriptor batch in-circuit
/// AND emit its constant-size ordered SEGMENT through the `expose_claim` table, BOUND
/// in-circuit to the descriptor proof's REAL published chain roots:
///
///   `Seg = [first_old, last_new, count, acc]`
///     first_old := descriptor PI `V1_PI_COUNT`   (the rotated OLD-state commitment)
///     last_new  := descriptor PI `V1_PI_COUNT+1` (the rotated NEW-state commitment)
///     count     := 1
///     acc       := H(first_old, last_new)        (the per-turn ordered-history seed)
///
/// Because `first_old`/`last_new` are READ from the descriptor proof's own verified
/// `air_public_targets` (not free prover scalars), the segment is tied to the ACTUAL
/// execution this leaf re-proves. A prover cannot expose a segment whose endpoints differ
/// from the descriptor it folded. This is what closes the mixed-root hole: there is no
/// separate, swappable binding leaf — the whole-chain endpoints/digest are derived from the
/// real descriptor leaves and combined up the tree.
pub fn prove_descriptor_leaf_rotated_with_segment(
    desc: &dregg_circuit::descriptor_ir2::EffectVmDescriptor2,
    proof: &Ir2BatchProof<DreggRecursionConfig>,
    descriptor_pis: &[BabyBear],
    config: &DreggRecursionConfig,
) -> Result<RecursionOutput<DreggRecursionConfig>, String> {
    use dregg_circuit::effect_vm::trace_rotated::{V1_PI_COUNT, WIDE_PI_COUNT};

    // FAITHFUL-FLOOR: source the two 8-felt state anchors the SAME way [`turn_anchors8`] /
    // [`leg_is_wide_anchored`] do host-side, so the in-circuit segment is byte-identical to the host
    // root segment.
    //   - WIDE / wide-welded leg: the GENUINE 8-felt `wide_old_root8`/`wide_new_root8` ride at the
    //     PI tail `[n-16..n]`, bound in-circuit (their `PiBinding` makes a tampered anchor UNSAT);
    //   - narrow leg: BROADCAST the single rotated commit PIs (34/35) across all eight lanes —
    //     the SAME bound PI target replicated, matching the host broadcast in `turn_anchors8`.
    //
    // H0 DEPLOYED-WIDE FLIP: the wide branch is selected STRUCTURALLY (`n >= WIDE_PI_COUNT`), the
    // exact host mirror of [`leg_is_wide_anchored`] — the bare wide cohort (whose name equals its
    // narrow twin's) is now recognized by its 16-felt PI tail, not a weld suffix.
    let n = descriptor_pis.len();
    let wide = n >= WIDE_PI_COUNT;
    let old_first = n.saturating_sub(2 * SEG_ANCHOR_WIDTH);
    let new_first = n.saturating_sub(SEG_ANCHOR_WIDTH);

    let (airs, table_public_inputs, common) =
        dregg_circuit::descriptor_ir2::ir2_airs_and_common_for_config(
            desc,
            proof,
            descriptor_pis,
            config,
        )?;

    let input: RecursionInput<'_, DreggRecursionConfig, dregg_circuit::descriptor_ir2::Ir2Air> =
        RecursionInput::NativeBatchStark {
            airs: &airs,
            proof,
            common_data: &common,
            table_public_inputs,
        };

    // The expose hook: the main instance (instance 0) carries the descriptor PIs. Build the two
    // 8-felt anchor blocks (genuine wide tail, or replicated single felt for a narrow leg), the
    // per-turn digest seed over them, and expose the 8-wide segment.
    let expose = move |cb: &mut p3_circuit::CircuitBuilder<RecursionChallenge>,
                       apt: &[Vec<p3_recursion::Target>],
                       _vk_cap: &[p3_recursion::Target]| {
        let main = apt
            .first()
            .expect("descriptor leaf has a main instance with descriptor PIs");
        debug_assert!(
            main.len() > V1_PI_COUNT + 1,
            "descriptor PI vector must carry the rotated OLD/NEW commitments"
        );
        let (first_old8, last_new8): (Vec<p3_recursion::Target>, Vec<p3_recursion::Target>) =
            if wide {
                debug_assert!(
                    main.len() >= n,
                    "wide descriptor PI target vector must carry the 8-felt anchors at its tail"
                );
                (
                    (0..SEG_ANCHOR_WIDTH).map(|k| main[old_first + k]).collect(),
                    (0..SEG_ANCHOR_WIDTH).map(|k| main[new_first + k]).collect(),
                )
            } else {
                // Narrow: replicate the single bound PI target across all eight lanes (no zero
                // constants — keeps the sponge off the shared `WitnessId(0)` class entirely).
                (
                    vec![main[V1_PI_COUNT]; SEG_ANCHOR_WIDTH],
                    vec![main[V1_PI_COUNT + 1]; SEG_ANCHOR_WIDTH],
                )
            };
        let count = cb.define_const(RecursionChallenge::ONE);
        // The per-turn seed: a genuine multi-felt Poseidon2 commitment over the leaf's
        // REAL (descriptor-bound) 8-felt endpoints (16 inputs).
        let mut acc_inputs = Vec::with_capacity(2 * SEG_ANCHOR_WIDTH);
        acc_inputs.extend_from_slice(&first_old8);
        acc_inputs.extend_from_slice(&last_new8);
        let acc = seg_poseidon_commit(cb, &acc_inputs);
        let mut seg = Vec::with_capacity(SEG_SPINE_WIDTH);
        seg.extend_from_slice(&first_old8);
        seg.extend_from_slice(&last_new8);
        seg.push(count);
        seg.extend_from_slice(&acc);
        // THE SPINE BASE CASE. A leaf has no child cap to absorb; its own cap is absorbed by its
        // parent. See `leaf_vk_spine` for why this constant seed is sound.
        seg.extend_from_slice(&leaf_vk_spine(cb));
        debug_assert_eq!(seg.len(), SEG_SPINE_WIDTH);
        cb.expose_as_public_output(&seg);
    };

    prove_recursion_layer_auto_with_expose(&input, &recursion_layer_over(config), Some(&expose))
        .map_err(|e| format!("rotated native-batch segment leaf-wrap failed: {e}"))
}

/// **THE DUAL-EXPOSE CUSTOM LEG LEAF (deployed custom-binding half #1).** Wrap one rotated
/// `customVmDescriptor2R24` finalized-turn batch in-circuit exactly like
/// [`prove_descriptor_leaf_rotated_with_segment`] AND expose, through ONE `expose_claim` table,
/// BOTH:
///
///   * the constant-size ordered chain SEGMENT `[first_old8, last_new8, count, acc]` (lanes
///     `[0 .. SEG_WIDTH)`), bound in-circuit to the descriptor's real rotated roots,
///   * the LEAF VK SPINE seed (lanes `[SEG_VK_SPINE_FIRST .. SEG_SPINE_WIDTH)`), byte-identical to
///     the one [`prove_descriptor_leaf_rotated_with_segment`] exposes, and
///   * the leg's CLAIMED `custom_proof_commitment` at IR2 PI
///     `[CUSTOM_COMMIT_PI_LO .. CUSTOM_COMMIT_PI_LO+CUSTOM_COMMIT_LEN)` (lanes
///     `[SEG_SPINE_WIDTH .. SEG_SPINE_WIDTH+CUSTOM_COMMIT_LEN)`), read from the same FRI-bound
///     `air_public_targets` the segment endpoints come from.
///
/// The commitment lanes are APPENDED AFTER the segment AND the spine, so a downstream segment
/// consumer that reads only `[0 .. SEG_SPINE_WIDTH)` (the host segment tooth, the plain
/// `aggregate_tree` combine) sees the identical claim a
/// [`prove_descriptor_leaf_rotated_with_segment`] leaf would expose.
/// The appended commitment is consumed by exactly one parent —
/// [`crate::joint_turn_recursive::prove_custom_binding_node_segmented`] — which `connect`s it to
/// the custom sub-proof leaf's genuine commitment and RE-EXPOSES only the segment, so the binding
/// node's output is an ordinary segment leaf to `aggregate_tree`. This is the dual-claim leaf the
/// deployed light-client custom binding needs (the segment keeps the chain, the commitment lane
/// carries the claim to be bound).
pub fn prove_descriptor_leaf_dual_expose(
    desc: &dregg_circuit::descriptor_ir2::EffectVmDescriptor2,
    proof: &Ir2BatchProof<DreggRecursionConfig>,
    descriptor_pis: &[BabyBear],
    config: &DreggRecursionConfig,
) -> Result<RecursionOutput<DreggRecursionConfig>, String> {
    use crate::joint_turn_recursive::{CUSTOM_COMMIT_LEN, CUSTOM_COMMIT_PI_LO};
    // The custom carrier is the original instance of the dual-expose: its claim slice is the
    // `custom_proof_commitment` at IR2 PI [CUSTOM_COMMIT_PI_LO .. +CUSTOM_COMMIT_LEN). The
    // generalized [`prove_descriptor_leaf_dual_expose_at`] takes any `(pi_lo, len)` so the
    // FACTORY (`child_vk[8]`) and HATCHERY (`contract_hash[8]`) carriers can dual-expose their own
    // teeth slices through the SAME segment-preserving wrap; this thin wrapper keeps every existing
    // custom call working verbatim.
    prove_descriptor_leaf_dual_expose_at(
        desc,
        proof,
        descriptor_pis,
        config,
        CUSTOM_COMMIT_PI_LO,
        CUSTOM_COMMIT_LEN,
    )
}

/// **THE GENERALIZED DUAL-EXPOSE LEG LEAF** — [`prove_descriptor_leaf_dual_expose`] with the
/// CLAIM slice `[claim_pi_lo .. claim_pi_lo+claim_len)` parameterized instead of pinned to the
/// custom commitment lanes. It exposes, through ONE `expose_claim` table, BOTH:
///
///   * the constant-size ordered chain SEGMENT `[first_old8, last_new8, count, acc]` (lanes
///     `[0 .. SEG_WIDTH)`), bound in-circuit to the descriptor's real rotated roots,
///   * the LEAF VK SPINE seed (lanes `[SEG_VK_SPINE_FIRST .. SEG_SPINE_WIDTH)`), and
///   * the leg's CLAIMED teeth at IR2 PI `[claim_pi_lo .. claim_pi_lo+claim_len)` (lanes
///     `[SEG_SPINE_WIDTH .. SEG_SPINE_WIDTH+claim_len)`), read from the same FRI-bound
///     `air_public_targets`.
///
/// The custom carrier passes `(CUSTOM_COMMIT_PI_LO, CUSTOM_COMMIT_LEN)`; the FACTORY carrier passes
/// its `child_vk[8]` tail-PI offset; the HATCHERY carrier passes its `contract_hash[8]` tail-PI
/// offset. The binding nodes (`prove_factory_binding_node_segmented` /
/// `prove_hatchery_binding_node_segmented` / `prove_custom_binding_node_segmented`) `connect` the
/// appended teeth to the re-proven backing/attestation leaf and re-expose ONLY the segment, so the
/// node folds into [`aggregate_tree`] like any segment leaf.
///
/// CONSTRAINT (the implementer of the deployed factory/hatchery descriptor must honor): on a WIDE
/// descriptor the segment anchors are sourced from the LAST `2*SEG_ANCHOR_WIDTH` PIs
/// (`n - 2*SEG_ANCHOR_WIDTH`), so the teeth tail-PIs MUST sit at a FIXED low offset (ahead of the
/// wide rotated-commit anchors), exactly as the 8-felt custom commitment sits at 46..53 ahead of
/// them — never appended past `n - 2*SEG_ANCHOR_WIDTH`, or the wide-anchor sourcing would read
/// the teeth as the rotated commits.
pub fn prove_descriptor_leaf_dual_expose_at(
    desc: &dregg_circuit::descriptor_ir2::EffectVmDescriptor2,
    proof: &Ir2BatchProof<DreggRecursionConfig>,
    descriptor_pis: &[BabyBear],
    config: &DreggRecursionConfig,
    claim_pi_lo: usize,
    claim_len: usize,
) -> Result<RecursionOutput<DreggRecursionConfig>, String> {
    use dregg_circuit::effect_vm::trace_rotated::{V1_PI_COUNT, WIDE_PI_COUNT};

    let commit_hi = claim_pi_lo + claim_len;
    if descriptor_pis.len() < commit_hi {
        return Err(format!(
            "dual-expose leg needs >= {commit_hi} descriptor PIs to carry the claim slice at \
             [{claim_pi_lo}..{commit_hi}), got {}",
            descriptor_pis.len()
        ));
    }

    // FAITHFUL-FLOOR anchor sourcing — identical to `prove_descriptor_leaf_rotated_with_segment`.
    //
    // H0 DEPLOYED-WIDE FLIP (the divergence fix): the wide branch is selected STRUCTURALLY
    // (`n >= WIDE_PI_COUNT`), the exact mirror of the plain segment leaf and of the host
    // [`leg_is_wide_anchored`]. This function previously kept the SUPERSEDED weld-suffix name
    // check, which cannot see the BARE wide cohort (its name equals its narrow twin's) — so the
    // deployed custom-wide dual leaf was misclassified NARROW and its segment anchors broadcast
    // the RETIRED-to-zero single-felt rotated commit PIs, making every honest custom-bearing
    // chain UNSAT at the aggregation combine (`connect(0, genuine-anchor)` — the
    // `WitnessConflict{existing: 0, ..}` both custom-binding honest poles hit). Fail-closed, not
    // unsound — but a broken deployed wire. The structural check restores byte-identity with the
    // host root segment.
    let n = descriptor_pis.len();
    let wide = n >= WIDE_PI_COUNT;
    let old_first = n.saturating_sub(2 * SEG_ANCHOR_WIDTH);
    let new_first = n.saturating_sub(SEG_ANCHOR_WIDTH);

    let (airs, table_public_inputs, common) =
        dregg_circuit::descriptor_ir2::ir2_airs_and_common_for_config(
            desc,
            proof,
            descriptor_pis,
            config,
        )?;

    let input: RecursionInput<'_, DreggRecursionConfig, dregg_circuit::descriptor_ir2::Ir2Air> =
        RecursionInput::NativeBatchStark {
            airs: &airs,
            proof,
            common_data: &common,
            table_public_inputs,
        };

    let expose = move |cb: &mut p3_circuit::CircuitBuilder<RecursionChallenge>,
                       apt: &[Vec<p3_recursion::Target>],
                       _vk_cap: &[p3_recursion::Target]| {
        let main = apt
            .first()
            .expect("custom descriptor leaf has a main instance with descriptor PIs");
        debug_assert!(
            main.len() >= commit_hi.max(V1_PI_COUNT + 2),
            "descriptor PI vector must carry both the rotated commitments and the claim slice"
        );
        // -- The SEGMENT (lanes [0 .. SEG_WIDTH)) — byte-identical to the plain segment leaf.
        let (first_old8, last_new8): (Vec<p3_recursion::Target>, Vec<p3_recursion::Target>) =
            if wide {
                (
                    (0..SEG_ANCHOR_WIDTH).map(|k| main[old_first + k]).collect(),
                    (0..SEG_ANCHOR_WIDTH).map(|k| main[new_first + k]).collect(),
                )
            } else {
                (
                    vec![main[V1_PI_COUNT]; SEG_ANCHOR_WIDTH],
                    vec![main[V1_PI_COUNT + 1]; SEG_ANCHOR_WIDTH],
                )
            };
        let count = cb.define_const(RecursionChallenge::ONE);
        let mut acc_inputs = Vec::with_capacity(2 * SEG_ANCHOR_WIDTH);
        acc_inputs.extend_from_slice(&first_old8);
        acc_inputs.extend_from_slice(&last_new8);
        let acc = seg_poseidon_commit(cb, &acc_inputs);
        let mut claim = Vec::with_capacity(SEG_SPINE_WIDTH + claim_len);
        claim.extend_from_slice(&first_old8);
        claim.extend_from_slice(&last_new8);
        claim.push(count);
        claim.extend_from_slice(&acc);
        debug_assert_eq!(claim.len(), SEG_WIDTH);
        // -- THE SPINE BASE CASE (lanes [SEG_VK_SPINE_FIRST .. +VK_SPINE_WIDTH)). Identical to the
        // plain segment leaf's: this IS a leaf, so its spine is the constant seed and its own
        // identity reaches the root through the cap its parent absorbs. Without it the binding
        // node above has no spine block to fold and every `*_segmented` parent re-exposes a
        // 25-lane pre-spine claim that `exposed_board_window` refuses.
        claim.extend_from_slice(&leaf_vk_spine(cb));
        debug_assert_eq!(claim.len(), SEG_SPINE_WIDTH);
        // -- The CLAIMED teeth (lanes [SEG_SPINE_WIDTH .. SEG_SPINE_WIDTH+claim_len)), read from
        // the leaf's own FRI-bound descriptor PIs (not free scalars).
        for k in 0..claim_len {
            claim.push(main[claim_pi_lo + k]);
        }
        debug_assert_eq!(claim.len(), SEG_SPINE_WIDTH + claim_len);
        cb.expose_as_public_output(&claim);
    };

    prove_recursion_layer_auto_with_expose(&input, &recursion_layer_over(config), Some(&expose))
        .map_err(|e| format!("rotated dual-expose custom leaf-wrap failed: {e}"))
}

/// **THE MULTI-CLAIM DUAL-EXPOSE LEG LEAF** — [`prove_descriptor_leaf_dual_expose_at`] widened to
/// append MORE THAN ONE claim slice after the segment. Exposes, through ONE `expose_claim` table:
///
///   * the constant-size ordered chain SEGMENT `[first_old8, last_new8, count, acc]` (lanes
///     `[0 .. SEG_WIDTH)`), bound in-circuit to the descriptor's real rotated roots,
///   * the LEAF VK SPINE seed (lanes `[SEG_VK_SPINE_FIRST .. SEG_SPINE_WIDTH)`), and
///   * each claim slice `claims[i] = (lo_i, len_i)` read from the leaf's FRI-bound descriptor PIs,
///     concatenated in order after the segment AND the spine: slice `i` at lanes
///     `[SEG_SPINE_WIDTH + Σ_{k<i} len_k .. + len_i)`.
///
/// The keystone app-root leg passes `[(CUSTOM_COMMIT_PI_LO, CUSTOM_COMMIT_LEN), (field_pi_lo,
/// field_len)]` — the claimed `custom_proof_commitment` AND the leg's committed value for the
/// declared field key `K`. The binding node
/// ([`crate::joint_turn_recursive::prove_custom_binding_node_app_root_segmented`]) `connect`s the
/// commitment to the sub-proof's genuine commitment, the leg's real roots to the sub-proof's
/// declared roots, AND the leg's field to the sub-proof's published root `R`, then re-exposes ONLY
/// the segment — so the node folds into [`aggregate_tree`] like any segment leaf.
///
/// CONSTRAINT (same as [`prove_descriptor_leaf_dual_expose_at`]): on a WIDE descriptor the segment
/// anchors are sourced from the LAST `2*SEG_ANCHOR_WIDTH` PIs, so every claim slice's PIs MUST sit
/// at a FIXED offset ahead of `n - 2*SEG_ANCHOR_WIDTH`, never overlapping the rotated-commit anchors.
pub fn prove_descriptor_leaf_expose_segment_and_claims(
    desc: &dregg_circuit::descriptor_ir2::EffectVmDescriptor2,
    proof: &Ir2BatchProof<DreggRecursionConfig>,
    descriptor_pis: &[BabyBear],
    config: &DreggRecursionConfig,
    claims: &[(usize, usize)],
) -> Result<RecursionOutput<DreggRecursionConfig>, String> {
    use dregg_circuit::effect_vm::trace_rotated::{V1_PI_COUNT, WIDE_PI_COUNT};

    if claims.is_empty() {
        return Err("multi-claim dual-expose requires at least one claim slice".to_string());
    }
    let claims: Vec<(usize, usize)> = claims.to_vec();
    let total_claim_len: usize = claims.iter().map(|&(_, len)| len).sum();
    let max_hi = claims.iter().map(|&(lo, len)| lo + len).max().unwrap_or(0);
    if descriptor_pis.len() < max_hi {
        return Err(format!(
            "multi-claim dual-expose leg needs >= {max_hi} descriptor PIs to carry every claim \
             slice, got {}",
            descriptor_pis.len()
        ));
    }

    let n = descriptor_pis.len();
    let wide = n >= WIDE_PI_COUNT;
    let old_first = n.saturating_sub(2 * SEG_ANCHOR_WIDTH);
    let new_first = n.saturating_sub(SEG_ANCHOR_WIDTH);

    let (airs, table_public_inputs, common) =
        dregg_circuit::descriptor_ir2::ir2_airs_and_common_for_config(
            desc,
            proof,
            descriptor_pis,
            config,
        )?;

    let input: RecursionInput<'_, DreggRecursionConfig, dregg_circuit::descriptor_ir2::Ir2Air> =
        RecursionInput::NativeBatchStark {
            airs: &airs,
            proof,
            common_data: &common,
            table_public_inputs,
        };

    let expose = move |cb: &mut p3_circuit::CircuitBuilder<RecursionChallenge>,
                       apt: &[Vec<p3_recursion::Target>],
                       _vk_cap: &[p3_recursion::Target]| {
        let main = apt
            .first()
            .expect("custom descriptor leaf has a main instance with descriptor PIs");
        debug_assert!(
            main.len() >= max_hi.max(V1_PI_COUNT + 2),
            "descriptor PI vector must carry both the rotated commitments and every claim slice"
        );
        // -- The SEGMENT (lanes [0 .. SEG_WIDTH)) — byte-identical to the plain segment leaf.
        let (first_old8, last_new8): (Vec<p3_recursion::Target>, Vec<p3_recursion::Target>) =
            if wide {
                (
                    (0..SEG_ANCHOR_WIDTH).map(|k| main[old_first + k]).collect(),
                    (0..SEG_ANCHOR_WIDTH).map(|k| main[new_first + k]).collect(),
                )
            } else {
                (
                    vec![main[V1_PI_COUNT]; SEG_ANCHOR_WIDTH],
                    vec![main[V1_PI_COUNT + 1]; SEG_ANCHOR_WIDTH],
                )
            };
        let count = cb.define_const(RecursionChallenge::ONE);
        let mut acc_inputs = Vec::with_capacity(2 * SEG_ANCHOR_WIDTH);
        acc_inputs.extend_from_slice(&first_old8);
        acc_inputs.extend_from_slice(&last_new8);
        let acc = seg_poseidon_commit(cb, &acc_inputs);
        let mut claim = Vec::with_capacity(SEG_SPINE_WIDTH + total_claim_len);
        claim.extend_from_slice(&first_old8);
        claim.extend_from_slice(&last_new8);
        claim.push(count);
        claim.extend_from_slice(&acc);
        debug_assert_eq!(claim.len(), SEG_WIDTH);
        // -- THE SPINE BASE CASE — see `prove_descriptor_leaf_dual_expose_at`; the claim slices sit
        // AFTER it, so every consumer reads them at `SEG_SPINE_WIDTH + offset`.
        claim.extend_from_slice(&leaf_vk_spine(cb));
        debug_assert_eq!(claim.len(), SEG_SPINE_WIDTH);
        // -- Each CLAIM slice (in order), read from the leaf's own FRI-bound descriptor PIs.
        for &(lo, len) in &claims {
            for k in 0..len {
                claim.push(main[lo + k]);
            }
        }
        debug_assert_eq!(claim.len(), SEG_SPINE_WIDTH + total_claim_len);
        cb.expose_as_public_output(&claim);
    };

    prove_recursion_layer_auto_with_expose(&input, &recursion_layer_over(config), Some(&expose))
        .map_err(|e| format!("rotated multi-claim dual-expose leaf-wrap failed: {e}"))
}

// ============================================================================
// The whole-chain IVC artifact (K-fold).
// ============================================================================

/// The Lean-emitted turn-chain descriptor proof together with the exact public-input vector it
/// was minted against.
///
/// `Ir2BatchProof` verification takes public inputs separately, so the four canonical `u32` lanes
/// travel in the same serialized component as the proof. This prevents the byte verifier from
/// extracting or inventing proof-described inputs. The fourth lane is the descriptor's sequential
/// scalar digest; it is intentionally distinct from [`WholeChainProof::chain_digest`], the 8-felt
/// ordered segment digest exposed by the recursive root.
#[derive(serde::Serialize, serde::Deserialize)]
#[serde(bound = "")]
pub struct TurnChainBindingProof {
    /// Batch STARK under the production IR-v2 descriptor config.
    pub proof: Ir2BatchProof<DreggStarkConfig>,
    /// `[genesis_root, final_root, num_turns, sequential_chain_digest]` as canonical BabyBear lanes.
    pub public_inputs: [u32; 4],
}

impl TurnChainBindingProof {
    fn pis(&self) -> [BabyBear; 4] {
        self.public_inputs.map(BabyBear::new)
    }
}

/// The Gold whole-chain artifact: ONE succinct recursive proof attesting to all K finalized-turn
/// leaves, plus the directly verified Lean-emitted sequential chain-binding descriptor proof. The
/// recursion root's exposed segment links the carried claim to the executed leaves; verifier cost
/// is independent of K.
pub struct WholeChainProof {
    /// The single root batch-STARK proof (the whole tree folded to one).
    pub root: RecursionOutput<DreggRecursionConfig>,
    /// The Lean-emitted chain-binding descriptor proof plus its exact four public inputs. The
    /// byte verifier re-parses `dregg-turn-chain-binding-v2` and runs `verify_vm_descriptor2`;
    /// no Rust-authored turn-chain algebra remains on this path.
    pub binding_proof: TurnChainBindingProof,
    /// The 8-felt (~124-bit faithful) genesis state anchor the chain starts from. A WIDE leg
    /// sources it genuinely; a narrow leg broadcasts its single rotated commit felt across the
    /// eight lanes (FAITHFUL-FLOOR lift — `docs/deos/COMMITMENT-WAIST-CENSUS.md` #1).
    pub genesis_root: [BabyBear; SEG_ANCHOR_WIDTH],
    /// The 8-felt final state anchor the chain reaches.
    pub final_root: [BabyBear; SEG_ANCHOR_WIDTH],
    /// The multi-felt Poseidon2 digest committing to the ordered (old_root, new_root)
    /// pairs (codex re-review #3, widened to [`SEG_DIGEST_WIDTH`] = 8 lanes ⇒ ~124-bit —
    /// a genuine collision-resistant commitment, replacing the algebraically-broken one-felt fold).
    pub chain_digest: [BabyBear; SEG_DIGEST_WIDTH],
    /// Number of finalized turns folded.
    pub num_turns: usize,
    /// **THE BOARD WINDOW** — `[first.IN ‖ last.OUT]`, present iff every turn declared a state
    /// window (the two-leg automatafl fold). `None` for every other chain, and then the root
    /// exposes exactly `SEG_SPINE_WIDTH` lanes as it always did.
    ///
    /// This is a CARRIED CLAIM, checked for exact equality against the root's exposure by
    /// [`verify_turn_chain_recursive_from_parts_with_board_window`] — in BOTH directions: a
    /// 55-lane root (`SEG_SPINE_WIDTH + 2·11`) with no carried window is refused, and a carried
    /// window against a 33-lane root is refused.
    pub board_window: Option<BoardWindow>,
}

impl WholeChainProof {
    /// The root proof's verifier-key fingerprint (see [`RecursionVk`]).
    ///
    /// An HONEST SETUP party extracts this ONCE from a locally produced fold
    /// and distributes it as the light client's trust anchor (exactly like a
    /// SNARK VK). A VERIFIER must NEVER take the anchor from the artifact it
    /// is verifying — [`verify_turn_chain_recursive`] recomputes this from
    /// the presented root and compares it to the caller-held anchor.
    ///
    /// Note the fingerprint is a function of the root circuit SHAPE, which
    /// varies with the tree structure (`num_turns`) and the leaf trace
    /// heights: an anchor pins one accepted window shape; a client accepting
    /// several window shapes holds one anchor per shape.
    pub fn root_vk_fingerprint(&self) -> RecursionVk {
        whole_chain_anchor(&self.root.0)
            .expect("a fold this crate produced always exposes a segment + VK spine")
    }

    /// Serialize the VERIFY-SUFFICIENT subset of this proof into a versioned byte
    /// envelope ([`WholeChainProofBytes`]) that round-trips over a wire.
    ///
    /// A whole [`WholeChainProof`] is NOT byte-encodable: its `root.1`
    /// (`Rc<CircuitProverData>`) is prover-chaining data with no serde and no
    /// verifier use. The envelope therefore carries only what
    /// [`verify_turn_chain_recursive_from_parts`] reads — the root
    /// [`BatchStarkProof`] (`root.0`), the chain-binding descriptor proof, and the four
    /// public scalars — as a self-describing, version-tagged blob. The producer
    /// (a node/relayer that ran the history) ships this; the consumer (a wasm tab,
    /// a pg-dregg SRF) calls [`verify_whole_chain_proof_bytes`] on it.
    ///
    /// Infallible: the alloc/postcard serializer does not fail on a well-formed
    /// value, and both proof components derive `Serialize` (`#[serde(bound = "")]`).
    pub fn to_bytes(&self) -> Vec<u8> {
        WholeChainProofBytes::from_proof(self).to_postcard()
    }
}

/// The versioned, wire-crossable byte envelope of a [`WholeChainProof`] — the S1
/// artifact (`.docs-history-noclaude/PG-DREGG.md` §10.2, `WEB-FORWARD.md` §7).
///
/// It carries the VERIFY-SUFFICIENT subset of a [`WholeChainProof`]: the
/// prover-only `root.1` (`Rc<CircuitProverData>`) is omitted because the verifier
/// never reads it. Both proof components ride as opaque postcard blobs so the
/// envelope itself is a plain serde value; the four publics ride as canonical
/// `u32`s (a `BabyBear` is one field element). A carried `vk_fingerprint_hex`
/// rides as a producer CLAIM for diagnostics and is NEVER trusted at verify — the
/// verifier compares the RECOMPUTED fingerprint against a caller-held anchor.
///
/// The version pin fail-closes a layout change: a stale producer's bytes are
/// refused (`EnvelopeDecode`), never misread as a different shape.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct WholeChainProofBytes {
    /// The envelope format version ([`WHOLE_CHAIN_PROOF_ENVELOPE_V1`]).
    pub version: u16,
    /// The producer's CLAIMED root-circuit VK fingerprint (hex). NEVER trusted at
    /// verify — the verifier recomputes it from `root_proof` and compares to the
    /// caller-held anchor. Carried only so a consumer can render the precise
    /// "built-for-circuit X, your anchor pins Y" diagnostic.
    pub vk_fingerprint_hex: String,
    /// Postcard bytes of `WholeChainProof.root.0` — the root [`BatchStarkProof`].
    /// Teeth 1 (VK pin) and 3 (root batch verify) read exactly this.
    pub root_proof: Vec<u8>,
    /// Postcard bytes of `WholeChainProof.binding_proof` — the Lean-emitted IR-v2 descriptor
    /// proof together with its exact four public inputs. Tooth 2 verifies it with
    /// `verify_vm_descriptor2`.
    pub binding_proof: Vec<u8>,
    /// The 8-felt genesis state anchor ([`SEG_ANCHOR_WIDTH`] canonical `BabyBear` lanes as `u32`).
    /// FAITHFUL-FLOOR lift: widened from a single felt; the envelope version was bumped to
    /// fail-close old readers.
    pub genesis_root: [u32; SEG_ANCHOR_WIDTH],
    /// The 8-felt final state anchor ([`SEG_ANCHOR_WIDTH`] canonical `BabyBear` lanes as `u32`).
    pub final_root: [u32; SEG_ANCHOR_WIDTH],
    /// The multi-felt Poseidon2 ordered-history digest over the (old_root, new_root)
    /// pairs ([`SEG_DIGEST_WIDTH`] = 8 canonical `BabyBear` lanes as `u32`). Codex #3 widened
    /// this from a single felt; the FAITHFUL-FLOOR lift widened it again 4→8.
    pub chain_digest: [u32; SEG_DIGEST_WIDTH],
    /// The number of finalized turns folded — a **`u32`**, and refused at decode unless it is
    /// `< BABY_BEAR_MODULUS`.
    ///
    /// **v6 flag day.** This was a `u64` through v5, and that was a zero-cost forgery: the count
    /// rides as ONE BabyBear lane of the root's exposed segment, so both comparison sites build
    /// `BabyBear::new(num_turns as u32)` — `as u32` truncates mod `2^32` and `BabyBear::new`
    /// reduces mod `p`. A relayer editing this one field to `n + p`, `n + 2p`, `n + 2^32` (no key,
    /// no proving, no witness) produced an envelope that passed every tooth while reporting the
    /// inflated count: a genuine 2-turn history attested as 6,308,233,219 turns
    /// (`circuit-prove/tests/num_turns_alias_probe.rs`,
    /// `lightclient/tests/num_turns_alias_reaches_attested_history.rs`).
    ///
    /// The `u32` kills the `2^32` alias BY TYPE — it is not representable on the wire — and
    /// [`WholeChainProofBytes::from_postcard`] kills the `mod p` alias at the ONE decode gate
    /// every wire consumer passes, on the `u32` itself, BEFORE any `as usize` (which is 32 bits
    /// under `wasm32`, where a `usize`-typed guard would have been truncated past).
    pub num_turns: u32,
    /// **THE BOARD WINDOW** (`v5`) — `[first.IN ‖ last.OUT]` as canonical `u32` lanes, `None` for
    /// every chain that declares no state window. The verifier appends it to the expected root
    /// exposure, so a board-window root shipped WITHOUT it is refused (a 25-lane `expected` vs a
    /// 55-lane exposure at W = 11) and a window carried against a plain root is refused too.
    pub board_window: Option<(Vec<u32>, Vec<u32>)>,
}

/// The on-the-wire version tag of [`WholeChainProofBytes`]. Bumped on any layout
/// change so an old producer's bytes are refused (fail-closed) not misread.
///
/// **v2** (codex re-review #3): `chain_digest` widened from one `u32` to
/// `[u32; SEG_DIGEST_WIDTH]` — the multi-felt Poseidon2 commitment.
/// **v3** (FAITHFUL-FLOOR lift): the state endpoints `genesis_root`/`final_root` widened from one
/// `u32` to `[u32; SEG_ANCHOR_WIDTH]` (8-felt anchors), and `SEG_DIGEST_WIDTH` widened 4→8.
/// **v4** (law-#1 turn-chain cutover): `binding_proof` changed from the hand-authored
/// turn-chain uni-STARK to the Lean-emitted IR-v2 descriptor proof plus its exact four
/// public inputs.
/// **v5** (the two-leg board-window fold): the optional `board_window` claim
/// (`[first.IN ‖ last.OUT]`) rides the envelope. Old readers are fail-closed off a v5 artifact
/// rather than silently ignoring lanes the root exposes and they never check.
/// **v6** (the count-lane alias close): `num_turns` narrowed `u64` -> `u32` and refused at decode
/// unless `< BABY_BEAR_MODULUS`. Through v5 a relayer could edit that one field to any modular
/// alias (`n + p`, `n + 2^32`, …) and the artifact still passed every tooth while reporting the
/// inflated count — no key, no proving, no witness. A v5 artifact now REFUSES to load rather than
/// being reinterpreted; re-emit the envelope from the same fold (no VK rotation, no re-proving).
pub const WHOLE_CHAIN_PROOF_ENVELOPE_V1: u16 = 6;

impl WholeChainProofBytes {
    /// Project a [`WholeChainProof`] to its verify-sufficient byte envelope.
    ///
    /// **Panics** if `proof.num_turns >= BABY_BEAR_MODULUS`, rather than narrowing a count that
    /// the wire cannot represent faithfully. Every fold entry point already refuses such a chain
    /// ([`prove_turn_chain_recursive`] and its wide/conflict twins), so this is unreachable from
    /// any produced artifact; it fires only on a hand-mutated `WholeChainProof`, and then a
    /// truncating `as u32` would be exactly the forgery v6 exists to kill.
    pub fn from_proof(proof: &WholeChainProof) -> Self {
        assert!(
            (proof.num_turns as u64) < BABY_BEAR_MODULUS as u64,
            "num_turns {} >= BabyBear modulus {BABY_BEAR_MODULUS}: the count rides as ONE field \
             lane, so this envelope cannot represent it faithfully (v6 refuses to narrow it)",
            proof.num_turns
        );
        let root_proof = postcard::to_allocvec(&proof.root.0)
            .expect("root BatchStarkProof postcard-encodes (serde(bound=\"\"))");
        let binding_proof = postcard::to_allocvec(&proof.binding_proof)
            .expect("binding Proof postcard-encodes (serde(bound=\"\"))");
        WholeChainProofBytes {
            version: WHOLE_CHAIN_PROOF_ENVELOPE_V1,
            vk_fingerprint_hex: proof.root_vk_fingerprint().to_hex(),
            root_proof,
            binding_proof,
            genesis_root: core::array::from_fn(|i| proof.genesis_root[i].as_u32()),
            final_root: core::array::from_fn(|i| proof.final_root[i].as_u32()),
            chain_digest: core::array::from_fn(|i| proof.chain_digest[i].as_u32()),
            num_turns: proof.num_turns as u32,
            board_window: proof.board_window.as_ref().map(|w| {
                (
                    w.first_in.iter().map(|f| f.as_u32()).collect(),
                    w.last_out.iter().map(|f| f.as_u32()).collect(),
                )
            }),
        }
    }

    /// Encode to wire bytes (postcard). Infallible on a well-formed value.
    pub fn to_postcard(&self) -> Vec<u8> {
        postcard::to_allocvec(self).expect("WholeChainProofBytes postcard-encodes")
    }

    /// Decode from wire bytes. Fail-closed: empty input, a malformed body, a wrong
    /// version, an empty proof component, or a **non-canonical `num_turns`** is an `Err` —
    /// never a silently-accepted half-envelope.
    ///
    /// **THE COUNT GATE (v6).** `num_turns >= BABY_BEAR_MODULUS` is refused HERE, on the `u32`,
    /// before any consumer converts it. This is the single decode seam every wire path shares
    /// ([`verify_whole_chain_proof_bytes`], `dregg_lightclient::verify_history_bytes`, the wasm
    /// `verify_devnet_history` family, the gnark exporter, the ETH bridge), and it must sit on
    /// the `u32` and not a `usize`: under `wasm32` a `usize` is 32 bits, so `env.num_turns as
    /// usize` would already have truncated by the time a `usize`-typed guard could see it.
    pub fn from_postcard(bytes: &[u8]) -> Result<Self, TurnChainError> {
        if bytes.is_empty() {
            return Err(TurnChainError::EnvelopeDecode {
                reason: "empty whole-chain proof envelope".to_string(),
            });
        }
        let env: WholeChainProofBytes =
            postcard::from_bytes(bytes).map_err(|e| TurnChainError::EnvelopeDecode {
                reason: format!("envelope body does not decode: {e}"),
            })?;
        if env.version != WHOLE_CHAIN_PROOF_ENVELOPE_V1 {
            return Err(TurnChainError::EnvelopeDecode {
                reason: format!(
                    "unsupported envelope version {} (this build reads v{})",
                    env.version, WHOLE_CHAIN_PROOF_ENVELOPE_V1
                ),
            });
        }
        if env.root_proof.is_empty() {
            return Err(TurnChainError::EnvelopeDecode {
                reason: "envelope carries an empty root proof".to_string(),
            });
        }
        if env.binding_proof.is_empty() {
            return Err(TurnChainError::EnvelopeDecode {
                reason: "envelope carries an empty binding proof".to_string(),
            });
        }
        if env.num_turns >= BABY_BEAR_MODULUS {
            return Err(TurnChainError::EnvelopeDecode {
                reason: format!(
                    "num_turns {} >= BabyBear modulus {BABY_BEAR_MODULUS}: the count rides as ONE \
                     field lane, so a count at or above p is an ALIAS of {} and the teeth cannot \
                     tell them apart — refused, never reduced",
                    env.num_turns,
                    env.num_turns % BABY_BEAR_MODULUS
                ),
            });
        }
        Ok(env)
    }

    /// The root-circuit VK fingerprint RECOMPUTED from the carried root proof — what a
    /// verifier compares to its own anchor, and what it reports as the PRESENTED fingerprint.
    /// Never the envelope's claimed `vk_fingerprint_hex`. Fail-closed on a root blob that does
    /// not decode.
    pub fn presented_vk_fingerprint(&self) -> Result<RecursionVk, TurnChainError> {
        let (root, _) = self.decode_parts()?;
        whole_chain_anchor(&root)
    }

    /// Decode the two opaque blobs into the concrete recursion proof types.
    /// Fail-closed on a blob that does not deserialize into its target type.
    fn decode_parts(
        &self,
    ) -> Result<
        (
            p3_circuit_prover::BatchStarkProof<DreggRecursionConfig>,
            TurnChainBindingProof,
        ),
        TurnChainError,
    > {
        let root_proof: p3_circuit_prover::BatchStarkProof<DreggRecursionConfig> =
            postcard::from_bytes(&self.root_proof).map_err(|e| TurnChainError::EnvelopeDecode {
                reason: format!("root BatchStarkProof does not decode: {e}"),
            })?;
        // Re-check the structural invariants the prover enforces but a raw
        // `#[derive(Deserialize)]` can bypass (ext-degree, row counts, packing,
        // non-primitive manifest) — a malformed-but-decodable root is refused
        // BEFORE the cryptographic teeth run on it.
        root_proof
            .validate()
            .map_err(|e| TurnChainError::EnvelopeDecode {
                reason: format!("root BatchStarkProof failed structural validation: {e:?}"),
            })?;
        let binding_proof: TurnChainBindingProof = postcard::from_bytes(&self.binding_proof)
            .map_err(|e| TurnChainError::EnvelopeDecode {
                reason: format!("binding descriptor proof does not decode: {e}"),
            })?;
        Ok((root_proof, binding_proof))
    }
}

/// **Verify a whole-chain proof straight from its byte envelope**, against a
/// caller-held trust anchor. The over-wire dual of [`verify_turn_chain_recursive`].
///
/// Decodes the [`WholeChainProofBytes`] (fail-closed on malformed/wrong-version/
/// empty-component bytes), reconstructs the two concrete proof types, and runs the
/// SAME three teeth as the in-memory verifier via
/// [`verify_turn_chain_recursive_from_parts`]. The prover-only `root.1` is never
/// needed, so byte-reconstruction of the verify path is total.
///
/// `expected_vk` is the caller's OWN configured anchor — it is NEVER read from the
/// envelope (the envelope's `vk_fingerprint_hex` is a discarded claim). A root of a
/// different circuit fails tooth 1; tampered publics fail tooth 2; a corrupted root
/// proof fails tooth 3 (or structural validation at decode).
pub fn verify_whole_chain_proof_bytes(
    bytes: &[u8],
    expected_vk: &RecursionVk,
) -> Result<(), TurnChainError> {
    let env = WholeChainProofBytes::from_postcard(bytes)?;
    let (root_proof, binding_proof) = env.decode_parts()?;
    let window = env.board_window.as_ref().map(|(i, o)| BoardWindow {
        first_in: i.iter().map(|v| BabyBear::new(*v)).collect(),
        last_out: o.iter().map(|v| BabyBear::new(*v)).collect(),
    });
    verify_turn_chain_recursive_from_parts_with_board_window(
        &root_proof,
        &binding_proof,
        core::array::from_fn(|i| BabyBear::new(env.genesis_root[i])),
        core::array::from_fn(|i| BabyBear::new(env.final_root[i])),
        core::array::from_fn(|i| BabyBear::new(env.chain_digest[i])),
        env.num_turns as usize,
        window.as_ref(),
        expected_vk,
    )
}

/// **Verify from the two OPAQUE proof-component blobs + publics** — the seam a
/// downstream that cannot name the p3 proof types (e.g. `pg-dregg`, which does not
/// depend on `p3-circuit-prover`) plugs into.
///
/// `root_blob` is the postcard of the root [`BatchStarkProof`] (`WholeChainProof.
/// root.0`) and `binding_blob` the postcard of the chain-binding descriptor proof
/// (`WholeChainProof.binding_proof`) — exactly the two blobs a transport
/// (`pg-dregg`'s `SerializedWholeChainProof`, or the circuit's
/// [`WholeChainProofBytes`]) carries. This decodes them inside the circuit crate
/// (where the p3 types live), structurally validates the root, and runs the SAME
/// three teeth as [`verify_turn_chain_recursive`] via
/// [`verify_turn_chain_recursive_from_parts`]. Fail-closed on a blob that does not
/// decode. `vk_anchor` is the caller's configured 32-byte trust anchor.
#[allow(clippy::too_many_arguments)]
pub fn verify_turn_chain_recursive_from_blobs(
    root_blob: &[u8],
    binding_blob: &[u8],
    genesis_root: &[u32],
    final_root: &[u32],
    chain_digest: &[u32],
    num_turns: usize,
    vk_anchor: &[u8; 32],
) -> Result<(), TurnChainError> {
    if chain_digest.len() != SEG_DIGEST_WIDTH {
        return Err(TurnChainError::EnvelopeDecode {
            reason: format!(
                "chain_digest must be {SEG_DIGEST_WIDTH} lanes, got {}",
                chain_digest.len()
            ),
        });
    }
    if genesis_root.len() != SEG_ANCHOR_WIDTH || final_root.len() != SEG_ANCHOR_WIDTH {
        return Err(TurnChainError::EnvelopeDecode {
            reason: format!(
                "genesis_root/final_root must be {SEG_ANCHOR_WIDTH} lanes each, got {}/{}",
                genesis_root.len(),
                final_root.len()
            ),
        });
    }
    if root_blob.is_empty() {
        return Err(TurnChainError::EnvelopeDecode {
            reason: "empty root proof blob".to_string(),
        });
    }
    if binding_blob.is_empty() {
        return Err(TurnChainError::EnvelopeDecode {
            reason: "empty binding proof blob".to_string(),
        });
    }
    let root_proof: p3_circuit_prover::BatchStarkProof<DreggRecursionConfig> =
        postcard::from_bytes(root_blob).map_err(|e| TurnChainError::EnvelopeDecode {
            reason: format!("root BatchStarkProof blob does not decode: {e}"),
        })?;
    root_proof
        .validate()
        .map_err(|e| TurnChainError::EnvelopeDecode {
            reason: format!("root BatchStarkProof failed structural validation: {e:?}"),
        })?;
    let binding_proof: TurnChainBindingProof =
        postcard::from_bytes(binding_blob).map_err(|e| TurnChainError::EnvelopeDecode {
            reason: format!("binding descriptor proof blob does not decode: {e}"),
        })?;
    verify_turn_chain_recursive_from_parts(
        &root_proof,
        &binding_proof,
        core::array::from_fn(|i| BabyBear::new(genesis_root[i])),
        core::array::from_fn(|i| BabyBear::new(final_root[i])),
        core::array::from_fn(|i| BabyBear::new(chain_digest[i])),
        num_turns,
        &RecursionVk(*vk_anchor),
    )
}

/// Fold K finalized-turn proofs into ONE whole-chain recursive proof.
///
/// `turns` must be in the node's **finalized order** (the `tau`/blocklace order
/// from `node::blocklace_sync::poll_finalized_blocks`). Each turn's `new_root`
/// must be the next turn's `old_root` — the temporal binding the recursive segment enforces
/// in-circuit, with a matching host pre-check.
///
/// Steps:
///   1. host admission: every turn's production descriptor proof verifies
///      SELECTOR-BOUND through the Lean descriptor verifier
///      ([`verify_descriptor_participant`]) — this also determines each turn's
///      descriptor selector;
///   2. host-side: >= 2 turns, sequential continuity;
///   3. prove the Lean-emitted turn-chain descriptor over the projected endpoint sequence;
///   4. re-prove each turn's REAL rotated descriptor batch over its OWN execution trace;
///   5. wrap every turn leaf in its own IN-CIRCUIT verifier layer —
///      per-turn execution soundness is verified inside the recursion, not
///      merely at the host gate;
///   6. pairwise-aggregate all batch leaves up a binary tree to ONE root.
///
/// The host gate (step 1) is an admission discipline, NOT the soundness
/// boundary: a prover that skips it (see
/// [`prove_turn_chain_recursive_without_host_gate`]) still cannot produce a
/// verifying root for a forged turn, because steps 4-5 have no satisfying
/// witness for a forged `(old_root, new_root)`.
pub fn prove_turn_chain_recursive(
    turns: &[FinalizedTurn],
) -> Result<WholeChainProof, TurnChainError> {
    // (1) host admission: descriptor-verify every turn, selector-bound.
    let mut selectors = Vec::with_capacity(turns.len());
    for (i, t) in turns.iter().enumerate() {
        let s = verify_descriptor_participant(&t.participant)
            .map_err(|reason| TurnChainError::TurnProofInvalid { index: i, reason })?;
        selectors.push(s);
    }
    let refs: Vec<&FinalizedTurn> = turns.iter().collect();
    prove_chain_core_rotated(&refs, &selectors)
}

/// **THE UNGATED PROVER (tamper surface).** Fold a chain WITHOUT the host-side
/// descriptor admission, taking the prover's CLAIMED selectors at face value.
///
/// This exists to make the soundness claim falsifiable: the host gate in
/// [`prove_turn_chain_recursive`] must NOT be load-bearing. A malicious prover
/// that skips it and feeds a forged turn (a post-commit lie in the PIs, a stub
/// trace, an absent/borrowed proof object) still has to satisfy the REAL
/// descriptor AIR in-circuit at the leaf wrap — and a forged statement has no
/// satisfying witness, so the fold fails and no verifying root exists. The
/// tests `ungated_prover_with_forged_post_commit_cannot_produce_a_root` and
/// `ungated_prover_with_stub_leaf_cannot_produce_a_root` drive this path.
pub fn prove_turn_chain_recursive_without_host_gate(
    turns: &[FinalizedTurn],
    claimed_selectors: &[usize],
) -> Result<WholeChainProof, TurnChainError> {
    let refs: Vec<&FinalizedTurn> = turns.iter().collect();
    prove_chain_core_rotated(&refs, claimed_selectors)
}

// ============================================================================
// THE ROTATED whole-chain fold (Bucket-F: the ONLY fold — the v1 `prove_chain_core`
// + v1 leaf are deleted; `prove_turn_chain_recursive` routes straight here).
// ============================================================================

/// Fold K finalized turns into one whole-chain proof through the ROTATED leaf-wrap.
///
/// Identical in shape to [`prove_turn_chain_recursive`], but every per-turn leaf is the
/// rotated multi-table `Ir2BatchProof` (carried on `participant.rotated`), minted in-circuit
/// via [`prove_descriptor_leaf_rotated_with_config`] at [`ir2_leaf_wrap_config`] — NOT the v1
/// uni-STARK `EffectVmDescriptorAir` wrap. The turn-leaf aggregation tree runs at the ONE wrap
/// config, exactly as the aggregation gate
/// (`rotation_batchstark_leaf_smoke::two_rotated_leaves_aggregate_at_wrap_config`) proves it
/// folds. Every turn MUST carry a rotated leg (`participant.rotated == Some`); a missing leg
/// fails closed.
///
/// The temporal binding is read from the genuine 8-felt anchors; the separate Lean descriptor
/// binds their scalar head-lane projection (which equals ROTATED PI 34/35 on narrow legs).
pub fn prove_turn_chain_recursive_rotated(
    turns: &[FinalizedTurn],
) -> Result<WholeChainProof, TurnChainError> {
    // Host admission: descriptor-verify every turn, selector-bound (the v1 leg gate; the
    // rotated leaf re-proof is the soundness boundary, this is admission discipline).
    let mut selectors = Vec::with_capacity(turns.len());
    for (i, t) in turns.iter().enumerate() {
        let s = verify_descriptor_participant(&t.participant)
            .map_err(|reason| TurnChainError::TurnProofInvalid { index: i, reason })?;
        selectors.push(s);
    }
    let refs: Vec<&FinalizedTurn> = turns.iter().collect();
    prove_chain_core_rotated(&refs, &selectors)
}

/// **THE BOUNDED-MEMORY streaming sibling of [`prove_turn_chain_recursive`].** Same host
/// admission, same root claim, same verifier — but leaf PROVING is interleaved with FOLDING
/// ([`aggregate_tree_streaming`]), so peak resident recursion proofs are O(W + log2(K/W))
/// instead of O(K). `window` is the memory budget W in leaf proofs (floored to a power of two,
/// min 2; [`DEFAULT_STREAM_FOLD_WINDOW`] is the recommended small constant): `2` degenerates to
/// an (almost) pure sequential fold, a large window approaches the resident tree's parallelism
/// window. The root exposes the IDENTICAL segment as the resident fold — the streaming schedule
/// reproduces `aggregate_tree`'s tree shape exactly, which is load-bearing because the ordered
/// chain digest is shape-sensitive — so artifacts from either path verify interchangeably
/// against the same [`RecursionVk`] anchor.
///
/// The default entries take this path too when `DREGG_STREAM_FOLD_WINDOW` is set
/// ([`STREAM_FOLD_WINDOW_ENV`]); this function is the programmatic, explicit-window twin.
pub fn prove_turn_chain_recursive_streaming(
    turns: &[FinalizedTurn],
    window: usize,
) -> Result<WholeChainProof, TurnChainError> {
    let mut selectors = Vec::with_capacity(turns.len());
    for (i, t) in turns.iter().enumerate() {
        let s = verify_descriptor_participant(&t.participant)
            .map_err(|reason| TurnChainError::TurnProofInvalid { index: i, reason })?;
        selectors.push(s);
    }
    let refs: Vec<&FinalizedTurn> = turns.iter().collect();
    prove_chain_core_rotated_with_fold(&refs, &selectors, ChainFoldStrategy::Streaming { window })
}

/// The host-side whole-chain summary the staged welded fold computes: the four chain claims the
/// in-circuit root segment exposes, derived from the welded legs' rotated `(old_root, new_root)`
/// (PI 34/35 — intact through the weld) folded through the SAME ordered binary tree the recursion
/// aggregation runs in-circuit.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct WeldedChainHostSummary {
    /// The first turn's 8-felt genesis anchor (broadcast of `old_root` for a narrow leg).
    pub genesis_root: [BabyBear; SEG_ANCHOR_WIDTH],
    /// The last turn's 8-felt final anchor (broadcast of `new_root` for a narrow leg).
    pub final_root: [BabyBear; SEG_ANCHOR_WIDTH],
    /// The number of folded turns.
    pub num_turns: usize,
    /// The multi-felt Poseidon2 ordered-history digest over the `(old_root, new_root)` triples.
    pub chain_digest: [BabyBear; SEG_DIGEST_WIDTH],
}

/// Host-admit ONE welded rotated+umem leg: re-verify its `Ir2BatchProof` against its carried
/// WELDED descriptor (under the leaf-wrap config). Unlike [`verify_descriptor_participant`], this
/// does NOT map the descriptor name back through the deployed R=24 registry — the welded form is
/// STAGED (its `name` carries the
/// [`dregg_circuit::effect_vm_descriptors::ROTATED_UMEM_WELD_SUFFIX`]), so admission verifies the
/// proof against the leg's own descriptor and confirms the staged-weld marker.
fn admit_welded_leg(t: &FinalizedTurn, index: usize) -> Result<(), TurnChainError> {
    use dregg_circuit::descriptor_ir2::verify_vm_descriptor2_with_config;
    use dregg_circuit::effect_vm_descriptors::{
        ROTATED_UMEM_WELD_SUFFIX, WIDE_UMEM_MULTIDOMAIN_WELD_SUFFIX, WIDE_UMEM_WELD_SUFFIX,
    };
    let leg = &t.participant.rotated;
    // Accept the staged weld forms: the NARROW rotated+umem weld (1-felt / 46-PI), the WIDE
    // rotated+umem weld (8-felt / ~124-bit, the wide commit PIs preserved through the additive
    // weld), and the WIDE MULTI-DOMAIN weld (the NOTE/BRIDGE economic verbs — one guarded `umemOp`
    // per domain, the same 8-felt anchors). Each rides the SAME single-felt `old_root`/`new_root`
    // (PI 34/35) the chain fold's temporal tooth binds; the wide forms additionally carry the 8-felt
    // anchors at their PI tail.
    if !(leg.descriptor.name.ends_with(ROTATED_UMEM_WELD_SUFFIX)
        || leg.descriptor.name.ends_with(WIDE_UMEM_WELD_SUFFIX)
        || leg
            .descriptor
            .name
            .ends_with(WIDE_UMEM_MULTIDOMAIN_WELD_SUFFIX))
    {
        return Err(TurnChainError::TurnProofInvalid {
            index,
            reason: format!(
                "leg descriptor '{}' is not a staged rotated+umem weld (narrow / wide / wide-multidomain)",
                leg.descriptor.name
            ),
        });
    }
    // THE WIDE-CARRIER GEOMETRY VERSION BOUNDARY (flag-day v2). A carried WIDE-form leg whose
    // carrier blocks ride the RETIRED v1 shape (57 carriers / 456-column block span / 912-column
    // appendix over the 169-limb body) is refused HERE with the TYPED
    // `WideGeometryVersionError::RetiredV1` — old 57/56 registry members and their VKs cannot
    // re-enter at the upgraded assurance rung, and are never silently widened. The detector is
    // structural (the leg's own 16 wide anchor pins), so it bites BEFORE registry grounding:
    // a v1 artifact gets the explicit version refusal, not a generic off-registry error.
    if leg.descriptor.name.ends_with(WIDE_UMEM_WELD_SUFFIX)
        || leg
            .descriptor
            .name
            .ends_with(WIDE_UMEM_MULTIDOMAIN_WELD_SUFFIX)
    {
        use dregg_circuit::effect_vm_descriptors::require_wide_carrier_geometry_v2;
        if let Err(e) = require_wide_carrier_geometry_v2(&leg.descriptor) {
            return Err(TurnChainError::TurnProofInvalid {
                index,
                reason: format!("wide-carrier geometry version boundary: {e}"),
            });
        }
    }
    // GROUND THE VERIFIER LEG against the Lean-grounded welded set. The WIDE single-domain weld
    // (`-umem-wide-welded-staged`, NOT the multidomain twin) has a Lean-grounded descriptor set (the
    // verified `EffectVmEmitUMemWeldWide.weldedWideRegistry`, derived here through
    // `derive_welded_wide_member` from the committed bare wide member + the emit's contract row).
    // For such a leg we REQUIRE the carried descriptor to be byte-equal to a member and verify
    // the proof against THAT member — so a producer cannot carry an off-registry welded descriptor (the
    // ungrounded gap the missing verifier leg left). The narrow / wide-multidomain weld forms keep
    // their carried-descriptor admission (separate staged forms, out of this registry's scope).
    let is_wide_single = leg.descriptor.name.ends_with(WIDE_UMEM_WELD_SUFFIX)
        && !leg
            .descriptor
            .name
            .ends_with(WIDE_UMEM_MULTIDOMAIN_WELD_SUFFIX);
    let verify_desc = if is_wide_single {
        // ⚑ ONE KEYED LOOKUP, NOT A 57-MEMBER SCAN OF 10 MB (2026-07-31). This used to walk every
        // line of the 10 MB welded registry TSV, JSON-parsing each member until one compared equal
        // to the leg's carried descriptor — up to 57 full descriptor parses per leg, and the fold
        // runs it per leg. The welded set is now DERIVED, and the leg's own welded NAME is the key:
        // resolve the single candidate, derive it, and compare once. The grounding is identical —
        // an off-registry welded descriptor still fails the equality and is refused.
        use dregg_circuit::effect_vm_descriptors::{
            derive_welded_wide_member, umem_weld_keys_for_welded_name,
        };
        let grounded = umem_weld_keys_for_welded_name(&leg.descriptor.name)
            .into_iter()
            .filter_map(derive_welded_wide_member)
            .find(|desc| *desc == leg.descriptor);
        match grounded {
            Some(d) => d,
            None => {
                return Err(TurnChainError::TurnProofInvalid {
                    index,
                    reason: format!(
                        "WIDE welded leg descriptor '{}' is NOT a member of the Lean-grounded \
                         welded set (off-registry welded descriptor refused)",
                        leg.descriptor.name
                    ),
                });
            }
        }
    } else {
        leg.descriptor.clone()
    };
    verify_vm_descriptor2_with_config(
        &verify_desc,
        &leg.proof,
        &leg.public_inputs,
        &ir2_leaf_wrap_config(),
    )
    .map_err(|reason| TurnChainError::TurnProofInvalid { index, reason })
}

/// **THE STAGED WELDED-UMEM IVC FOLD (HOST — VK-RISK-FREE) — the last precursor before the VK
/// epoch.** Fold a multi-turn history of WELDED rotated+umem legs
/// ([`crate::joint_turn_aggregation::RotatedParticipantLeg::mint_welded_from_block_witnesses`]): each
/// leg is host-admitted (its welded `Ir2BatchProof` re-verified against its welded descriptor — the
/// umem reconciliation rides INSIDE the proof), then the chain's temporal tooth
/// (`prev.new_root == next.old_root`) + the ordered-history digest are folded through the SAME host
/// recipe [`prove_chain_core_rotated`] runs before its recursion aggregation
/// ([`compute_root_segment`] / continuity).
///
/// This is the IVC half of the flag-day weld, proved STAGED: the welded leg supplies the
/// `old_root`/`new_root` PI accessors (PI 34/35 — intact through the weld) the chain fold binds, so
/// a multi-turn history folds through the rotated+umem form exactly as it does through the deployed
/// rotated form — the 0-PI cohort leg's IVC incompatibility resolved. A `ChainBreak` (reordered /
/// dropped / spliced turn) and a leg whose welded proof does not verify are both refused.
///
/// STAGED: nothing deployed — the welded legs carry staged descriptors, no VK epoch, no
/// deployed-default flip. (The full in-circuit recursion aggregation over the welded leaves is
/// [`prove_welded_umem_turn_chain_recursive_staged`]; this host fold proves the binding the
/// aggregation succinctly attests.)
pub fn fold_welded_umem_turn_chain_staged(
    turns: &[FinalizedTurn],
) -> Result<WeldedChainHostSummary, TurnChainError> {
    if turns.len() < 2 {
        return Err(TurnChainError::TooFewTurns { count: turns.len() });
    }
    for (i, t) in turns.iter().enumerate() {
        admit_welded_leg(t, i)?;
    }
    let refs: Vec<&FinalizedTurn> = turns.iter().collect();
    // The temporal tooth: `prev.new_root == next.old_root` over the welded legs' rotated roots.
    generate_chain_trace_rotated_continuity(&refs)?;
    // The ordered root segment — the SAME pairwise binary fold the in-circuit aggregation runs.
    let root_seg = compute_root_segment(&refs);
    Ok(WeldedChainHostSummary {
        genesis_root: root_seg.first_old8,
        final_root: root_seg.last_new8,
        num_turns: turns.len(),
        chain_digest: root_seg.acc,
    })
}

/// The host-side whole-chain summary the staged WIDE welded fold computes — the 8-felt (~124-bit)
/// twin of [`WeldedChainHostSummary`]. For a WIDE welded leg the single-felt rotated commit PIs are
/// retired to zero (the 8-felt wide commit is the sole binding), so the chain is bound at the 8-felt
/// `wide_old_root8`/`wide_new_root8` anchors — the genesis / final / ordered-history digest are all
/// 8-felt.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct WideWeldedChainHostSummary {
    /// The first turn's `wide_old_root8` (the 8-felt chain genesis).
    pub genesis_root8: [BabyBear; 8],
    /// The last turn's `wide_new_root8` (the 8-felt chain head).
    pub final_root8: [BabyBear; 8],
    /// The number of folded turns.
    pub num_turns: usize,
    /// The 8-felt Poseidon2 ordered-history digest over the per-turn `(wide_old_root8,
    /// wide_new_root8)` pairs (`hash_many_8`-folded in chain order — a genuine ~124-bit
    /// collision-resistant commitment; a reorder yields a different digest).
    pub chain_digest8: [BabyBear; 8],
}

/// **THE STAGED WIDE WELDED-UMEM IVC FOLD (HOST — VK-RISK-FREE) — the IVC half of the genuine flip
/// precursor the VK epoch needs.** The 8-felt (~124-bit) twin of
/// [`fold_welded_umem_turn_chain_staged`]: fold a multi-turn history of WIDE welded rotated+umem
/// legs ([`crate::joint_turn_aggregation::RotatedParticipantLeg::mint_welded_wide_from_block_witnesses`]).
/// Each leg is host-admitted (its welded `Ir2BatchProof` re-verified against its welded WIDE
/// descriptor), then the chain's temporal tooth is bound at the **8-felt** anchor
/// (`prev.wide_new_root8 == next.wide_old_root8`) — NOT the single felt, which the wide form retires
/// to zero — and the 8-felt ordered-history digest is folded.
///
/// A `WideChainBreak` (reordered / dropped / spliced turn), a `MissingWideAnchor` (a narrow leg
/// presented to the wide fold), and a leg whose welded proof does not verify are all refused. STAGED:
/// nothing deployed — the welded legs carry staged descriptors, no VK epoch, no deployed-default
/// flip.
pub fn fold_wide_welded_umem_turn_chain_staged(
    turns: &[FinalizedTurn],
) -> Result<WideWeldedChainHostSummary, TurnChainError> {
    use dregg_circuit::poseidon2::hash_many_8;
    if turns.len() < 2 {
        return Err(TurnChainError::TooFewTurns { count: turns.len() });
    }
    // (1) Host admission: each leg's welded WIDE proof re-verifies against its welded descriptor.
    for (i, t) in turns.iter().enumerate() {
        admit_welded_leg(t, i)?;
    }
    // (2) Collect the 8-felt anchors (a narrow leg lacking the wide tail is refused).
    let mut anchors: Vec<([BabyBear; 8], [BabyBear; 8])> = Vec::with_capacity(turns.len());
    for (i, t) in turns.iter().enumerate() {
        let leg = &t.participant.rotated;
        let old8 = leg
            .wide_old_root8()
            .ok_or(TurnChainError::MissingWideAnchor { index: i })?;
        let new8 = leg
            .wide_new_root8()
            .ok_or(TurnChainError::MissingWideAnchor { index: i })?;
        anchors.push((old8, new8));
    }
    // (3) The 8-felt temporal tooth: each turn's old8 == the previous turn's new8.
    for i in 1..anchors.len() {
        if anchors[i].0 != anchors[i - 1].1 {
            return Err(TurnChainError::WideChainBreak { index: i });
        }
    }
    // (4) The 8-felt ordered-history digest (a genuine ~124-bit Poseidon2 fold over the ordered
    //     `(old8, new8)` pairs; a reorder yields a different digest).
    let mut acc = [BabyBear::ZERO; 8];
    for (old8, new8) in &anchors {
        let mut absorb = Vec::with_capacity(24);
        absorb.extend_from_slice(&acc);
        absorb.extend_from_slice(old8);
        absorb.extend_from_slice(new8);
        acc = hash_many_8(&absorb);
    }
    Ok(WideWeldedChainHostSummary {
        genesis_root8: anchors[0].0,
        final_root8: anchors[anchors.len() - 1].1,
        num_turns: turns.len(),
        chain_digest8: acc,
    })
}

/// **THE STAGED WELDED-UMEM IVC FOLD (RECURSIVE — VK-RISK-FREE).** The in-circuit twin of
/// [`fold_welded_umem_turn_chain_staged`]: host-admit each welded leg, check continuity, then mint
/// ONE segment-carrying recursion leaf per welded turn ([`prove_descriptor_leaf_rotated_with_segment`]
/// — which RE-VERIFIES the welded (umem-bearing) descriptor proof IN-CIRCUIT) and aggregate them to
/// one root whose exposed segment is the whole-chain `[genesis_root, final_root, num_turns,
/// chain_digest]`. Returns the same [`WholeChainProof`] artifact the deployed rotated fold yields.
///
/// STAGED: the leaves carry welded (staged) descriptors; no VK epoch, no deployed-default flip. This
/// is the genuine end-to-end IVC fold over the rotated+umem form — the precursor whose ONLY remaining
/// step to deployment is the gated VK epoch (committing the welded descriptor's VK).
pub fn prove_welded_umem_turn_chain_recursive_staged(
    turns: &[FinalizedTurn],
) -> Result<WholeChainProof, TurnChainError> {
    if turns.len() < 2 {
        return Err(TurnChainError::TooFewTurns { count: turns.len() });
    }
    for (i, t) in turns.iter().enumerate() {
        admit_welded_leg(t, i)?;
    }
    let refs: Vec<&FinalizedTurn> = turns.iter().collect();
    generate_chain_trace_rotated_continuity(&refs)?;
    if (turns.len() as u64) >= BABY_BEAR_MODULUS as u64 {
        return Err(TurnChainError::RecursionFailed {
            reason: format!(
                "num_turns {} >= BabyBear modulus {BABY_BEAR_MODULUS} (count lane would wrap mod p)",
                turns.len()
            ),
        });
    }
    let root_seg = compute_root_segment(&refs);
    let genesis_root = root_seg.first_old8;
    let final_root = root_seg.last_new8;
    let chain_digest = root_seg.acc;

    let config = ir2_leaf_wrap_config();
    // ⚑ THE FOLD ENGINE, DERIVED. A leaf wrap now emits at `recursion_layer_over(config)`'s mint
    // knobs, so every node above it verifies at those — one more application of the same rule,
    // which is its fixed point. See [`turn_chain_root_config`].
    let fold_config = recursion_layer_over(&recursion_layer_over(&config));
    let backend = create_recursion_backend();
    let params = ProveNextLayerParams::default();

    // The carried binding proof (defense-in-depth host witness; NOT folded into the root — the
    // segment tooth over the root's exposed segment binds the claim).
    let binding_inner = prove_chain_binding_descriptor_rotated(&refs)?;

    let mut batch_leaves: Vec<RecursionOutput<DreggRecursionConfig>> =
        Vec::with_capacity(turns.len());
    for (i, t) in refs.iter().enumerate() {
        let leg = &t.participant.rotated;
        let wrapped = prove_descriptor_leaf_rotated_with_segment(
            &leg.descriptor,
            &leg.proof,
            &leg.public_inputs,
            &config,
        )
        .map_err(|reason| TurnChainError::TurnProofInvalid { index: i, reason })?;
        batch_leaves.push(wrapped);
    }
    let root = aggregate_tree(batch_leaves, &fold_config, &backend, &params)?;

    Ok(WholeChainProof {
        root,
        binding_proof: binding_inner,
        genesis_root,
        final_root,
        chain_digest,
        num_turns: turns.len(),
        board_window: None,
    })
}

// ============================================================================
// THE IN-CIRCUIT RECURSIVE WIDE FOLD — the 8-felt generalization of the
// single-felt chain-binding recursion (the named tail from the WIDE+umem weld
// `d81f7f60`; the host fold `fold_wide_welded_umem_turn_chain_staged` is its
// host-side twin). STAGED / VK-risk-free.
//
// The single-felt recursion exposes a per-leaf SEGMENT `[first_old, last_new,
// count, acc]` whose `first_old`/`last_new` are the single-felt rotated commits
// (PI 34/35), and combines segments up a binary tree binding single-felt
// continuity `L.last_new == R.first_old` in-circuit. This is its 8-felt
// generalization: the wide-welded leg retires the single-felt PIs (34/35) to
// zero (the 8-felt wide commit is the sole binding), so the segment's endpoints
// are the **8-felt** wide anchors (`wide_old_root8`/`wide_new_root8`, the leg's
// last-16 PIs) and the combine binds 8-felt continuity
// (`prev.wide_new_root8 == next.wide_old_root8`) lane-by-lane IN-CIRCUIT. The
// ordered-history digest reuses the proven [`seg_poseidon_commit`] multi-felt
// (~124-bit) Poseidon2 commitment — the load-bearing generalization is the
// 8-felt anchor binding, not the digest width.
// ============================================================================

/// The number of base-field lanes in a WIDE state-commit anchor (the 8-felt /
/// ~124-bit faithful commit a WIDE / wide-welded leg publishes).
pub const WIDE_ANCHOR_WIDTH: usize = 8;

// The WIDE segment lane layout exposed through the `expose_claim` table:
// `[first_old8(8), last_new8(8), count(1), acc(SEG_DIGEST_WIDTH)]`.
const WSEG_FIRST_OLD: usize = 0;
const WSEG_LAST_NEW: usize = WIDE_ANCHOR_WIDTH;
const WSEG_COUNT: usize = 2 * WIDE_ANCHOR_WIDTH;
const WSEG_DIGEST_FIRST: usize = 2 * WIDE_ANCHOR_WIDTH + 1;
/// A wide segment is exactly this many base-field lanes.
pub const WIDE_SEG_WIDTH: usize = WSEG_DIGEST_FIRST + SEG_DIGEST_WIDTH;

/// The WIDE family's VK-spine offset and total exposed width — the 8-felt twin of
/// [`SEG_VK_SPINE_FIRST`] / [`SEG_SPINE_WIDTH`]. Same spine, same fold, different segment ahead of
/// it, so a wide root is anchored on its subtree's circuit identity exactly as a narrow one is.
pub const WSEG_VK_SPINE_FIRST: usize = WIDE_SEG_WIDTH;
pub const WIDE_SEG_SPINE_WIDTH: usize = WIDE_SEG_WIDTH + VK_SPINE_WIDTH;

/// The host-side mirror of one WIDE descriptor-leaf / aggregation-node segment
/// (the 8-felt twin of [`HostSeg`]): the base-field values it exposes through the
/// `expose_claim` table, `[first_old8(8), last_new8(8), count(1), acc(W)]`. The
/// prover folds these the SAME way the in-circuit combine does so it knows the
/// root segment (hence the wide chain claims) to carry.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct WideHostSeg {
    pub first_old8: [BabyBear; WIDE_ANCHOR_WIDTH],
    pub last_new8: [BabyBear; WIDE_ANCHOR_WIDTH],
    pub count: BabyBear,
    /// The multi-felt Poseidon2 ordered-history digest (the SAME [`seg_poseidon_commit_host`]
    /// the single-felt recursion uses).
    pub acc: [BabyBear; SEG_DIGEST_WIDTH],
}

/// The per-turn (wide descriptor-leaf) segment: `first_old8`/`last_new8` are the
/// 8-felt wide anchors, `count = 1`, `acc = commit([first_old8 ++ last_new8])` —
/// the SAME seed [`seg_poseidon_commit`] computes at the wide leaf wrap (16 inputs).
pub(crate) fn leaf_wide_seg(
    old8: [BabyBear; WIDE_ANCHOR_WIDTH],
    new8: [BabyBear; WIDE_ANCHOR_WIDTH],
) -> WideHostSeg {
    let mut inputs = Vec::with_capacity(2 * WIDE_ANCHOR_WIDTH);
    inputs.extend_from_slice(&old8);
    inputs.extend_from_slice(&new8);
    WideHostSeg {
        first_old8: old8,
        last_new8: new8,
        count: BabyBear::ONE,
        acc: seg_poseidon_commit_host(&inputs),
    }
}

/// Combine two adjacent wide segments (the host mirror of the wide aggregation combine):
/// 8-felt continuity `l.last_new8 == r.first_old8` (caller-checked upstream as
/// `WideChainBreak`), `first_old8 = l.first_old8`, `last_new8 = r.last_new8`,
/// `count = l.count + r.count`, `acc = commit(l.acc ++ r.acc)` (order-sensitive: l before r,
/// the SAME 8-input commit the in-circuit combine runs).
pub(crate) fn combine_wide_seg(l: WideHostSeg, r: WideHostSeg) -> WideHostSeg {
    let mut acc_inputs = Vec::with_capacity(2 * SEG_DIGEST_WIDTH);
    acc_inputs.extend_from_slice(&l.acc);
    acc_inputs.extend_from_slice(&r.acc);
    WideHostSeg {
        first_old8: l.first_old8,
        last_new8: r.last_new8,
        count: l.count + r.count,
        acc: seg_poseidon_commit_host(&acc_inputs),
    }
}

/// Fold the per-turn wide leaf segments into the ROOT wide segment using the SAME pairwise
/// left-to-right binary tree (with odd-element carry) that [`aggregate_tree_wide`] runs
/// in-circuit — so the host-computed root `[first_old8, last_new8, count, acc]` equals what
/// the wide root proof exposes.
fn compute_root_wide_segment(
    anchors: &[([BabyBear; WIDE_ANCHOR_WIDTH], [BabyBear; WIDE_ANCHOR_WIDTH])],
) -> WideHostSeg {
    let mut level: Vec<WideHostSeg> = anchors.iter().map(|(o, n)| leaf_wide_seg(*o, *n)).collect();
    while level.len() > 1 {
        let mut next: Vec<WideHostSeg> = Vec::with_capacity(level.len().div_ceil(2));
        let mut i = 0;
        while i + 1 < level.len() {
            next.push(combine_wide_seg(level[i], level[i + 1]));
            i += 2;
        }
        if i < level.len() {
            next.push(level[i]);
        }
        level = next;
    }
    level[0]
}

/// Collect each welded leg's 8-felt wide anchors and check the **8-felt** temporal tooth
/// (`prev.wide_new_root8 == next.wide_old_root8`). A narrow leg lacking the wide tail is
/// `MissingWideAnchor`; a reorder/splice is `WideChainBreak`. The host twin of the in-circuit
/// continuity the wide combine binds lane-by-lane.
fn collect_wide_anchors(
    turns: &[&FinalizedTurn],
) -> Result<Vec<([BabyBear; WIDE_ANCHOR_WIDTH], [BabyBear; WIDE_ANCHOR_WIDTH])>, TurnChainError> {
    if turns.len() < 2 {
        return Err(TurnChainError::TooFewTurns { count: turns.len() });
    }
    let mut anchors = Vec::with_capacity(turns.len());
    for (i, t) in turns.iter().enumerate() {
        let leg = &t.participant.rotated;
        let old8 = leg
            .wide_old_root8()
            .ok_or(TurnChainError::MissingWideAnchor { index: i })?;
        let new8 = leg
            .wide_new_root8()
            .ok_or(TurnChainError::MissingWideAnchor { index: i })?;
        anchors.push((old8, new8));
    }
    for i in 1..anchors.len() {
        if anchors[i].0 != anchors[i - 1].1 {
            return Err(TurnChainError::WideChainBreak { index: i });
        }
    }
    Ok(anchors)
}

/// **THE WIDE SEGMENT-ACCUMULATOR DESCRIPTOR LEAF** (the 8-felt twin of
/// [`prove_descriptor_leaf_rotated_with_segment`]). Wrap one WIDE welded finalized-turn
/// descriptor batch in-circuit AND emit its constant-size ordered WIDE SEGMENT through the
/// `expose_claim` table, BOUND in-circuit to the descriptor proof's REAL published 8-felt
/// anchors:
///
///   `WideSeg = [first_old8(8), last_new8(8), count(1), acc(W)]`
///     first_old8 := descriptor PIs `[n-16 .. n-8)` (the wide BEFORE 8-felt commit)
///     last_new8  := descriptor PIs `[n-8  .. n)`   (the wide AFTER  8-felt commit)
///     count      := 1
///     acc        := commit([first_old8 ++ last_new8]) (the per-turn ordered-history seed)
///
/// Because `first_old8`/`last_new8` are READ from the descriptor proof's own verified
/// `air_public_targets` (absolute PI indices `n-16..n`, the wide carrier PIs whose
/// `PiBinding` makes a tampered anchor UNSAT), the segment is tied to the ACTUAL execution
/// this leaf re-proves — a prover cannot expose 8-felt endpoints that differ from the wide
/// descriptor it folded. The single-felt rotated PIs (34/35) are retired to zero on the wide
/// form, so the 8-felt anchors are the sole binding.
pub fn prove_descriptor_leaf_rotated_with_wide_segment(
    desc: &dregg_circuit::descriptor_ir2::EffectVmDescriptor2,
    proof: &Ir2BatchProof<DreggRecursionConfig>,
    descriptor_pis: &[BabyBear],
    config: &DreggRecursionConfig,
) -> Result<RecursionOutput<DreggRecursionConfig>, String> {
    let n = descriptor_pis.len();
    if n < 2 * WIDE_ANCHOR_WIDTH {
        return Err(format!(
            "wide segment leaf needs >= {} PIs to carry the two 8-felt anchors, got {n}",
            2 * WIDE_ANCHOR_WIDTH
        ));
    }
    // Absolute PI indices of the wide anchors (the SAME tail `RotatedParticipantLeg::
    // wide_old_root8`/`wide_new_root8` read host-side): old8 at `[n-16 .. n-8)`, new8 at
    // `[n-8 .. n)`. Indexed from the START so they are correct even if the main instance's
    // target vector is padded past `n`.
    let old_first = n - 2 * WIDE_ANCHOR_WIDTH;
    let new_first = n - WIDE_ANCHOR_WIDTH;

    let (airs, table_public_inputs, common) =
        dregg_circuit::descriptor_ir2::ir2_airs_and_common_for_config(
            desc,
            proof,
            descriptor_pis,
            config,
        )?;

    let input: RecursionInput<'_, DreggRecursionConfig, dregg_circuit::descriptor_ir2::Ir2Air> =
        RecursionInput::NativeBatchStark {
            airs: &airs,
            proof,
            common_data: &common,
            table_public_inputs,
        };

    let expose = move |cb: &mut p3_circuit::CircuitBuilder<RecursionChallenge>,
                       apt: &[Vec<p3_recursion::Target>],
                       _vk_cap: &[p3_recursion::Target]| {
        let main = apt
            .first()
            .expect("descriptor leaf has a main instance with descriptor PIs");
        debug_assert!(
            main.len() >= n,
            "descriptor PI target vector must carry the 8-felt wide anchors at its tail"
        );
        let first_old8: Vec<p3_recursion::Target> = (0..WIDE_ANCHOR_WIDTH)
            .map(|k| main[old_first + k])
            .collect();
        let last_new8: Vec<p3_recursion::Target> = (0..WIDE_ANCHOR_WIDTH)
            .map(|k| main[new_first + k])
            .collect();
        let count = cb.define_const(RecursionChallenge::ONE);
        // The per-turn seed: a genuine multi-felt Poseidon2 commitment over the leaf's REAL
        // (descriptor-bound) 8-felt endpoints (16 inputs).
        let mut acc_inputs = Vec::with_capacity(2 * WIDE_ANCHOR_WIDTH);
        acc_inputs.extend_from_slice(&first_old8);
        acc_inputs.extend_from_slice(&last_new8);
        let acc = seg_poseidon_commit(cb, &acc_inputs);
        let mut seg = Vec::with_capacity(WIDE_SEG_WIDTH);
        seg.extend_from_slice(&first_old8);
        seg.extend_from_slice(&last_new8);
        seg.push(count);
        seg.extend_from_slice(&acc);
        seg.extend_from_slice(&leaf_vk_spine(cb));
        debug_assert_eq!(seg.len(), WIDE_SEG_SPINE_WIDTH);
        cb.expose_as_public_output(&seg);
    };

    prove_recursion_layer_auto_with_expose(&input, &recursion_layer_over(config), Some(&expose))
        .map_err(|e| format!("rotated native-batch WIDE segment leaf-wrap failed: {e}"))
}

/// Fold a vector of WIDE-segment-carrying batch-STARK proofs to ONE via 2-to-1 aggregation
/// layers, combining the WIDE segments in-circuit at each node (8-felt continuity + count
/// additivity + ordered-digest fold) — the 8-felt twin of [`aggregate_tree`].
fn aggregate_tree_wide(
    mut proofs: Vec<RecursionOutput<DreggRecursionConfig>>,
    config: &DreggRecursionConfig,
    _backend: &p3_recursion::FriRecursionBackendForExt<
        D,
        16,
        8,
        p3_recursion::ops::Poseidon2Config,
    >,
    _params: &ProveNextLayerParams,
) -> Result<RecursionOutput<DreggRecursionConfig>, TurnChainError> {
    if proofs.is_empty() {
        return Err(TurnChainError::RecursionFailed {
            reason: "no wide leaves to aggregate".to_string(),
        });
    }
    while proofs.len() > 1 {
        let mut next_level: Vec<RecursionOutput<DreggRecursionConfig>> =
            Vec::with_capacity(proofs.len().div_ceil(2));
        let mut i = 0;
        while i + 1 < proofs.len() {
            let left_idx = expose_claim_instance_index(&proofs[i].0).ok_or_else(|| {
                TurnChainError::RecursionFailed {
                    reason: "left wide aggregation child carries no segment (expose_claim) table"
                        .to_string(),
                }
            })?;
            let right_idx = expose_claim_instance_index(&proofs[i + 1].0).ok_or_else(|| {
                TurnChainError::RecursionFailed {
                    reason: "right wide aggregation child carries no segment (expose_claim) table"
                        .to_string(),
                }
            })?;

            // ⚑ THE CHILD-VK PINS. Unpinned, each child's preprocessed commitment is an
            // unconstrained runtime public input, so a same-shape/different-constants child — a
            // VALID proof of a DIFFERENT circuit — folds through and the parent VK does not move.
            // TRACKED (read off the children being folded) because a tree fold over a runtime-sized
            // vector has no per-node anchor to name: what the pin buys here is that the pinned
            // values reach the parent's `RecursionVk`, so the substitution moves the ROOT
            // fingerprint a consumer anchors. See `crate::fold_vk_pin`.
            let pins = crate::fold_vk_pin::FoldVkPins::tracked(&proofs[i], &proofs[i + 1])
                .map_err(|reason| TurnChainError::RecursionFailed {
                    reason: format!("wide aggregation child VK pin unavailable: {reason}"),
                })?;
            let left = proofs[i].into_recursion_input_pinned::<BatchOnly>(pins.left.clone());
            let right = proofs[i + 1].into_recursion_input_pinned::<BatchOnly>(pins.right.clone());

            let expose = move |cb: &mut p3_circuit::CircuitBuilder<RecursionChallenge>,
                               left_apt: &[Vec<p3_recursion::Target>],
                               right_apt: &[Vec<p3_recursion::Target>],
                               left_vk_cap: &[p3_recursion::Target],
                               right_vk_cap: &[p3_recursion::Target]| {
                let l = left_apt
                    .get(left_idx)
                    .expect("left wide segment instance present");
                let r = right_apt
                    .get(right_idx)
                    .expect("right wide segment instance present");
                debug_assert!(l.len() >= WIDE_SEG_SPINE_WIDTH && r.len() >= WIDE_SEG_SPINE_WIDTH);
                let vk_spine =
                    combine_vk_spine(cb, l, r, left_vk_cap, right_vk_cap, WSEG_VK_SPINE_FIRST);

                // (1) THE 8-FELT STATE CONTINUITY tooth, IN-CIRCUIT: L.last_new8 == R.first_old8,
                // lane-by-lane. The left subtree's final 8-felt root must be the right subtree's
                // first 8-felt root. `connect` (not `assert_zero(sub(..))`) keeps the equality off
                // the shared `ExprId::ZERO` witness — equal on the honest path, a conflict (a
                // tampered/discontinuous chain) on a mismatch, fail-closed.
                for k in 0..WIDE_ANCHOR_WIDTH {
                    cb.connect(l[WSEG_LAST_NEW + k], r[WSEG_FIRST_OLD + k]);
                }

                // (2) parent wide segment: span [L.first_old8 .. R.last_new8], count L+R, ordered
                // multi-felt digest acc = commit(L.acc ++ R.acc) (L absorbed before R ⇒
                // order-sensitive).
                let count = cb.add(l[WSEG_COUNT], r[WSEG_COUNT]);
                let mut acc_inputs = Vec::with_capacity(2 * SEG_DIGEST_WIDTH);
                acc_inputs
                    .extend_from_slice(&l[WSEG_DIGEST_FIRST..WSEG_DIGEST_FIRST + SEG_DIGEST_WIDTH]);
                acc_inputs
                    .extend_from_slice(&r[WSEG_DIGEST_FIRST..WSEG_DIGEST_FIRST + SEG_DIGEST_WIDTH]);
                let acc = seg_poseidon_commit(cb, &acc_inputs);
                let mut parent = Vec::with_capacity(WIDE_SEG_SPINE_WIDTH);
                parent.extend_from_slice(&l[WSEG_FIRST_OLD..WSEG_FIRST_OLD + WIDE_ANCHOR_WIDTH]);
                parent.extend_from_slice(&r[WSEG_LAST_NEW..WSEG_LAST_NEW + WIDE_ANCHOR_WIDTH]);
                parent.push(count);
                parent.extend_from_slice(&acc);
                parent.extend_from_slice(&vk_spine);
                debug_assert_eq!(parent.len(), WIDE_SEG_SPINE_WIDTH);
                cb.expose_as_public_output(&parent);
            };

            let out =
                prove_recursion_aggregation_auto_with_expose(&left, &right, config, Some(&expose))
                    .map_err(|e| TurnChainError::RecursionFailed {
                        reason: format!("wide aggregation layer failed: {e}"),
                    })?;
            next_level.push(out);
            i += 2;
        }
        if i < proofs.len() {
            next_level.push(proofs.pop().unwrap());
        }
        proofs = next_level;
    }
    Ok(proofs.pop().unwrap())
}

/// The WIDE whole-chain IVC artifact (the 8-felt twin of [`WholeChainProof`]): ONE succinct
/// recursive proof whose root's exposed WIDE segment IS the whole-chain claim
/// `[genesis_root8, final_root8, num_turns, chain_digest]`, derived BY CONSTRUCTION from the
/// real wide welded descriptor leaves and combined up the tree with 8-felt continuity. The
/// verifier checks only the root; cost is independent of the number of folded turns.
///
/// There is no carried scalar binding descriptor here (the wide form retires scalar PI 34/35 to
/// zero) — the wide segment tooth over the root's exposed segment is the sole binding, exactly as
/// the codex ordered-segment-accumulator close intends.
pub struct WideWholeChainProof {
    /// The single root batch-STARK proof (the whole wide tree folded to one).
    pub root: RecursionOutput<DreggRecursionConfig>,
    /// The 8-felt genesis (the first turn's `wide_old_root8`).
    pub genesis_root8: [BabyBear; WIDE_ANCHOR_WIDTH],
    /// The 8-felt final root (the last turn's `wide_new_root8`).
    pub final_root8: [BabyBear; WIDE_ANCHOR_WIDTH],
    /// The multi-felt Poseidon2 ordered-history digest over the per-turn `(wide_old_root8,
    /// wide_new_root8)` segments, tree-folded (the SAME [`seg_poseidon_commit`] the deployed
    /// single-felt recursion uses).
    pub chain_digest: [BabyBear; SEG_DIGEST_WIDTH],
    /// Number of finalized turns folded.
    pub num_turns: usize,
}

impl WideWholeChainProof {
    /// The root proof's verifier-key fingerprint (see [`RecursionVk`]). An honest setup party
    /// extracts this ONCE and distributes it as the trust anchor; a verifier NEVER takes the
    /// anchor from the artifact it verifies.
    pub fn root_vk_fingerprint(&self) -> RecursionVk {
        whole_chain_anchor(&self.root.0)
            .expect("a fold this crate produced always exposes a segment + VK spine")
    }
}

/// **THE STAGED WIDE WELDED-UMEM IVC FOLD (RECURSIVE — VK-RISK-FREE).** The IN-CIRCUIT twin of
/// [`fold_wide_welded_umem_turn_chain_staged`] and the 8-felt generalization of
/// [`prove_welded_umem_turn_chain_recursive_staged`]: host-admit each WIDE welded leg, collect
/// its 8-felt anchors + check 8-felt continuity, then mint ONE wide-segment-carrying recursion
/// leaf per turn ([`prove_descriptor_leaf_rotated_with_wide_segment`] — which RE-VERIFIES the
/// wide welded (umem-bearing) descriptor proof IN-CIRCUIT) and aggregate them to one root whose
/// exposed WIDE segment is the whole-chain `[genesis_root8, final_root8, num_turns,
/// chain_digest]`. The 8-felt continuity (`prev.wide_new_root8 == next.wide_old_root8`) is bound
/// IN-CIRCUIT at each aggregation node (lane-by-lane `connect`), so the whole-history IVC folds
/// the wide+umem legs in-circuit — not just host-side.
///
/// STAGED: the leaves carry wide welded (staged) descriptors; no VK epoch, no deployed-default
/// flip. This is the genuine end-to-end in-circuit IVC fold over the rotated+umem WIDE form —
/// the flip precursor whose ONLY remaining step to deployment is the gated VK epoch.
pub fn prove_wide_welded_umem_turn_chain_recursive_staged(
    turns: &[FinalizedTurn],
) -> Result<WideWholeChainProof, TurnChainError> {
    if turns.len() < 2 {
        return Err(TurnChainError::TooFewTurns { count: turns.len() });
    }
    // (1) host admission: each WIDE welded leg's proof re-verifies against its welded descriptor.
    for (i, t) in turns.iter().enumerate() {
        admit_welded_leg(t, i)?;
    }
    let refs: Vec<&FinalizedTurn> = turns.iter().collect();
    // (2) collect the 8-felt anchors + the 8-felt continuity tooth (host twin of the in-circuit
    //     combine). A narrow leg is `MissingWideAnchor`; a reorder is `WideChainBreak`.
    let anchors = collect_wide_anchors(&refs)?;
    // CODEX #5: the count lane is a BabyBear (mod p), so num_turns must be < p (no modular wrap).
    if (turns.len() as u64) >= BABY_BEAR_MODULUS as u64 {
        return Err(TurnChainError::RecursionFailed {
            reason: format!(
                "num_turns {} >= BabyBear modulus {BABY_BEAR_MODULUS} (count lane would wrap mod p)",
                turns.len()
            ),
        });
    }
    // (3) the ROOT wide segment the host computes by folding the per-turn leaf segments through
    //     the SAME pairwise binary tree `aggregate_tree_wide` runs in-circuit.
    let root_seg = compute_root_wide_segment(&anchors);
    let genesis_root8 = root_seg.first_old8;
    let final_root8 = root_seg.last_new8;
    let chain_digest = root_seg.acc;

    let config = ir2_leaf_wrap_config();
    // ⚑ THE FOLD ENGINE, DERIVED. A leaf wrap now emits at `recursion_layer_over(config)`'s mint
    // knobs, so every node above it verifies at those — one more application of the same rule,
    // which is its fixed point. See [`turn_chain_root_config`].
    let fold_config = recursion_layer_over(&recursion_layer_over(&config));
    let backend = create_recursion_backend();
    let params = ProveNextLayerParams::default();

    // (4) one WIDE-segment-carrying descriptor leaf per finalized turn (each re-verifying the wide
    //     welded descriptor proof in-circuit, exposing its 8-felt segment bound to the real anchors).
    let mut batch_leaves: Vec<RecursionOutput<DreggRecursionConfig>> =
        Vec::with_capacity(turns.len());
    for (i, t) in refs.iter().enumerate() {
        let leg = &t.participant.rotated;
        let wrapped = prove_descriptor_leaf_rotated_with_wide_segment(
            &leg.descriptor,
            &leg.proof,
            &leg.public_inputs,
            &config,
        )
        .map_err(|reason| TurnChainError::TurnProofInvalid { index: i, reason })?;
        batch_leaves.push(wrapped);
    }
    // (5) aggregate to ONE root, combining the wide segments in-circuit (8-felt continuity + count
    //     + ordered-digest fold). The root's exposed wide segment is the whole-chain claim.
    let root = aggregate_tree_wide(batch_leaves, &fold_config, &backend, &params)?;

    Ok(WideWholeChainProof {
        root,
        genesis_root8,
        final_root8,
        chain_digest,
        num_turns: turns.len(),
    })
}

/// Verify a WIDE whole-chain artifact against a caller-held trust anchor (the 8-felt twin of
/// [`verify_turn_chain_recursive`]). Cost is independent of the number of folded turns. Three
/// teeth, in order:
///
///   1. **VK pin** — the presented root's verifier-key fingerprint must equal `expected_vk`
///      (a root of a different circuit is refused).
///   2. **The root** — the single root batch-STARK proof verifies under
///      [`turn_chain_root_config`] (⚠ it used to be [`ir2_leaf_wrap_config`]; a leaf wrap now
///      mints at its own engine, so every node above it does too).
///   3. **The WIDE segment tooth** — the root's exposed ordered WIDE segment
///      `[first_old8, last_new8, count, acc]` (built BY CONSTRUCTION from the real wide
///      descriptor leaves and combined up the tree with 8-felt continuity) must equal the carried
///      `[genesis_root8, final_root8, num_turns, chain_digest]`. A root that executed history A
///      cannot expose B's 8-felt endpoints, so a B-claim against an A-execution is refused.
pub fn verify_wide_turn_chain_recursive(
    proof: &WideWholeChainProof,
    expected_vk: &RecursionVk,
) -> Result<(), TurnChainError> {
    // (0) THE COUNT BOUND. This verifier does NOT funnel through
    // `verify_turn_chain_recursive_from_parts_with_board_window` — it builds its own
    // `BabyBear::new(proof.num_turns as u32)` below — so it needs its own branch. (The first pass
    // of this fix read only the funnelling entries and would have left this one aliasing.)
    if (proof.num_turns as u64) >= BABY_BEAR_MODULUS as u64 {
        return Err(TurnChainError::ClaimedPublicsUnattested {
            reason: format!(
                "num_turns {} >= BabyBear modulus {BABY_BEAR_MODULUS}: the wide count lane would \
                 wrap mod p, making this claim indistinguishable from {} — refused",
                proof.num_turns,
                (proof.num_turns as u64) % (BABY_BEAR_MODULUS as u64)
            ),
        });
    }

    // (1) VK pin.
    let found = recursion_vk_fingerprint(&proof.root.0);
    if found != *expected_vk {
        return Err(TurnChainError::VkFingerprintMismatch {
            expected: expected_vk.to_hex(),
            found: found.to_hex(),
        });
    }

    // (2) the root — at [`turn_chain_root_config`], the engine every node ABOVE a leaf mints
    //     and verifies at. ⚠ NOT `ir2_leaf_wrap_config()`: that is the engine the leaf's CHILD
    //     (the IR-v2 descriptor batch) is minted at, and no proof in this artifact carries it.
    verify_recursive_batch_proof_with_config(&proof.root.0, &turn_chain_root_config())
        .map_err(|reason| TurnChainError::RecursionFailed { reason })?;

    // (3) THE WIDE SEGMENT TOOTH.
    let exposed = root_exposed_claims(&proof.root.0).ok_or_else(|| {
        TurnChainError::ClaimedPublicsUnattested {
            reason: "root proof carries no exposed wide segment table (segment channel absent)"
                .to_string(),
        }
    })?;
    let mut expected = Vec::with_capacity(WIDE_SEG_WIDTH);
    expected.extend_from_slice(&proof.genesis_root8);
    expected.extend_from_slice(&proof.final_root8);
    expected.push(BabyBear::new(proof.num_turns as u32));
    expected.extend_from_slice(&proof.chain_digest);
    if exposed != expected {
        return Err(TurnChainError::ClaimedPublicsUnattested {
            reason: format!(
                "root-exposed wide segment {exposed:?} != carried claim {expected:?} \
                 (the carried claim is not the fold of the real wide descriptor leaves)"
            ),
        });
    }

    Ok(())
}

// ============================================================================
// THE CARRIER CLAIM PI SLOTS (v12 STEP-3 geometry — the deployed-leg teeth the carrier fold
// arms dual-expose).
// ============================================================================

/// The factory leg's `child_vk8` claim PI base — `factoryV3Carriers` TAIL-appends the
/// child-VK octet pins (AFTER-block limbs `B_CHILD_VK_OCTET..+8`) after the narrow factory
/// PI count 47 (Lean `EffectVmEmitRotationV3.withAfterOctetPins`, commit `556970558`:
/// PI `[narrow factory piCount, +8)`). REGEN-RIDER: the committed `WIDE_REGISTRY_STAGED_TSV`
/// row still carries the pre-pin shape; the fold arm admits a leg only when its descriptor
/// actually carries these pins ([`carrier_claim_pins_admitted`]), so until the big-bang
/// descriptor regen lands the arm stays fail-closed on deployed legs.
///
/// Derived: the narrow factory is the rotated prefix plus its one new-cell-key pin, so this is
/// `ROT_PI_COUNT + 1`. It was the literal `47` until the 2026-08-07 seven-slot PI compaction.
pub const FACTORY_CHILD_VK_PI_LO: usize = dregg_circuit::effect_vm::trace_rotated::ROT_PI_COUNT + 1;
/// The hatchery leg's `contract_hash8` claim PI base — the SECOND octet cohort on the same
/// `factoryV3Carriers` descriptor (AFTER-block limbs `B_CONTRACT_HASH_OCTET..+8`, the octet
/// immediately after the child-VK octet; the hatchery carrier rides factory's
/// `CreateCellFromFactory` leg). Same regen-rider note. Derived — it was the literal `55` until
/// the 2026-08-07 seven-slot PI compaction.
pub const HATCHERY_CONTRACT_HASH_PI_LO: usize = FACTORY_CHILD_VK_PI_LO + 8;
/// The sovereign leg's `KEY_COMMIT` teeth claim PI base — **NATIVE**: the committed wide
/// registry row (`CarrierComposed.makeSovereignV3DeployedWide`, the v12 big-bang regen) pins
/// the 4 teeth columns (113..=116) at PI `[ROT_PI_COUNT + 12, +4)` (record-pin8 `ROT_PI_COUNT + 8`
/// + the 4 dsl rc, THEN the teeth, ahead of the 16 wide anchors) and welds them in-AIR to the
/// committed
/// `B_PUBKEY8` octet via the KEY_COMMIT chip gate (Lean keystone
/// `makeSovereignV3DeployedWide_publishes_key_commit`). The fold arm admits only a leg whose
/// descriptor genuinely pins these slots, so a mismatched convention fails closed.
/// Derived — it was the literal `58` until the 2026-08-07 seven-slot PI compaction.
pub const SOVEREIGN_KEY_COMMIT_PI_LO: usize =
    dregg_circuit::effect_vm::trace_rotated::ROT_PI_COUNT + 8 + 4;
/// The membership leg's `(sender_leaf, authorized_root)` claim PI base — **NATIVE**: the
/// committed wide transfer row (`CarrierComposed.transferV3MembershipWide`, the v12 big-bang
/// regen) pins the two teeth columns (past the carriers, 1771..1772) at PI
/// `[ROT_PI_COUNT + 4, +2)` (the bare rotated prefix + the 4 dsl rc, THEN the teeth, ahead of
/// the 16 anchors — Lean keystone
/// `transferV3MembershipWide_publishes_teeth`). PI-EXPOSURE leg only (the FOLD edge binds;
/// the in-AIR welds stay the named `MembershipAuthRootEdge` seams). Same fail-closed
/// admission discipline.
// ⚠ STALE AS OF 2026-08-01, IN THE DIRECTION THAT MAKES THE WOUND LOOK CLOSED.
//
// Re-measured on the emitted bytes: `transferVmDescriptor2R24` has 61 PIs (68 before the
// 2026-08-07 seven-slot compaction) and 29 pins, and there is **no `pi_binding` at
// `MEMBERSHIP_CLAIM_PI_LO` or `+1`**. Columns 1735/1736 are referenced by NOTHING, while 1730-1734
// and 1737+ all are — `dropUnforcedPins` deleted the pins and E1 compaction then removed the dead
// columns. Top pinned column is 1734.
//
// ⚑ CONSEQUENCE: `carrier_claim_pins_admitted` hard-requires the pin, so the **Membership fold arm is
// FAIL-CLOSED on every deployed leg today** — `MembershipBindingFromFold`'s flip is inert on the
// deployed object, and this tooth's *honest* pole cannot pass either. The same cause reds
// `BRIDGE_MINT_HASH_PI`.
// The teeth are not "native at 1771..1772"; they do not exist.
/// Derived — it was the literal `50` until the 2026-08-07 seven-slot PI compaction.
pub const MEMBERSHIP_CLAIM_PI_LO: usize = dregg_circuit::effect_vm::trace_rotated::ROT_PI_COUNT + 4;
/// The bridge leg's felt mint-hash claim PI — **NATIVE**: the committed mint row
/// (`mintV3BridgeHash`, the STEP-3/4 regen) pins the mint row's `param0` (`prmCol 0` — since
/// the STEP-1 executor re-align, the FELT-domain `note_spend_mint_hash_felt` over the six
/// compressed felts `apply_bridge_mint` enforces the note-spend STARK against) at PI
/// `ROT_PI_COUNT` on the FIRST row (Lean keystone `withMintHashPin_publishes`; rc rides the
/// four after it, then the 16 wide anchors). ONE lane binds the whole spend tuple: the identity
/// is the leaf's in-AIR
/// `hash_fact` chain over its own PI-pinned `(nullifier, root, value_lo, asset, dest_fed,
/// value_hi)`. Same fail-closed admission discipline.
/// Derived — it was the literal `46` until the 2026-08-07 seven-slot PI compaction.
pub const BRIDGE_MINT_HASH_PI: usize = dregg_circuit::effect_vm::trace_rotated::ROT_PI_COUNT;
/// The bridge claim length (the single felt mint identity lane).
pub const BRIDGE_MINT_HASH_CLAIM_LEN: usize = 1;

/// The DECO/Stripe leg's felt payment-identity claim PI — the deployed `stripeMint`/`decoMint`
/// row (the 8th carrier) pins the mint row's `param0` (`prmCol 0` — the FELT-domain
/// `deco_payment_hash_felt` over the PaymentFacts, `dsl::deco_payment`) at a TAIL PI on the
/// FIRST row, the twin of the bridge `withMintHashPin` (both mint-family rows share the rotated
/// base, so the identity rides the SAME `param0`/PI-46 slot convention as bridge). ONE lane
/// binds the whole payment tuple: the identity is the DECO leaf's in-AIR `hash_fact` chain over
/// its own PI-pinned `(amountCents, currency, recipient, paymentIntentId)`. Same fail-closed
/// admission discipline. ⚑ The deployed `stripeMint` descriptor EMIT (`withPaymentHashPin` +
/// the `generate_rotated_stripe_mint_wide` producer + the TSV regen) rides the coordinated
/// big-bang descriptor regen (`DECO-CARRIER-PLAN.md` §2 finale) — until it lands, `stripeMint`
/// legs are `Effect::Mint` rows that carry NO payment-hash pin, so this arm's admission
/// REFUSES them (fail-closed), never silently degrading to a fabricated fold.
/// Derived from `ROT_PI_COUNT` — it was the literal `46` until the 2026-08-07 seven-slot PI
/// compaction (`docs/PI-DISPOSITION.md` §6).
pub const DECO_PAYMENT_HASH_PI: usize = dregg_circuit::effect_vm::trace_rotated::ROT_PI_COUNT;
/// The DECO claim length (the single felt payment-identity lane).
pub const DECO_PAYMENT_HASH_CLAIM_LEN: usize = 1;

/// **The DSL/Dfa rc claim PI base — DERIVED PER MEMBER from the committed registry row.**
///
/// The dsl rc-EMIT (`withDfaRcPins`, cohort-wide) pins the 4-felt DFA route-commitment
/// carrier at FIXED trace COLUMNS (`CAVEAT_BASE + C_DFA_RC_OFF + k`, row LAST) but at
/// PER-MEMBER PI indices: the wrap appended the rc as the LAST 4 member PIs at emit time
/// (transfer 46..49), and the post-exposure v12 members appended their carrier teeth AFTER it
/// (membership teeth at 50..51 on the wide transfer; sovereign KEY_COMMIT at 58..61 past its
/// record-pin8, rc at 54..57) — so unlike factory/hatchery/sovereign/membership there is no
/// single `*_PI_LO` constant. The sound derivation reads the leg's OWN committed descriptor:
/// find the `PiBinding` that publishes rc lane 0 (column `CAVEAT_BASE + C_DFA_RC_OFF`, row
/// LAST) and take its `pi_index`; [`carrier_claim_pins_admitted`] then enforces that all
/// [`DFA_RC_LEN`](dregg_circuit::effect_vm::trace_rotated::DFA_RC_LEN) slots are contiguous
/// pins of exactly the rc columns. A descriptor with NO rc pin (the pre-rc corpus) is refused
/// — the fail-closed law.
///
/// ⚑ **AND THE COLUMN IS IN THE COMMITTED MEMBER'S COORDINATES, NOT THE LAYOUT'S.** `CAVEAT_BASE +
/// C_DFA_RC_OFF` names a column in the ORIGINAL rotated geometry, which is what the NARROW
/// `rotation-v3-staged-registry.tsv` still commits (transfer pins rc at 715..718). Every WIDE
/// registry row is S2- and E1-COMPACTED, and on the wide transfer the same carrier is committed at
/// **501** — 715 loses 120 columns across the two S2 carrier bands and a further 94 across the
/// three E1 bands. Measured 2026-07-29: this searched 715 against the wide row and found nothing,
/// so the Dsl carrier fold arm REFUSED EVERY DEPLOYED LEG — fail-closed, and therefore silent: the
/// arm has been dead, not wrong-answered. [`dsl_rc_carrier_col`] resolves the column in whichever
/// geometry the descriptor is actually in.
pub fn dsl_rc_claim_pi_lo(
    desc: &dregg_circuit::descriptor_ir2::EffectVmDescriptor2,
) -> Result<usize, String> {
    use dregg_circuit::descriptor_ir2::VmConstraint2;
    use dregg_circuit::lean_descriptor_air::{VmConstraint, VmRow};

    let rc_col0 = dsl_rc_carrier_col(desc)?;
    desc.constraints
        .iter()
        .find_map(|c| match c {
            VmConstraint2::Base(VmConstraint::PiBinding { row, col, pi_index })
                if *row == VmRow::Last && *col == rc_col0 =>
            {
                Some(*pi_index)
            }
            _ => None,
        })
        .ok_or_else(|| {
            format!(
                "dsl: leg descriptor carries NO rc pin (no last-row PiBinding at the DFA \
                 route-commitment carrier column {rc_col0}) — the pre-rc corpus, or a member \
                 outside the `withDfaRcPins` cohort; refusing to fold (fail-closed)"
            )
        })
}

/// **The DFA route-commitment carrier column IN `desc`'s OWN GEOMETRY** — lane 0 of the 4-felt rc
/// carrier the `withDfaRcPins` emit binds at row LAST.
///
/// The layout constant `CAVEAT_BASE + avail_pad + C_DFA_RC_OFF` is a column in the ORIGINAL rotated
/// geometry (the hardened `…-v1-avail` transfer/burn members shift the whole caveat region by their
/// availability pad, so the pad is part of the raw address). A NARROW `rotation-v3-staged-registry`
/// member commits exactly that geometry. A WIDE member is S2+E1 COMPACTED, so the same carrier is
/// committed at the deletion's IMAGE of that column, which
/// [`compacted_column`](dregg_circuit::effect_vm::trace_rotated::compacted_column) computes by
/// running the DEPLOYED compaction — never by an offset transcribed here.
///
/// The geometry is decided by the PI COUNT, which is the same discriminator
/// [`carrier_claim_pins_admitted`] uses: a wide leg carries at least
/// [`WIDE_PI_COUNT`](dregg_circuit::effect_vm::trace_rotated::WIDE_PI_COUNT) PIs (the rotated base
/// + the 4 rc + the 16 anchors), a narrow one cannot. Fails CLOSED — an unresolvable member, or a
/// raw column the kill-set DELETED, is a refusal, never a guessed column.
pub fn dsl_rc_carrier_col(
    desc: &dregg_circuit::descriptor_ir2::EffectVmDescriptor2,
) -> Result<usize, String> {
    use dregg_circuit::effect_vm::trace_rotated::{
        C_DFA_RC_OFF, CAVEAT_BASE, WIDE_PI_COUNT, avail_pad_for_descriptor_name, compacted_column,
        wide_registry_key_for_descriptor_name,
    };

    let raw = CAVEAT_BASE + avail_pad_for_descriptor_name(&desc.name) + C_DFA_RC_OFF;
    if desc.public_input_count < WIDE_PI_COUNT {
        // A narrow committed member is in the layout's own coordinates.
        return Ok(raw);
    }
    let key = wide_registry_key_for_descriptor_name(&desc.name)
        .map_err(|e| format!("dsl: rc carrier column for '{}': {e}", desc.name))?;
    compacted_column(key, raw)
        .map_err(|e| format!("dsl: rc carrier column for '{}': {e}", desc.name))?
        .ok_or_else(|| {
            format!(
                "dsl: the DFA route-commitment carrier column {raw} was DELETED by {key}'s S2/E1 \
                 kill-set — the committed member cannot pin it; refusing to fold (fail-closed)"
            )
        })
}

/// **THE CARRIER-CLAIM ADMISSION GATE (the fold arms' fail-closed half).** A carrier fold
/// arm may dual-expose the leg's claim slice `[claim_pi_lo .. claim_pi_lo+claim_len)` ONLY
/// when:
///
///   1. the leg is WIDE (`n >= WIDE_PI_COUNT` — the deployed-default 8-felt-anchored leaf),
///   2. the claim slice sits strictly AHEAD of the 16 wide anchor PIs (`claim_hi +
///      2*SEG_ANCHOR_WIDTH <= n`) — otherwise the "claim" lanes would alias the rotated
///      commit anchors (exactly the pre-regen deployed shape, which must REFUSE), and
///   3. the leg's descriptor CARRIES a `PiBinding` for every claim slot — the slot is
///      genuinely a published trace tooth, not an unconstrained public value. When
///      `expected_cols = Some((col_base, row))` (factory/hatchery, whose STEP-3 pin columns
///      are committed in Lean), the pin must bind exactly `col_base + k` at `row` — the
///      AFTER-block committed carrier octet — so the fold arm folds ONLY the real third-edge
///      shape.
///
/// ⚑ **THE CHILD-VK PINS FOR ONE CARRIER FOLD ARM**, TRACKED off the two children this turn just
/// minted ([`crate::fold_vk_pin`]).
///
/// Every carrier arm below folds a dual-expose leg leaf with a backing leaf through
/// `into_recursion_input`, which passed `expected_preprocessed_commit: None` — so each child's
/// preprocessed commitment (its VK-identity core) was an UNCONSTRAINED runtime public input and a
/// child of identical table shape with different constants (a valid proof of a DIFFERENT
/// descriptor) folded through leaving the parent VK byte-identical.
///
/// ⚠ **This is not a host pre-flight.** It compares nothing: it READS each child's own commitment
/// and hands it to the fold, which `connect`s it to an `alloc_const` in-circuit. A host comparison
/// would fire first and leave the in-circuit constraint untested. What a tracked pin buys is
/// consequence (2) in [`crate::fold_vk_pin`]: the pinned values land in the parent's `RecursionVk`,
/// so a substituted child moves the ROOT fingerprint a light client anchors.
///
/// Fails closed if either child carries no preprocessed commitment — an unpinnable child is refused
/// rather than folded unpinned.
fn carrier_fold_pins(
    left: &RecursionOutput<DreggRecursionConfig>,
    right: &RecursionOutput<DreggRecursionConfig>,
    index: usize,
) -> Result<crate::fold_vk_pin::FoldVkPins, TurnChainError> {
    crate::fold_vk_pin::FoldVkPins::tracked(left, right).map_err(|reason| {
        TurnChainError::TurnProofInvalid {
            index,
            reason: format!("carrier fold child VK pin unavailable: {reason}"),
        }
    })
}

/// A leg failing any tooth is REFUSED (the carrier witness never silently degrades to the
/// plain segment leaf): pre-regen deployed legs land here, which is the fail-closed law.
fn carrier_claim_pins_admitted(
    desc: &dregg_circuit::descriptor_ir2::EffectVmDescriptor2,
    leg_pis: &[BabyBear],
    claim_pi_lo: usize,
    claim_len: usize,
    carrier: &'static str,
    expected_cols: Option<(usize, dregg_circuit::lean_descriptor_air::VmRow)>,
) -> Result<(), String> {
    use dregg_circuit::descriptor_ir2::VmConstraint2;
    use dregg_circuit::effect_vm::trace_rotated::WIDE_PI_COUNT;
    use dregg_circuit::lean_descriptor_air::VmConstraint;

    let n = leg_pis.len();
    let claim_hi = claim_pi_lo + claim_len;
    if n < WIDE_PI_COUNT {
        return Err(format!(
            "carrier '{carrier}': leg is not a WIDE (8-felt-anchored) leaf ({n} PIs < \
             {WIDE_PI_COUNT}) — the carrier fold arms bind wide legs only"
        ));
    }
    if claim_hi + 2 * SEG_ANCHOR_WIDTH > n {
        return Err(format!(
            "carrier '{carrier}': the claim slice [{claim_pi_lo}..{claim_hi}) overlaps the \
             16 wide anchor PIs of the {n}-PI leg — the leg does not publish the carrier \
             claim slots (the STEP-3 octet-pin descriptor rides the big-bang regen); \
             refusing to fold (fail-closed)"
        ));
    }
    for k in 0..claim_len {
        let pi = claim_pi_lo + k;
        let found = desc.constraints.iter().find_map(|c| match c {
            VmConstraint2::Base(VmConstraint::PiBinding { row, col, pi_index })
                if *pi_index == pi =>
            {
                Some((*row, *col))
            }
            _ => None,
        });
        let (row, col) = found.ok_or_else(|| {
            format!(
                "carrier '{carrier}': leg descriptor carries NO PiBinding for claim PI {pi} \
                 — the slot is not a published trace tooth (the pinned descriptor rides the \
                 big-bang regen); refusing to fold (fail-closed)"
            )
        })?;
        if let Some((col_base, want_row)) = expected_cols {
            if col != col_base + k || row != want_row {
                return Err(format!(
                    "carrier '{carrier}': claim PI {pi} is pinned to column {col} (row \
                     {row:?}), not the committed carrier octet column {} (row {want_row:?}) \
                     — refusing to fold a claim that is not the third-edge octet",
                    col_base + k
                ));
            }
        }
    }
    Ok(())
}

/// The env knob that opts the DEFAULT chain-fold entries ([`prove_turn_chain_recursive`] and its
/// `_rotated` / `_without_host_gate` siblings — all of which route through
/// [`prove_chain_core_rotated`]) into the bounded-memory STREAMING fold. Unset ⇒ the resident
/// collect-then-fold path, byte-for-byte today's behavior. Set to an integer `>= 2` ⇒ streaming
/// with that window; set to anything else (empty, `0`, `1`, garbage) ⇒ streaming with
/// [`DEFAULT_STREAM_FOLD_WINDOW`]. The programmatic twin is
/// [`prove_turn_chain_recursive_streaming`], which takes the window explicitly.
pub const STREAM_FOLD_WINDOW_ENV: &str = "DREGG_STREAM_FOLD_WINDOW";

/// The default streaming window W. Peak resident proofs on the streaming path are about
/// `1.5 * W` (the window fold's per-level transient) plus `log2(K / W)` carry-stack sub-roots;
/// W = 8 keeps that around a dozen fat recursion proofs on ANY chain length while still letting
/// the window-internal tree amortize.
pub const DEFAULT_STREAM_FOLD_WINDOW: usize = 8;

/// How the whole-chain fold schedules leaf proving + tree aggregation. Both strategies fold the
/// IDENTICAL balanced-tree DAG (same pairing, same odd-tail promotion, same per-node
/// [`merge_two_segment_proofs`]), so both roots expose the SAME ordered segment — shape identity
/// is load-bearing because the ordered digest is NOT associative (see
/// [`aggregate_tree_streaming`]).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ChainFoldStrategy {
    /// Mint ALL K leaves, then fold the tree (today's path; the merge-pool scan-state driver
    /// when `DREGG_MERGE_WORKERS` is set). Peak resident proofs O(K) — latency-optimal on a
    /// prover farm, pathological in RAM on a long chain.
    Resident,
    /// The bounded-memory streaming fold: prove leaves in windows of `window` (floored to a
    /// power of two, min 2), fold each window to ONE sub-root, carry sub-roots in a
    /// binary-counter stack. Peak resident proofs O(window + log2(K/window)), independent of K.
    Streaming { window: usize },
}

impl ChainFoldStrategy {
    /// Read the operator opt-in ([`STREAM_FOLD_WINDOW_ENV`]); unset keeps [`Self::Resident`].
    pub fn from_env() -> Self {
        match std::env::var(STREAM_FOLD_WINDOW_ENV) {
            Err(_) => ChainFoldStrategy::Resident,
            Ok(v) => ChainFoldStrategy::Streaming {
                window: v
                    .parse::<usize>()
                    .ok()
                    .filter(|&n| n >= 2)
                    .unwrap_or(DEFAULT_STREAM_FOLD_WINDOW),
            },
        }
    }
}

/// The rotated fold core at the OPERATOR-DEFAULT fold strategy ([`ChainFoldStrategy::from_env`]:
/// resident unless `DREGG_STREAM_FOLD_WINDOW` opts into streaming).
fn prove_chain_core_rotated(
    turns: &[&FinalizedTurn],
    selectors: &[usize],
) -> Result<WholeChainProof, TurnChainError> {
    prove_chain_core_rotated_with_fold(turns, selectors, ChainFoldStrategy::from_env())
}

/// The rotated fold core: like [`prove_chain_core`] but mints rotated native-batch leaves and
/// runs LEAVES at [`ir2_leaf_wrap_config`]'s VERIFY role and every node above them at
/// [`turn_chain_root_config`] (⚠ it was ONE config for the whole tree until the leaf-wrap mint
/// split), scheduling leaf proving + aggregation per the
/// given [`ChainFoldStrategy`].
fn prove_chain_core_rotated_with_fold(
    turns: &[&FinalizedTurn],
    selectors: &[usize],
    strategy: ChainFoldStrategy,
) -> Result<WholeChainProof, TurnChainError> {
    if selectors.len() != turns.len() {
        return Err(TurnChainError::RecursionFailed {
            reason: format!(
                "selector count {} != turn count {}",
                selectors.len(),
                turns.len()
            ),
        });
    }
    // Host-side continuity (the `ChainBreak` tooth: `prev.new_root == next.old_root`). This
    // mirrors the in-circuit combine's continuity constraint and fails closed BEFORE any proving.
    generate_chain_trace_rotated_continuity(turns)?;

    // CODEX #5 — the count field is a BabyBear (mod p), so `num_turns` must be `< p` for the
    // exposed `count` lane to faithfully equal the real turn count (no modular wrap). A single
    // K-fold window of `>= p ~ 2^31` turns is far past any real finality stream, but we bound it
    // explicitly rather than rely on the implicit ceiling.
    if (turns.len() as u64) >= BABY_BEAR_MODULUS as u64 {
        return Err(TurnChainError::RecursionFailed {
            reason: format!(
                "num_turns {} >= BabyBear modulus {BABY_BEAR_MODULUS} (count lane would wrap mod p)",
                turns.len()
            ),
        });
    }

    // The ROOT SEGMENT the host computes by folding the per-turn leaf segments through the SAME
    // pairwise binary tree `aggregate_tree` runs in-circuit. Its four fields ARE the four chain
    // claims the artifact carries — derived from the REAL descriptor leaves' rotated roots, NOT
    // from a separate (swappable) binding leaf.
    let root_seg = compute_root_segment(turns);
    let genesis_root = root_seg.first_old8;
    let final_root = root_seg.last_new8;
    let chain_digest = root_seg.acc;

    // THE BOARD-WINDOW HOST MIRROR (fail-closed BEFORE any proving). If the chain declares state
    // windows, `turn[i].OUT` must already equal `turn[i+1].IN` — the in-circuit `connect` the
    // merge makes. A forged mid costs milliseconds here instead of hours of proving followed by
    // an UNSAT node.
    let board_window = compute_root_board_window(turns)?;

    // The ONE FRI engine the whole rotated tree runs at (inner proof + leaf-wrap +
    // aggregation), so the in-circuit FRI verifier params match every child's FRI engine.
    let config = ir2_leaf_wrap_config();
    // ⚑ THE FOLD ENGINE, DERIVED. A leaf wrap now emits at `recursion_layer_over(config)`'s mint
    // knobs, so every node above it verifies at those — one more application of the same rule,
    // which is its fixed point. See [`turn_chain_root_config`].
    let fold_config = recursion_layer_over(&recursion_layer_over(&config));
    let backend = create_recursion_backend();
    let params = ProveNextLayerParams::default();

    // The carried binding proof is RETAINED for byte-envelope/struct API compatibility and as a
    // host-side defense-in-depth witness of the ordered chain — but it is NO LONGER a soundness
    // dependency of `verify_turn_chain_recursive` (see its tooth list: the segment tooth (4) over
    // the root's exposed segment is what binds the claim now). It is NOT folded into the root.
    let binding_inner = prove_chain_binding_descriptor_rotated(turns)?;

    // — THE FOLD DISPATCH: two memory shapes over the SAME tree ------------------------------
    //
    // Both strategies fold the identical balanced-tree DAG, so both roots expose the SAME
    // ordered segment. The shape matters: the ordered digest `acc = H(L.acc ++ R.acc)` is NOT
    // associative — the digest encodes the tree SHAPE (pinned by the
    // `ordered_digest_combine_is_not_associative` test) — so a fold of a different shape would
    // expose a DIFFERENT chain digest and fail the verifier's segment tooth.
    //
    //   * RESIDENT (default — unchanged behavior): mint ALL K leaf proofs, then fold. Serial
    //     `aggregate_tree`, or the parallel merge-pool scan-state driver when
    //     `DREGG_MERGE_WORKERS` is set (independent merges farmed to N workers — byte-identical
    //     root; the operator THROUGHPUT knob). Peak resident proofs O(K).
    //   * STREAMING (opt-in: `DREGG_STREAM_FOLD_WINDOW` / [`prove_turn_chain_recursive_streaming`]
    //     — the operator MEMORY knob): interleave leaf PROVING with folding via
    //     [`aggregate_tree_streaming`]. Peak resident proofs O(W + log2(K/W)), independent of K.
    let root = match strategy {
        ChainFoldStrategy::Streaming { window } => {
            // FAIL-CLOSED SCHEDULE GUARD (host math, BEFORE any proving): fold the host
            // segments through the SAME streaming schedule and require equality with the
            // balanced-tree root segment (the carried claim). If the streaming schedule ever
            // diverged from `aggregate_tree`'s shape, the root would expose a different
            // (shape-sensitive) digest and the verifier's segment tooth would refuse it — this
            // guard surfaces that in milliseconds instead of after hours of proving.
            let streamed_seg = compute_root_segment_streaming(turns, window);
            if streamed_seg != root_seg {
                return Err(TurnChainError::RecursionFailed {
                    reason: format!(
                        "streaming fold schedule (window {window}) diverged from the balanced \
                         aggregate_tree segment — the ordered digest is shape-sensitive; \
                         refusing to prove a root that could not verify against the carried \
                         claim"
                    ),
                });
            }
            aggregate_tree_streaming(
                turns.len(),
                window,
                |i| mint_rotated_turn_leaf(i, turns[i], &config),
                &fold_config,
                &backend,
                &params,
            )?
        }
        ChainFoldStrategy::Resident => {
            let mut batch_leaves: Vec<RecursionOutput<DreggRecursionConfig>> =
                Vec::with_capacity(turns.len());
            for (i, t) in turns.iter().enumerate() {
                batch_leaves.push(mint_rotated_turn_leaf(i, t, &config)?);
            }
            // Aggregate the segment-carrying descriptor leaves to ONE root, COMBINING the
            // segments in-circuit at each node (continuity + count + ordered-digest fold). The
            // root's exposed segment is the whole-chain `[genesis_root, final_root, num_turns,
            // chain_digest]`.
            if crate::merge_pool::parallel_aggregation_enabled() {
                crate::merge_pool::aggregate_tree_scan_state_configured(batch_leaves)?
            } else {
                aggregate_tree(batch_leaves, &fold_config, &backend, &params)?
            }
        }
    };

    Ok(WholeChainProof {
        root,
        binding_proof: binding_inner,
        genesis_root,
        final_root,
        chain_digest,
        num_turns: turns.len(),
        board_window,
    })
}

/// Mint the ONE segment-carrying recursion leaf for finalized turn `t` at chain position `i`
/// (`i` is error attribution only) — the per-turn body of the fold, extracted so the RESIDENT
/// path (collect-then-fold) and the bounded-memory STREAMING path
/// ([`aggregate_tree_streaming`]) prove leaves through the SAME carrier-arm dispatch below.
fn mint_rotated_turn_leaf(
    i: usize,
    t: &FinalizedTurn,
    config: &DreggRecursionConfig,
) -> Result<RecursionOutput<DreggRecursionConfig>, TurnChainError> {
    // ⚑⚑ TWO ROLES, TWO CONFIGS — this function is a mini tower, not a leaf minter. `config` is
    // the engine the inner IR-v2 descriptor batches are minted at; every LEAF below derives its
    // own wrap engine from it (`recursion_layer_over`, inside the leaf functions), so a leaf now
    // emits at `create_recursion_config`'s knobs. The BINDING NODES fold those leaves, so they
    // must verify at what the leaves emit — one more application of the same rule, which is its
    // fixed point. Handing a binding node `config` instead is how a fold ends up verifying its
    // children at an engine they were not minted at.
    let fold_config = recursion_layer_over(&recursion_layer_over(config));

    // One rotated descriptor leaf per finalized turn, EACH carrying its ordered segment
    // (first_old/last_new bound to the descriptor's real roots, count=1, acc=H(old,new)).
    //
    // THE CARRIER WITNESS SOCKET (Step-2 of the uniform carrier build): the per-turn fold branch
    // is picked by matching the leg's `carrier_witness`.
    //
    // CUSTOM-BINDING DEPLOYED WIRE (the ONE deployed carrier arm): a turn whose leg carries a
    // `CarrierWitness::Custom` bundle (a `Custom`-effect turn, `customVmDescriptor2R24`) does NOT
    // get the plain segment leaf. Instead it gets a DUAL-EXPOSE leaf (segment ++ claimed 8-felt
    // `custom_proof_commitment` PI 46..53 — the proof-bind flag-day rotation; a legacy 4-felt
    // leg is version-refused at admission) folded against the RE-PROVEN custom sub-proof leaf
    // through `prove_custom_binding_node_state_segmented` — the STATE-BINDING node, the deployed
    // default. It welds TWO things in the recursion tree a pure light client folds:
    //
    //   1. the leg's CLAIMED commitment == the sub-proof's GENUINE in-circuit commitment (so a
    //      forged claim no verifying sub-proof backs is UNSAT), and
    //   2. the sub-proof's DECLARED `[old8 ‖ new8]` prefix == the leg's REAL descriptor-bound
    //      rotated roots (the segment anchors), so a sub-proof about a DIFFERENT transition —
    //      one that verifies, whose commitment is honest — is UNSAT too.
    //
    // Tooth 2 is why the leaf is the 24-lane `prove_custom_leaf_with_state_commitment`. The two
    // teeth answer the two distinct questions a light client must ask: "does a real sub-proof
    // back this commitment?" AND "is that sub-proof about THIS cell's roots?". The node
    // re-exposes only the SEGMENT, so it folds into `aggregate_tree` like any segment leaf.
    //
    // WHY THE SEGMENT ANCHORS ARE THE RIGHT COMPARAND (the semantics, since two different
    // 8-felt values in this system are both called "the commitment"): the leg's segment anchors
    // on a WIDE leg are the last 16 descriptor PIs = the v9 CHIP commit
    // (`fill_wide_block` / `wire_commit_8_chip` over the 178 rotated limbs + iroot). The
    // executor writes `stored_old8`/`claimed_new8` into exactly those tail PIs
    // (`proof_verify.rs`) and enforces the ABI prefix against those SAME values
    // (`enforce_custom_proof_state_binding`). So this connect enforces in-circuit precisely what
    // the executor enforces off-AIR — not a cousin of it. (It is NOT
    // `CellState::compute_commitment_8` / `PI[OLD_COMMIT_BASE..+8]`, the legacy bundle-path
    // commitment that also rides the wide PI prefix; those two values are different hashes over
    // different preimages and can never be equal.)
    //
    // This makes the custom binding REAL for a pure light client (the premise of
    // `CustomBindingFromFold.custom_binding_from_fold` is now TRUE on the deployed path), and
    // closes the `custom_state_binding` "tooth 2" remainder.
    //
    // THE CARRIER ARMS: ALL SEVEN are FOLD-WIRED — custom + the four v12 carriers (factory /
    // hatchery / sovereign / membership) + dsl + bridge. Each mints a dual-expose leaf at its
    // claim PI slots (gated by `carrier_claim_pins_admitted`, which REFUSES a leg whose
    // descriptor does not carry the STEP-3 claim pins — the big-bang regen tie) and binds the
    // re-proven carrier leaf under its segment-preserving binding node. A turn that WANTS the
    // re-exec rung carries `carrier_witness: None` (the sanctioned path, identical to today's
    // non-carrier turns) — EXCEPT for the custom member, which has no re-exec rung and is now
    // REFUSED on that arm (`require_no_unbacked_proof_bind`, the `None` arm below): its claim is
    // the one thing the deployed AIR does not constrain, so detaching the witness deletes the
    // claim's only enforcement rather than deferring it to a re-executing validator.
    // There is deliberately NO wildcard arm, so a new variant is a compile
    // error here (the wave must decide its fold branch).
    let leg = &t.participant.rotated;
    Ok(match &leg.carrier_witness {
        Some(CarrierWitness::Custom(bundle)) => {
            // THE PROOF-BIND CARRIER VERSION BOUNDARY (faithful flag-day v3): a leg whose
            // descriptor publishes either the RETIRED commitment4/VK4 exposure or the retired
            // commitment8/VK4 prefix is refused HERE with a TYPED error. Old custom artifacts
            // cannot re-enter at the exact commitment8+VK8 assurance rung and are never silently
            // widened, zero-padded, or prefix-matched. The detector is structural (the leg's own
            // exposure pins), the exact custom twin of the wide-carrier geometry boundary in
            // `admit_welded_leg`.
            dregg_circuit::effect_vm_descriptors::require_custom_carrier_vk8(&leg.descriptor)
                .map_err(|e| TurnChainError::TurnProofInvalid {
                    index: i,
                    reason: format!("custom proof-bind commitment version boundary: {e}"),
                })?;
            // THE ARM RE-POINT (the deployed keystone): a custom turn that DECLARES an
            // app-root weld (`bundle.app_root_binding = Some(binding)`) mints the APP-ROOT
            // node + the app-root leaf, NOT the state-only pair. MANDATORY, not a conditional
            // connect: the app-root node itself REQUIRES the wide field-exposure claim, so a
            // forging prover cannot dodge the weld by minting the narrow state leaf (a custom
            // turn with an app-root binding whose published `R != field_K` has NO satisfying
            // fold — UNSAT, no root). A custom turn with `None` is byte-identical to before
            // (the state node), so a no-app-root custom turn is UNAFFECTED.
            match &bundle.app_root_binding {
                None => {
                    let dual = prove_descriptor_leaf_dual_expose(
                        &leg.descriptor,
                        &leg.proof,
                        &leg.public_inputs,
                        config,
                    )
                    .map_err(|reason| TurnChainError::TurnProofInvalid { index: i, reason })?;
                    // THE STATE-BINDING LEAF (the deployed default for a no-app-root custom
                    // turn). The 24-lane claim `[commitment(8) ‖ pis[0..16]]` — NOT the 8-lane
                    // commitment-only leaf. A sub-program that cannot express the
                    // `custom_state_binding` ABI prefix (< 16 PIs) is REFUSED here, fail-closed,
                    // never zero-padded into a false prefix. That refusal is not new reach: the
                    // deployed EXECUTOR already refuses such a turn at
                    // `enforce_custom_proof_state_binding` (`PublicInputsTooShort`), so a chain
                    // the old prover happily minted was one no executor would accept. The prover
                    // now agrees with the verifier.
                    // THE STEP-CUTOVER SEAM: if the bundle carries a PROVEN Lean descriptor +
                    // retained trace (`descriptor_state_leaf`), mint the leaf DIRECTLY from it
                    // (proving the Lean-authored AIR) instead of lowering the Rust `CellProgram`.
                    // The exposed claim `[commitment(8) ‖ old8 ‖ new8]` is byte-identical, and the
                    // commitment + state prefix are both taken over the SAME `bundle.public_inputs`,
                    // so the state-binding node below is UNCHANGED. Fail-closed on a PI-count
                    // disagreement between the descriptor and the bundle's claimed PIs.
                    // THE BOARD-WINDOW SEAM (the two-leg fold): when the descriptor source
                    // DECLARES an IN/OUT state window, the leaf re-exposes both windows and the
                    // per-turn node carries them up instead of dropping the sub-proof's
                    // application PIs. That is what makes `left.OUT == right.IN` connectable at
                    // the merge — the mid seam, the inter-round carry, and the root's
                    // `[first.IN ‖ last.OUT]` endpoints. `None` is byte-identical to before.
                    let board_window = bundle
                        .descriptor_state_leaf
                        .as_ref()
                        .and_then(|src| src.board_window.clone());
                    let custom_leaf = match &bundle.descriptor_state_leaf {
                        Some(src) => {
                            if src.descriptor.public_input_count != bundle.public_inputs.len() {
                                return Err(TurnChainError::TurnProofInvalid {
                                    index: i,
                                    reason: format!(
                                        "direct-IR2 custom state leaf: descriptor '{}' publishes \
                                         {} PIs but the bundle claims {}",
                                        src.descriptor.name,
                                        src.descriptor.public_input_count,
                                        bundle.public_inputs.len()
                                    ),
                                });
                            }
                            match &board_window {
                                Some(bw) => {
                                    crate::custom_leaf_adapter::prove_custom_leaf_descriptor_with_board_window(
                                        &src.descriptor,
                                        &src.base_trace,
                                        &bundle.public_inputs,
                                        bw,
                                        config,
                                    )
                                    .map_err(|reason| TurnChainError::TurnProofInvalid {
                                        index: i,
                                        reason: format!(
                                            "board-window sub-proof leaf mint failed: {reason}"
                                        ),
                                    })?
                                }
                                None => {
                                    crate::custom_leaf_adapter::prove_custom_leaf_descriptor_with_state_commitment(
                                        &src.descriptor,
                                        &src.base_trace,
                                        &bundle.public_inputs,
                                        config,
                                    )
                                    .map_err(|reason| TurnChainError::TurnProofInvalid {
                                        index: i,
                                        reason: format!(
                                            "direct-IR2 custom state-binding sub-proof leaf mint failed: {reason}"
                                        ),
                                    })?
                                }
                            }
                        }
                        None => {
                            crate::custom_leaf_adapter::prove_custom_leaf_with_state_commitment(
                                &bundle.program,
                                &bundle.witness_values,
                                bundle.num_rows,
                                &bundle.public_inputs,
                                config,
                            )
                            .map_err(|reason| {
                                TurnChainError::TurnProofInvalid {
                                    index: i,
                                    reason: format!(
                                        "custom state-binding sub-proof leaf mint failed: {reason}"
                                    ),
                                }
                            })?
                        }
                    };
                    match &board_window {
                        Some(bw) => {
                            crate::joint_turn_recursive::prove_custom_binding_node_state_and_board_segmented(
                                &dual,
                                &custom_leaf,
                                &carrier_fold_pins(&dual, &custom_leaf, i)?,
                                &fold_config,
                                bw.window_len(),
                            )
                            .map_err(|e| TurnChainError::TurnProofInvalid {
                                index: i,
                                reason: format!("board-window custom-binding node failed: {e:?}"),
                            })?
                        }
                        None => {
                            crate::joint_turn_recursive::prove_custom_binding_node_state_segmented(
                                &dual,
                                &custom_leaf,
                                &carrier_fold_pins(&dual, &custom_leaf, i)?,
                                &fold_config,
                            )
                            .map_err(|e| TurnChainError::TurnProofInvalid {
                                index: i,
                                reason: format!("state-binding custom-binding node failed: {e:?}"),
                            })?
                        }
                    }
                }
                Some(binding) => {
                    if !binding.is_well_formed() {
                        return Err(TurnChainError::TurnProofInvalid {
                            index: i,
                            reason: format!(
                                "custom app-root binding {binding:?} is ill-formed (R must sit \
                                 strictly past the 16-felt state prefix and have nonzero width)"
                            ),
                        });
                    }
                    // WHERE THE LEG PUBLISHES field_K: the wide custom descriptor exposes the
                    // cell's committed field octet (the faithfully-carried `fields[0..8]` the
                    // `new8` commitment absorbs) ahead of the post-fields-root octet and the 16
                    // wide anchors — see `custom_leg_field_octet_lo`, the single derivation (the
                    // `generate_rotated_custom_wide` field-K exposure / Lean
                    // `customFieldKExposure`). `field_key` selects the lane within that octet;
                    // the claim is `L = app_root_len` felts wide starting there.
                    let n = leg.public_inputs.len();
                    let octet_lo = custom_leg_field_octet_lo(n).ok_or_else(|| {
                        TurnChainError::TurnProofInvalid {
                            index: i,
                            reason: format!(
                                "custom app-root leg publishes {n} PIs — too few to carry the \
                                 field octet ahead of the {} wide anchors; the wide custom \
                                 descriptor must expose field_K (leg-emit not present)",
                                2 * SEG_ANCHOR_WIDTH
                            ),
                        }
                    })?;
                    if binding.field_key + binding.app_root_len > CUSTOM_APP_FIELD_OCTET_LEN {
                        return Err(TurnChainError::TurnProofInvalid {
                            index: i,
                            reason: format!(
                                "custom app-root binding {binding:?}: field_key + app_root_len \
                                 exceeds the {CUSTOM_APP_FIELD_OCTET_LEN}-felt exposed field \
                                 octet"
                            ),
                        });
                    }
                    let field_k_pi_lo = octet_lo + binding.field_key;
                    let dual = prove_descriptor_leaf_expose_segment_and_claims(
                        &leg.descriptor,
                        &leg.proof,
                        &leg.public_inputs,
                        config,
                        &[
                            (
                                crate::joint_turn_recursive::CUSTOM_COMMIT_PI_LO,
                                crate::joint_turn_recursive::CUSTOM_COMMIT_LEN,
                            ),
                            (field_k_pi_lo, binding.app_root_len),
                        ],
                    )
                    .map_err(|reason| TurnChainError::TurnProofInvalid { index: i, reason })?;
                    // THE APP-ROOT LEAF: `[commitment(8) ‖ old8 ‖ new8 ‖ R(L)]` — re-exposes
                    // the sub-proof's published root R for the fold to connect. Fail-closed on
                    // a sub-program that cannot carry the binding.
                    let custom_leaf =
                        crate::custom_leaf_adapter::prove_custom_leaf_with_app_root_commitment(
                            &bundle.program,
                            &bundle.witness_values,
                            bundle.num_rows,
                            &bundle.public_inputs,
                            binding,
                            config,
                        )
                        .map_err(|reason| {
                            TurnChainError::TurnProofInvalid {
                                index: i,
                                reason: format!(
                                    "custom app-root sub-proof leaf mint failed: {reason}"
                                ),
                            }
                        })?;
                    crate::joint_turn_recursive::prove_custom_binding_node_app_root_segmented(
                        &dual,
                        &custom_leaf,
                        &carrier_fold_pins(&dual, &custom_leaf, i)?,
                        &fold_config,
                        binding.app_root_len,
                    )
                    .map_err(|e| TurnChainError::TurnProofInvalid {
                        index: i,
                        reason: format!("app-root custom-binding node failed: {e:?}"),
                    })?
                }
            }
        }
        // DIRECT IR2 CUSTOM ARM: re-prove the exact Lean-authored descriptor and
        // connect commitment8, state roots, app root, and canonical program VK8
        // to the faithful custom-wide leg inside one binding node.
        Some(CarrierWitness::CustomIr2(bundle)) => {
            dregg_circuit::effect_vm_descriptors::require_custom_carrier_vk8(&leg.descriptor)
                .map_err(|e| TurnChainError::TurnProofInvalid {
                    index: i,
                    reason: format!("direct-IR2 custom carrier version boundary: {e}"),
                })?;
            bundle
                .vk_recipe
                .require_exact_descriptor(&bundle.descriptor)
                .map_err(|reason| TurnChainError::TurnProofInvalid { index: i, reason })?;
            let direct_vk8 = bundle.vk_recipe.canonical_vk_felts();
            let leg_vk8 = leg
                .public_inputs
                .get(
                    CUSTOM_PROGRAM_VK_PI_LO
                        ..CUSTOM_PROGRAM_VK_PI_LO + DEPLOYED_CUSTOM_PROGRAM_VK_PI_LEN,
                )
                .ok_or_else(|| TurnChainError::TurnProofInvalid {
                    index: i,
                    reason: DIRECT_IR2_VK8_REFUSAL.to_string(),
                })?;
            require_direct_ir2_leg_vk8(leg_vk8, direct_vk8)
                .map_err(|reason| TurnChainError::TurnProofInvalid { index: i, reason })?;

            let binding = &bundle.app_root_binding;
            if !binding.is_well_formed()
                || binding.field_key + binding.app_root_len > CUSTOM_APP_FIELD_OCTET_LEN
            {
                return Err(TurnChainError::TurnProofInvalid {
                    index: i,
                    reason: format!("direct-IR2 custom app-root binding {binding:?} is ill-formed"),
                });
            }
            let n = leg.public_inputs.len();
            let octet_lo =
                custom_leg_field_octet_lo(n).ok_or_else(|| TurnChainError::TurnProofInvalid {
                    index: i,
                    reason: format!("direct-IR2 custom leg publishes only {n} PIs"),
                })?;
            match &bundle.post_fields_root_binding {
                None => {
                    let dual = prove_descriptor_leaf_expose_segment_and_claims(
                        &leg.descriptor,
                        &leg.proof,
                        &leg.public_inputs,
                        config,
                        &[
                            (
                                crate::joint_turn_recursive::CUSTOM_COMMIT_PI_LO,
                                crate::joint_turn_recursive::CUSTOM_COMMIT_LEN,
                            ),
                            (octet_lo + binding.field_key, binding.app_root_len),
                            (CUSTOM_PROGRAM_VK_PI_LO, DEPLOYED_CUSTOM_PROGRAM_VK_PI_LEN),
                        ],
                    )
                    .map_err(|reason| TurnChainError::TurnProofInvalid { index: i, reason })?;
                    let direct_leaf =
                        crate::custom_leaf_adapter::prove_direct_ir2_leaf_with_app_root_commitment(
                            &bundle.descriptor,
                            &bundle.base_trace,
                            &bundle.public_inputs,
                            &bundle.vk_recipe,
                            binding,
                            config,
                        )
                        .map_err(|reason| TurnChainError::TurnProofInvalid { index: i, reason })?;
                    crate::joint_turn_recursive::prove_direct_ir2_binding_node_app_root_segmented(
                        &dual,
                        &direct_leaf,
                        &carrier_fold_pins(&dual, &direct_leaf, i)?,
                        &fold_config,
                        binding.app_root_len,
                    )
                    .map_err(|e| TurnChainError::TurnProofInvalid {
                        index: i,
                        reason: format!("direct-IR2 custom binding node failed: {e:?}"),
                    })?
                }
                Some(fields_binding) => {
                    if !fields_binding.is_well_formed() {
                        return Err(TurnChainError::TurnProofInvalid {
                            index: i,
                            reason: format!(
                                "direct-IR2 custom post-fields-root binding {fields_binding:?} \
                                 is ill-formed"
                            ),
                        });
                    }
                    let fields_root_lo = n
                        .checked_sub(2 * SEG_ANCHOR_WIDTH + CUSTOM_POST_FIELDS_ROOT_LEN)
                        .ok_or_else(|| TurnChainError::TurnProofInvalid {
                            index: i,
                            reason: format!(
                                "direct-IR2 custom leg publishes only {n} PIs; no faithful \
                                 post-fields-root octet precedes its state anchors"
                            ),
                        })?;
                    let dual = prove_descriptor_leaf_expose_segment_and_claims(
                        &leg.descriptor,
                        &leg.proof,
                        &leg.public_inputs,
                        config,
                        &[
                            (
                                crate::joint_turn_recursive::CUSTOM_COMMIT_PI_LO,
                                crate::joint_turn_recursive::CUSTOM_COMMIT_LEN,
                            ),
                            (octet_lo + binding.field_key, binding.app_root_len),
                            (fields_root_lo, CUSTOM_POST_FIELDS_ROOT_LEN),
                            (CUSTOM_PROGRAM_VK_PI_LO, DEPLOYED_CUSTOM_PROGRAM_VK_PI_LEN),
                        ],
                    )
                    .map_err(|reason| TurnChainError::TurnProofInvalid { index: i, reason })?;
                    let direct_leaf = crate::custom_leaf_adapter::
                        prove_direct_ir2_leaf_with_app_and_fields_root_commitment(
                            &bundle.descriptor,
                            &bundle.base_trace,
                            &bundle.public_inputs,
                            &bundle.vk_recipe,
                            binding,
                            fields_binding,
                            config,
                        )
                        .map_err(|reason| TurnChainError::TurnProofInvalid { index: i, reason })?;
                    crate::joint_turn_recursive::
                        prove_direct_ir2_binding_node_app_and_fields_root_segmented(
                            &dual,
                            &direct_leaf,
                            &carrier_fold_pins(&dual, &direct_leaf, i)?,
                            &fold_config,
                            binding.app_root_len,
                        )
                        .map_err(|e| TurnChainError::TurnProofInvalid {
                            index: i,
                            reason: format!(
                                "direct-IR2 custom fields-root binding node failed: {e:?}"
                            ),
                        })?
                }
            }
        }
        // THE BRIDGE FOLD ARM (the 7th carrier) — the named residual CLOSED by the
        // felt-domain mint_hash thread: (STEP 1) the executor re-aligned `mint_hash` to
        // the FELT-domain `note_spend_mint_hash_felt` (the `687601953` precedent — over
        // the six compressed felts `apply_bridge_mint` enforces the REAL note-spend STARK
        // against); (STEP 2/3/4) the deployed `mintVmDescriptor2R24` (`mintV3BridgeHash`)
        // pins the mint row's `param0` at PI 46, producer-filled. The arm mirrors the
        // factory shape: (1) ADMIT the leg's claim slot (fail-closed on a pin-less or
        // wrong-column descriptor — the regen tie; the expected pin is the FIRST-row
        // `prmCol 0`, never a free column), (2) mint the DUAL-EXPOSE leaf (segment ++ the
        // published mint identity), (3) re-prove the REAL foreign note-spend STARK as the
        // G2 backing leaf (`prove_note_spend_leaf_with_claim` — spending-key knowledge +
        // Merkle membership + full-width commitment, with the mint identity recomputed
        // IN-AIR at lane 6; the binding-only `bridge_action_air` was REFUSED as backing),
        // (4) fold under the mint-hash binding node — the in-circuit `connect` makes a
        // published mint identity no verifying note-spend backs UNSAT.
        Some(CarrierWitness::Bridge(bundle)) => {
            use dregg_circuit::effect_vm::columns::{PARAM_BASE, param};
            use dregg_circuit::lean_descriptor_air::VmRow;
            carrier_claim_pins_admitted(
                &leg.descriptor,
                &leg.public_inputs,
                BRIDGE_MINT_HASH_PI,
                BRIDGE_MINT_HASH_CLAIM_LEN,
                "bridge",
                Some((PARAM_BASE + param::MINT_HASH, VmRow::First)),
            )
            .map_err(|reason| TurnChainError::TurnProofInvalid { index: i, reason })?;
            let dual = prove_descriptor_leaf_dual_expose_at(
                &leg.descriptor,
                &leg.proof,
                &leg.public_inputs,
                config,
                BRIDGE_MINT_HASH_PI,
                BRIDGE_MINT_HASH_CLAIM_LEN,
            )
            .map_err(|reason| TurnChainError::TurnProofInvalid { index: i, reason })?;
            let backing = crate::note_spend_leaf_adapter::prove_note_spend_leaf_with_claim(
                &bundle.note_spend,
                &bundle.public_inputs,
                config,
            )
            .map_err(|reason| TurnChainError::TurnProofInvalid {
                index: i,
                reason: format!("bridge note-spend backing leaf mint failed: {reason}"),
            })?;
            crate::note_spend_leaf_adapter::prove_note_spend_mint_binding_node_segmented(
                &dual,
                &backing,
                &carrier_fold_pins(&dual, &backing, i)?,
                &fold_config,
            )
            .map_err(|e| TurnChainError::TurnProofInvalid {
                index: i,
                reason: format!("segmented bridge mint-hash binding node failed: {e:?}"),
            })?
        }
        // THE DECO/Stripe money-in FOLD ARM (the 8th carrier) — the fiat twin of the
        // bridge arm (`DECO-CARRIER-PLAN.md` Option B, the bridge-style commitment fold):
        // (1) ADMIT the leg's payment-hash claim slot (fail-closed on a pin-less or
        // wrong-column descriptor — the expected pin is the FIRST-row `prmCol 0`, the
        // deployed `stripeMint` twin of `withMintHashPin`; until the descriptor regen
        // lands a Stripe `Effect::Mint` leg has no such pin and is REFUSED), (2) mint the
        // DUAL-EXPOSE leaf (segment ++ the published payment identity), (3) re-prove the
        // DECO commitment leaf (`prove_deco_leaf_with_claim` — a Poseidon2-only AIR
        // recomputing the felt identity IN-AIR from PI-pinned PaymentFacts; ed25519/HMAC/
        // SHA-256 stay OFF-AIR as named §8 carriers, mirroring bridge's ed25519), (4) fold
        // under the payment-hash binding node — the in-circuit `connect` makes a published
        // payment identity no verifying DECO commitment backs UNSAT.
        Some(CarrierWitness::Deco(bundle)) => {
            use dregg_circuit::effect_vm::columns::{PARAM_BASE, param};
            use dregg_circuit::lean_descriptor_air::VmRow;
            carrier_claim_pins_admitted(
                &leg.descriptor,
                &leg.public_inputs,
                DECO_PAYMENT_HASH_PI,
                DECO_PAYMENT_HASH_CLAIM_LEN,
                "deco",
                Some((PARAM_BASE + param::MINT_HASH, VmRow::First)),
            )
            .map_err(|reason| TurnChainError::TurnProofInvalid { index: i, reason })?;
            let dual = prove_descriptor_leaf_dual_expose_at(
                &leg.descriptor,
                &leg.proof,
                &leg.public_inputs,
                config,
                DECO_PAYMENT_HASH_PI,
                DECO_PAYMENT_HASH_CLAIM_LEN,
            )
            .map_err(|reason| TurnChainError::TurnProofInvalid { index: i, reason })?;
            let backing = crate::deco_leaf_adapter::prove_deco_leaf_with_claim(
                &bundle.witness,
                &bundle.public_inputs,
                config,
            )
            .map_err(|reason| TurnChainError::TurnProofInvalid {
                index: i,
                reason: format!("deco payment backing leaf mint failed: {reason}"),
            })?;
            crate::deco_leaf_adapter::prove_deco_payment_binding_node_segmented(
                &dual,
                &backing,
                &carrier_fold_pins(&dual, &backing, i)?,
                &fold_config,
            )
            .map_err(|e| TurnChainError::TurnProofInvalid {
                index: i,
                reason: format!("segmented deco payment-binding node failed: {e:?}"),
            })?
        }
        // THE DSL/Dfa FOLD ARM (the 6th carrier) — mirrors the Custom arm term-for-term
        // (the dsl adapter REUSES custom's leaf + binding-node machinery; the claim shape
        // is the SAME 4-felt PI-commitment). Differences, both fail-closed:
        //
        //   * the rc claim slots are DERIVED per member from the leg's committed
        //     descriptor ([`dsl_rc_claim_pi_lo`] — the `withDfaRcPins` pins ride at fixed
        //     COLUMNS but per-member PI indices), then admitted through
        //     `carrier_claim_pins_admitted` with the rc columns as the expected pins;
        //   * the ZERO SENTINEL is REFUSED: a turn without a Dfa caveat publishes rc = 0
        //     (`RotatedCaveatManifest::dfa_rc` default) — folding a witness against it
        //     would bind a vacuous claim no predicate gated. Such a turn takes the
        //     re-exec rung (`carrier_witness: None`), never a fabricated fold.
        Some(CarrierWitness::Dsl(bundle)) => {
            use dregg_circuit::effect_vm::trace_rotated::DFA_RC_LEN;
            use dregg_circuit::lean_descriptor_air::VmRow;
            let rc_lo = dsl_rc_claim_pi_lo(&leg.descriptor)
                .map_err(|reason| TurnChainError::TurnProofInvalid { index: i, reason })?;
            // ONE resolver for the carrier column (`dsl_rc_carrier_col`): the avail pad on the
            // hardened `…-v1-avail` members AND the S2/E1 compaction of a WIDE committed row. This
            // recomputed the RAW column beside a `dsl_rc_claim_pi_lo` that had done the same, so
            // the two agreed with each other and disagreed with the committed member.
            let rc_col0 = dsl_rc_carrier_col(&leg.descriptor)
                .map_err(|reason| TurnChainError::TurnProofInvalid { index: i, reason })?;
            carrier_claim_pins_admitted(
                &leg.descriptor,
                &leg.public_inputs,
                rc_lo,
                DFA_RC_LEN,
                "dsl",
                Some((rc_col0, VmRow::Last)),
            )
            .map_err(|reason| TurnChainError::TurnProofInvalid { index: i, reason })?;
            if leg.public_inputs[rc_lo..rc_lo + DFA_RC_LEN]
                .iter()
                .all(|f| *f == BabyBear::ZERO)
            {
                return Err(TurnChainError::TurnProofInvalid {
                    index: i,
                    reason: format!(
                        "dsl: the leg's published route-commitment at PI {rc_lo}..{} is the \
                         ZERO sentinel (no Dfa caveat gated this turn) — refusing to fold a \
                         vacuous claim; detach the witness (carrier_witness: None) to take \
                         the re-exec rung",
                        rc_lo + DFA_RC_LEN
                    ),
                });
            }
            let dual = prove_descriptor_leaf_dual_expose_at(
                &leg.descriptor,
                &leg.proof,
                &leg.public_inputs,
                config,
                rc_lo,
                DFA_RC_LEN,
            )
            .map_err(|reason| TurnChainError::TurnProofInvalid { index: i, reason })?;
            let dsl_leaf = crate::dsl_leaf_adapter::prove_dsl_leaf_with_commitment(
                &bundle.program,
                &bundle.witness_values,
                bundle.num_rows,
                &bundle.public_inputs,
                config,
            )
            .map_err(|reason| TurnChainError::TurnProofInvalid {
                index: i,
                reason: format!("dsl sub-proof leaf mint failed: {reason}"),
            })?;
            crate::dsl_leaf_adapter::prove_dsl_binding_node_segmented(
                &dual,
                &dsl_leaf,
                &carrier_fold_pins(&dual, &dsl_leaf, i)?,
                &fold_config,
            )
            .map_err(|e| TurnChainError::TurnProofInvalid {
                index: i,
                reason: format!("segmented dsl-binding node failed: {e:?}"),
            })?
        }
        // THE FOUR v12 CARRIER FOLD ARMS (factory · hatchery · sovereign · membership) —
        // each mirrors the Custom arm: (1) ADMIT the leg's claim slots through
        // `carrier_claim_pins_admitted` (fail-closed until the STEP-3 pinned descriptor is
        // the leg's descriptor — the big-bang regen tie), (2) mint the DUAL-EXPOSE leaf
        // (segment ++ the leg's claimed carrier teeth) at the carrier's claim PI slots,
        // (3) re-prove the carrier's backing tuple as its adapter leaf, (4) fold both
        // under the segment-preserving binding node — the in-circuit `connect` makes a
        // forged claim (no backing leaf binds it) UNSAT, and the node re-exposes the
        // chain segment so it folds into `aggregate_tree` like any per-turn leaf.
        Some(CarrierWitness::Factory(bundle)) => {
            use dregg_circuit::effect_vm::trace_rotated::{AFTER_BASE, B_CHILD_VK_OCTET};
            use dregg_circuit::lean_descriptor_air::VmRow;
            carrier_claim_pins_admitted(
                &leg.descriptor,
                &leg.public_inputs,
                FACTORY_CHILD_VK_PI_LO,
                crate::factory_leaf_adapter::FACTORY_CHILD_VK_CLAIM_LEN,
                "factory",
                Some((AFTER_BASE + B_CHILD_VK_OCTET, VmRow::Last)),
            )
            .map_err(|reason| TurnChainError::TurnProofInvalid { index: i, reason })?;
            let dual = prove_descriptor_leaf_dual_expose_at(
                &leg.descriptor,
                &leg.proof,
                &leg.public_inputs,
                config,
                FACTORY_CHILD_VK_PI_LO,
                crate::factory_leaf_adapter::FACTORY_CHILD_VK_CLAIM_LEN,
            )
            .map_err(|reason| TurnChainError::TurnProofInvalid { index: i, reason })?;
            let backing = crate::factory_leaf_adapter::prove_factory_leaf_with_child_vk_claim(
                &bundle.backing,
                &bundle.public_inputs,
                config,
            )
            .map_err(|reason| TurnChainError::TurnProofInvalid {
                index: i,
                reason: format!("factory backing leaf mint failed: {reason}"),
            })?;
            crate::factory_leaf_adapter::prove_factory_binding_node_segmented(
                &dual,
                &backing,
                &carrier_fold_pins(&dual, &backing, i)?,
                &fold_config,
            )
            .map_err(|e| TurnChainError::TurnProofInvalid {
                index: i,
                reason: format!("segmented factory-binding node failed: {e:?}"),
            })?
        }
        Some(CarrierWitness::Hatchery(bundle)) => {
            use dregg_circuit::effect_vm::trace_rotated::{AFTER_BASE, B_CONTRACT_HASH_OCTET};
            use dregg_circuit::lean_descriptor_air::VmRow;
            carrier_claim_pins_admitted(
                &leg.descriptor,
                &leg.public_inputs,
                HATCHERY_CONTRACT_HASH_PI_LO,
                crate::hatchery_leaf_adapter::HATCHERY_CONTRACT_CLAIM_LEN,
                "hatchery",
                Some((AFTER_BASE + B_CONTRACT_HASH_OCTET, VmRow::Last)),
            )
            .map_err(|reason| TurnChainError::TurnProofInvalid { index: i, reason })?;
            let dual = prove_descriptor_leaf_dual_expose_at(
                &leg.descriptor,
                &leg.proof,
                &leg.public_inputs,
                config,
                HATCHERY_CONTRACT_HASH_PI_LO,
                crate::hatchery_leaf_adapter::HATCHERY_CONTRACT_CLAIM_LEN,
            )
            .map_err(|reason| TurnChainError::TurnProofInvalid { index: i, reason })?;
            let attestation =
                crate::hatchery_leaf_adapter::prove_hatchery_leaf_with_contract_claim(
                    &bundle.attestation,
                    &bundle.public_inputs,
                    config,
                )
                .map_err(|reason| TurnChainError::TurnProofInvalid {
                    index: i,
                    reason: format!("hatchery attestation leaf mint failed: {reason}"),
                })?;
            crate::hatchery_leaf_adapter::prove_hatchery_binding_node_segmented(
                &dual,
                &attestation,
                &carrier_fold_pins(&dual, &attestation, i)?,
                &fold_config,
            )
            .map_err(|e| TurnChainError::TurnProofInvalid {
                index: i,
                reason: format!("segmented hatchery-binding node failed: {e:?}"),
            })?
        }
        Some(CarrierWitness::Sovereign(bundle)) => {
            carrier_claim_pins_admitted(
                &leg.descriptor,
                &leg.public_inputs,
                SOVEREIGN_KEY_COMMIT_PI_LO,
                crate::sovereign_leaf_adapter::SOVEREIGN_KEY_CLAIM_LEN,
                "sovereign",
                // The teeth columns are pinned by the regen (the KEY_COMMIT teeth cols;
                // `CarrierComposed` keeps them parametric until the emit), so the
                // admission requires a genuine PiBinding at every claim slot without
                // fixing the column base.
                None,
            )
            .map_err(|reason| TurnChainError::TurnProofInvalid { index: i, reason })?;
            let dual = prove_descriptor_leaf_dual_expose_at(
                &leg.descriptor,
                &leg.proof,
                &leg.public_inputs,
                config,
                SOVEREIGN_KEY_COMMIT_PI_LO,
                crate::sovereign_leaf_adapter::SOVEREIGN_KEY_CLAIM_LEN,
            )
            .map_err(|reason| TurnChainError::TurnProofInvalid { index: i, reason })?;
            let authority = crate::sovereign_leaf_adapter::prove_sovereign_leaf_with_key_claim(
                &bundle.authority,
                &bundle.public_inputs,
                config,
            )
            .map_err(|reason| TurnChainError::TurnProofInvalid {
                index: i,
                reason: format!("sovereign authority leaf mint failed: {reason}"),
            })?;
            crate::joint_turn_recursive::prove_sovereign_binding_node_segmented(
                &dual,
                &authority,
                &carrier_fold_pins(&dual, &authority, i)?,
                &fold_config,
            )
            .map_err(|e| TurnChainError::TurnProofInvalid {
                index: i,
                reason: format!("segmented sovereign-binding node failed: {e:?}"),
            })?
        }
        Some(CarrierWitness::Membership(bundle)) => {
            carrier_claim_pins_admitted(
                &leg.descriptor,
                &leg.public_inputs,
                MEMBERSHIP_CLAIM_PI_LO,
                crate::membership_leaf_adapter::MEMBERSHIP_CLAIM_LEN,
                "membership",
                // The (sender_leaf, authorized_root) tooth columns are parametric until
                // the regen pins them (`MembershipAuthRootEdge` builds the edge over a
                // parametric base) — same column-free admission as sovereign.
                None,
            )
            .map_err(|reason| TurnChainError::TurnProofInvalid { index: i, reason })?;
            let dual = prove_descriptor_leaf_dual_expose_at(
                &leg.descriptor,
                &leg.proof,
                &leg.public_inputs,
                config,
                MEMBERSHIP_CLAIM_PI_LO,
                crate::membership_leaf_adapter::MEMBERSHIP_CLAIM_LEN,
            )
            .map_err(|reason| TurnChainError::TurnProofInvalid { index: i, reason })?;
            let membership = crate::membership_leaf_adapter::prove_membership_leaf_with_claim(
                &bundle.membership,
                &bundle.public_inputs,
                config,
            )
            .map_err(|reason| TurnChainError::TurnProofInvalid {
                index: i,
                reason: format!("membership leaf mint failed: {reason}"),
            })?;
            crate::membership_leaf_adapter::prove_membership_binding_node_segmented(
                &dual,
                &membership,
                &carrier_fold_pins(&dual, &membership, i)?,
                &fold_config,
            )
            .map_err(|e| TurnChainError::TurnProofInvalid {
                index: i,
                reason: format!("segmented membership-binding node failed: {e:?}"),
            })?
        }
        None => {
            // THE ARM-SELECTION FAIL-CLOSED (the exact twin of the Custom arm's
            // `require_custom_carrier_vk8` version boundary, on the other polarity). That guard
            // asks "does a leg WITH a custom witness publish the live exposure?"; this one asks
            // the question nothing asked before: "is this leg ALLOWED on the unbound arm at all?"
            //
            // WHY IT HAS TO BE HERE. `carrier_witness` is a plain `pub` field the prover fills
            // in, and the arm is chosen by matching it. For every member except one that is
            // sound — `None` IS the sanctioned re-exec rung, and the leg's own AIR constrains
            // everything it publishes. The custom member is the exception, because what it
            // publishes at IR2 PI 46..53 is a CLAIM about an external sub-proof and the deployed
            // AIR does not constrain it: the evaluator (`Ir2Air::Main`) has no `ProofBind` arm at
            // all, and the sixteen `pi_binding` pins only PUBLISH the binding columns. The single
            // thing that makes the claim mean anything is the Custom arm's connect
            // (`joint_turn_recursive`, the leg's re-exposed PI 46..53 tied lane-by-lane to the
            // re-proven sub-proof leaf's genuine in-circuit commitment). Dropping the witness
            // therefore did not weaken the claim — it DELETED its only enforcement, and a light
            // client folding the root cannot observe which arm was taken.
            //
            // KEYED ON DESCRIPTOR IDENTITY, never on a caller-passed flag: the leg's own
            // committed descriptor declaring a `DescriptorIR2.ProofBind` op IS the custom member
            // (measured across all three staged registries — exactly one declarer each, always
            // `customVmDescriptor2R24`). A prover cannot dodge the guard by lying about intent;
            // it would have to present a different descriptor, which is a different leg.
            //
            // NO CARVE-OUT. There is deliberately no "zero-commitment sentinel" escape here (the
            // Dsl arm's zero-rc sentinel routes the OTHER way — it refuses to FOLD a vacuous
            // claim). A proof-bind member has no re-exec rung to fall back to.
            dregg_circuit::effect_vm_descriptors::require_no_unbacked_proof_bind(&leg.descriptor)
                .map_err(|e| TurnChainError::TurnProofInvalid {
                index: i,
                reason: format!("unbacked proof-bind arm selection: {e}"),
            })?;
            prove_descriptor_leaf_rotated_with_segment(
                &leg.descriptor,
                &leg.proof,
                &leg.public_inputs,
                config,
            )
            .map_err(|reason| TurnChainError::TurnProofInvalid { index: i, reason })?
        }
    })
}

// (The `unfilled_carrier_arm` fail-closed refusal helper is RETIRED: every `CarrierWitness`
// variant is fold-wired — custom/factory/hatchery/sovereign/membership/dsl/bridge. The
// fail-closed discipline lives on in `carrier_claim_pins_admitted` (a leg whose descriptor
// does not genuinely pin the claim slots is refused) and in the no-wildcard match (a NEW
// variant is a compile error until its wave decides its fold branch).)

/// Host-side continuity check ONLY (the `ChainBreak` tooth), extracted so the rotated fold no
/// longer needs the full binding-trace generation just to validate ordering. Returns `Ok(())`
/// when `>= 2` turns and every `prev.new_root == next.old_root`.
fn generate_chain_trace_rotated_continuity(turns: &[&FinalizedTurn]) -> Result<(), TurnChainError> {
    if turns.len() < 2 {
        return Err(TurnChainError::TooFewTurns { count: turns.len() });
    }
    // H0 DEPLOYED-WIDE: continuity is checked at the GENUINE 8-felt anchor ([`turn_anchors8`]) — the
    // SAME lane-by-lane endpoints the in-circuit segment combine binds (`L.last_new8 == R.first_old8`,
    // accumulator.rs). For a WIDE leg these are the ~124-bit faithful anchors (the single-felt rotated
    // roots PI 42/43 are RETIRED to zero, so the old 1-felt check would be vacuously 0==0); for a
    // narrow leg they are the single rotated commit felt broadcast across all eight lanes, so the
    // check degrades exactly to the prior 1-felt continuity. Either way the host pre-check mirrors the
    // in-circuit tooth and never passes vacuously on a wide chain break.
    for i in 1..turns.len() {
        let (_, prev_new) = turn_anchors8(turns[i - 1]);
        let (this_old, _) = turn_anchors8(turns[i]);
        if prev_new != this_old {
            return Err(TurnChainError::ChainBreak {
                index: i,
                expected_old_root: prev_new[0].0,
                found_old_root: this_old[0].0,
            });
        }
    }
    Ok(())
}

/// Prove and self-verify one witness against the registered Lean-emitted turn-chain descriptor.
/// The resulting IR-v2 batch proof is carried alongside the recursion root and verified directly;
/// it is not wrapped into the recursive tree.
fn prove_turn_chain_binding_trace(
    trace: &[Vec<BabyBear>],
    pis: &[BabyBear],
) -> Result<TurnChainBindingProof, String> {
    let desc = descriptor_by_name(TURN_CHAIN_BINDING_NAME).ok_or_else(|| {
        format!("Lean-emitted descriptor {TURN_CHAIN_BINDING_NAME:?} is not registered")
    })?;
    let proof = prove_vm_descriptor2(&desc, trace, pis, &MemBoundaryWitness::default(), &[])?;
    verify_vm_descriptor2(&desc, &proof, pis)?;
    let public_inputs: [u32; 4] = pis
        .iter()
        .map(|v| v.as_u32())
        .collect::<Vec<_>>()
        .try_into()
        .map_err(|v: Vec<u32>| format!("turn-chain descriptor needs 4 PIs, got {}", v.len()))?;
    Ok(TurnChainBindingProof {
        proof,
        public_inputs,
    })
}

/// Prove the Lean-emitted turn-chain binding descriptor from scalar endpoint pairs. Shared by the
/// finite K-fold and the online accumulator so both deployed producers use one descriptor path.
pub(crate) fn prove_turn_chain_binding_for_roots(
    root_pairs: &[(BabyBear, BabyBear)],
) -> Result<TurnChainBindingProof, String> {
    let (trace, pis) = turn_chain_binding_witness(root_pairs)?;
    prove_turn_chain_binding_trace(&trace, &pis)
}

fn prove_chain_binding_descriptor_rotated(
    turns: &[&FinalizedTurn],
) -> Result<TurnChainBindingProof, TurnChainError> {
    // Keep the production turn-consuming trace generator: it validates and projects the mandatory
    // rotated legs, then delegates row construction to the chip-lane witness builder.
    let (trace, pis, _digest) = generate_chain_trace_rotated(turns)?;
    prove_turn_chain_binding_trace(&trace, &pis)
        .map_err(|reason| TurnChainError::RecursionFailed { reason })
}

/// The runtime preprocessed-commitment value type for the recursion config — a child proof's
/// VK-identity core (a Merkle cap). This is what lever (a)'s in-circuit pin constrains; the merge
/// primitive extracts it directly from a bare [`BatchStarkProof`] (the host mirror of
/// [`RecursionOutput::running_preprocessed_commit`]).
pub(crate) type RecursionCommit =
    <<DreggRecursionConfig as p3_uni_stark::StarkGenericConfig>::Pcs as p3_commit::Pcs<
        <DreggRecursionConfig as p3_uni_stark::StarkGenericConfig>::Challenge,
        <DreggRecursionConfig as p3_uni_stark::StarkGenericConfig>::Challenger,
    >>::Commitment;

/// **THE SEGMENT-COMBINE EXPOSE HOOK** — factored out of [`aggregate_tree`]'s inner loop so the
/// serial tree fold AND the parallel scan-state driver (the [`crate::merge_pool`]) drive the SAME
/// per-node math: state continuity (`L.last_new == R.first_old`, by direct `connect` — never
/// `sub`+`assert_zero`, which would clobber the shared `WitnessId(0)`), count additivity
/// (`count = L.count + R.count`), the ordered multi-felt digest fold (`acc = commit(L.acc ++ R.acc)`,
/// L absorbed before R ⇒ order-sensitive), then expose the parent `[first_old, last_new, count, acc]`.
/// Because both paths call this ONE function, the parallel root is byte-identical to the serial root.
///
/// ⚑⚑ **`pub` SINCE 2026-08-11, AND THE REASON IS A MEASURED TEST DEFECT.** While this was
/// `pub(crate)`, `circuit-prove/tests/ivc_turn_chain_rotated.rs` — an integration test, which links
/// this crate as an external rlib and so cannot see `pub(crate)` — carried THREE hand-rolled
/// mirrors of the body below. They could not track it, and they did not: every one still built a
/// `SEG_WIDTH`-lane parent after the VK spine widened the exposure to `SEG_SPINE_WIDTH`, so
/// `mixed_root_forgery_executes_A_claims_B` was passing on the verifier's *pre-spine artifact*
/// SHAPE GUARD rather than on the segment tooth its name and its whole docblock claim. A mirror of
/// a `pub(crate)` function is not a copy, it is a fork with a deadline; the visibility was the
/// cheaper thing to change.
pub fn segment_combine_expose(
    cb: &mut p3_circuit::CircuitBuilder<RecursionChallenge>,
    left_apt: &[Vec<p3_recursion::Target>],
    right_apt: &[Vec<p3_recursion::Target>],
    left_idx: usize,
    right_idx: usize,
    left_vk_cap: &[p3_recursion::Target],
    right_vk_cap: &[p3_recursion::Target],
) {
    let l = left_apt
        .get(left_idx)
        .expect("left segment instance present");
    let r = right_apt
        .get(right_idx)
        .expect("right segment instance present");
    debug_assert!(l.len() >= SEG_SPINE_WIDTH && r.len() >= SEG_SPINE_WIDTH);
    let vk_spine = combine_vk_spine(cb, l, r, left_vk_cap, right_vk_cap, SEG_VK_SPINE_FIRST);

    // (1) STATE CONTINUITY: L.last_new8 == R.first_old8, lane-by-lane over the 8-felt anchors
    //     (the temporal tooth, off the zero slot — `connect`, never `sub`+`assert_zero`).
    for k in 0..SEG_ANCHOR_WIDTH {
        cb.connect(l[SEG_LAST_NEW + k], r[SEG_FIRST_OLD + k]);
    }

    // (2) parent segment: span [L.first_old8 .. R.last_new8], count L+R, ordered multi-felt digest
    //     acc = commit(L.acc ++ R.acc).
    let count = cb.add(l[SEG_COUNT], r[SEG_COUNT]);
    let mut acc_inputs = Vec::with_capacity(2 * SEG_DIGEST_WIDTH);
    acc_inputs.extend_from_slice(&l[SEG_DIGEST_FIRST..SEG_DIGEST_FIRST + SEG_DIGEST_WIDTH]);
    acc_inputs.extend_from_slice(&r[SEG_DIGEST_FIRST..SEG_DIGEST_FIRST + SEG_DIGEST_WIDTH]);
    let acc = seg_poseidon_commit(cb, &acc_inputs);
    let mut parent = Vec::with_capacity(SEG_SPINE_WIDTH);
    parent.extend_from_slice(&l[SEG_FIRST_OLD..SEG_FIRST_OLD + SEG_ANCHOR_WIDTH]);
    parent.extend_from_slice(&r[SEG_LAST_NEW..SEG_LAST_NEW + SEG_ANCHOR_WIDTH]);
    parent.push(count);
    parent.extend_from_slice(&acc);
    // (3) THE VK SPINE — both children's circuit identities, folded into the parent's claim.
    parent.extend_from_slice(&vk_spine);
    debug_assert_eq!(parent.len(), SEG_SPINE_WIDTH);
    cb.expose_as_public_output(&parent);
}

/// **THE BOARD-WINDOW MERGE** — [`segment_combine_expose`] plus the ONE cross-leaf rule of the
/// two-leg fold: `left.OUT == right.IN`, lane by lane.
///
/// `window == 0` is BYTE-IDENTICAL to [`segment_combine_expose`] (every non-automatafl chain, and
/// the tug/membership folds, are untouched — a hard requirement, since the ordered digest is
/// shape-sensitive: `ordered_digest_combine_is_not_associative`). With `window == W > 0`, each
/// child carries `[segment(SEG_WIDTH) ‖ IN(W) ‖ OUT(W)]`, and this:
///
/// ```text
///   (3) BOARD CONTINUITY:  L.OUT[k] == R.IN[k]           k in 0..W        ← the seam
///   (4) parent window:     [L.IN ‖ R.OUT]                                 ← carried to the root
/// ```
///
/// At the leaf-pair nodes (3) IS `hseamPack ∧ hseamAutoX ∧ hseamAutoY` — the exact hypotheses
/// `AutomataflTurnCapstone.turn_sat_imp_roundStep_pi` takes, so a folded round's Leg-A `new` board
/// IS `AutomataflRules.roundStep`'s outcome board for the moves Leg R adjudicated. One level up,
/// the SAME rule is the inter-round carry (`A_i.OUT == R_{i+1}.IN`) — so the rounds form ONE
/// trajectory, not K independent transitions. At the root, (4) is `[first.IN ‖ last.OUT]`: the
/// genesis and final positions, in the clear (the automatafl pack is injective, so the 9-felt
/// board half decodes to the actual board with no further circuit).
///
/// A disagreeing pair is a per-lane `connect` CONFLICT ⇒ the node is UNSAT ⇒ no root ⇒ the light
/// client never receives a verifying artifact.
/// **THE SEAM ITSELF** — `left.OUT[k] == right.IN[k]` for `k < window`, as `window` in-circuit
/// `connect`s, and NOTHING else. Split out of [`segment_combine_expose_with_board_window`] so the
/// one rule the whole two-leg design rests on can be exercised in a bare `CircuitBuilder` (no FRI,
/// no sponge, no aggregation) — a broken seam must be a `WitnessConflict`, which is what "the node
/// is UNSAT ⇒ no root ⇒ the light client never receives a verifying artifact" MEANS at the
/// mechanism level.
///
/// The window lanes sit past the segment in each child's exposed claim: `IN` at
/// `[SEG_WIDTH .. SEG_WIDTH+W)`, `OUT` at `[SEG_WIDTH+W .. SEG_WIDTH+2W)`.
///
/// `connect` in this builder is witness-slot ALIASING (a disjoint-set forest over expressions,
/// one shared slot per class), so a disagreeing pair is not a soft constraint that a clever prover
/// can satisfy some other way: the two lanes literally become one witness cell, and a witness that
/// wants two different values in it does not exist.
pub(crate) fn board_window_connects(
    cb: &mut p3_circuit::CircuitBuilder<RecursionChallenge>,
    l: &[p3_recursion::Target],
    r: &[p3_recursion::Target],
    window: usize,
) {
    for k in 0..window {
        cb.connect(l[SEG_SPINE_WIDTH + window + k], r[SEG_SPINE_WIDTH + k]);
    }
}

/// **THE CLEAN-HANDOFF SEAM** — the `C_last.OUT == R.IN` connect of the multi-round braid, the
/// analogue of [`board_window_connects`] for two legs whose windows have DIFFERENT widths.
///
/// The conflict chain runs on the FULL RoundState window
/// `[board ‖ marks ‖ locked ‖ waiting ‖ auto]` (`l_window` lanes; 32 at n = 11, P = 2) with
/// [`board_window_connects`] connecting all `l_window` lanes `C_k.OUT == C_{k+1}.IN`. When the last
/// conflict round hands off to a CLEAN round (Leg R), the clean segment CONSUMES `locked`/`waiting`
/// — those tables do not cross into it — so the handoff connects ONLY the leading `handoff` lanes,
/// `board ‖ marks` (18 at n = 11), of the conflict round's OUT window to the clean round's IN
/// window, and DROPS the rest.
///
/// `L.OUT`'s board+marks prefix is `l[SEG_WIDTH + l_window .. SEG_WIDTH + l_window + handoff)`;
/// `R.IN`'s is `r[SEG_WIDTH .. SEG_WIDTH + handoff)`. Both windows are authored `board`-first then
/// `marks` (the RoundState order, `AutomataflLegCEmit`), so the shared prefix IS `board ‖ marks` on
/// each side. `L.OUT`'s dropped `locked`/`waiting`/`auto` lanes are left free — a differing locked
/// lane does NOT break this handoff, by design (it is consumed at the clean round, not carried).
///
/// Same aliasing force as [`board_window_connects`]: each connected lane pair becomes ONE witness
/// cell, so a board-or-marks disagreement across the clean handoff is a `WitnessConflict` — a
/// witness that does not exist, not a soft constraint. `handoff` must be `<= min(l_window, R.IN
/// width)` and every connected lane must be `board ‖ marks` on both sides (the caller's contract;
/// the M7 braid supplies it from `roundstate_window_n11::HANDOFF_LANES`).
///
/// Wired by the M7 multi-round braid fold (which chooses the merge per adjacent-leg pair); today it
/// is exercised at the connect level by `board_window_seam_tests`.
#[allow(dead_code)]
pub(crate) fn board_window_clean_handoff_connects(
    cb: &mut p3_circuit::CircuitBuilder<RecursionChallenge>,
    l: &[p3_recursion::Target],
    r: &[p3_recursion::Target],
    l_window: usize,
    handoff: usize,
) {
    for k in 0..handoff {
        cb.connect(l[SEG_SPINE_WIDTH + l_window + k], r[SEG_SPINE_WIDTH + k]);
    }
}

pub(crate) fn segment_combine_expose_with_board_window(
    cb: &mut p3_circuit::CircuitBuilder<RecursionChallenge>,
    left_apt: &[Vec<p3_recursion::Target>],
    right_apt: &[Vec<p3_recursion::Target>],
    left_idx: usize,
    right_idx: usize,
    window: usize,
    left_vk_cap: &[p3_recursion::Target],
    right_vk_cap: &[p3_recursion::Target],
) {
    if window == 0 {
        segment_combine_expose(
            cb,
            left_apt,
            right_apt,
            left_idx,
            right_idx,
            left_vk_cap,
            right_vk_cap,
        );
        return;
    }
    let l = left_apt
        .get(left_idx)
        .expect("left segment instance present");
    let r = right_apt
        .get(right_idx)
        .expect("right segment instance present");
    debug_assert!(
        l.len() >= SEG_SPINE_WIDTH + 2 * window && r.len() >= SEG_SPINE_WIDTH + 2 * window
    );
    let vk_spine = combine_vk_spine(cb, l, r, left_vk_cap, right_vk_cap, SEG_VK_SPINE_FIRST);

    // (1) STATE CONTINUITY — the cell tooth, unchanged.
    for k in 0..SEG_ANCHOR_WIDTH {
        cb.connect(l[SEG_LAST_NEW + k], r[SEG_FIRST_OLD + k]);
    }
    // (3) BOARD CONTINUITY — the board tooth.
    board_window_connects(cb, l, r, window);

    // (2) parent segment — identical math to the plain combine.
    let count = cb.add(l[SEG_COUNT], r[SEG_COUNT]);
    let mut acc_inputs = Vec::with_capacity(2 * SEG_DIGEST_WIDTH);
    acc_inputs.extend_from_slice(&l[SEG_DIGEST_FIRST..SEG_DIGEST_FIRST + SEG_DIGEST_WIDTH]);
    acc_inputs.extend_from_slice(&r[SEG_DIGEST_FIRST..SEG_DIGEST_FIRST + SEG_DIGEST_WIDTH]);
    let acc = seg_poseidon_commit(cb, &acc_inputs);
    let mut parent = Vec::with_capacity(SEG_SPINE_WIDTH + 2 * window);
    parent.extend_from_slice(&l[SEG_FIRST_OLD..SEG_FIRST_OLD + SEG_ANCHOR_WIDTH]);
    parent.extend_from_slice(&r[SEG_LAST_NEW..SEG_LAST_NEW + SEG_ANCHOR_WIDTH]);
    parent.push(count);
    parent.extend_from_slice(&acc);
    parent.extend_from_slice(&vk_spine);
    // (4) parent window: the LEFT child's IN and the RIGHT child's OUT.
    parent.extend_from_slice(&l[SEG_SPINE_WIDTH..SEG_SPINE_WIDTH + window]);
    parent.extend_from_slice(&r[SEG_SPINE_WIDTH + window..SEG_SPINE_WIDTH + 2 * window]);
    debug_assert_eq!(parent.len(), SEG_SPINE_WIDTH + 2 * window);
    cb.expose_as_public_output(&parent);
}

/// **THE CLEAN-HANDOFF SEAM + PARENT MIXED-WINDOW CARRY** — the board-visible half of the mixed-width
/// merge node ([`segment_combine_expose_with_clean_handoff`]), factored out so it can be driven in a
/// bare `CircuitBuilder` (where a broken seam is a millisecond `WitnessConflict`) WITHOUT the
/// tens-of-minutes real aggregation the ordered-digest sponge needs.
///
/// It (a) connects the leading `handoff` `board ‖ marks` lanes of the LEFT child's OUT window
/// (`l_window` lanes) to the RIGHT child's IN window via [`board_window_clean_handoff_connects`],
/// dropping `locked ‖ waiting ‖ auto`, and (b) returns the parent MIXED window `[L.IN(l_window) ‖
/// R.OUT(r_window)]` — the whole turn's genesis RoundState and the clean round's final state. The
/// segment digest (count + `acc`) is the unchanged shared [`seg_poseidon_commit`], added by the
/// caller.
fn clean_handoff_seam_and_window(
    cb: &mut p3_circuit::CircuitBuilder<RecursionChallenge>,
    l: &[p3_recursion::Target],
    r: &[p3_recursion::Target],
    l_window: usize,
    r_window: usize,
    handoff: usize,
) -> Vec<p3_recursion::Target> {
    // (3) THE CLEAN HANDOFF — connect the `board ‖ marks` prefix, drop the rest.
    board_window_clean_handoff_connects(cb, l, r, l_window, handoff);
    // (4) THE PARENT MIXED WINDOW — L.IN(l_window) then R.OUT(r_window).
    let mut win = Vec::with_capacity(l_window + r_window);
    win.extend_from_slice(&l[SEG_SPINE_WIDTH..SEG_SPINE_WIDTH + l_window]); // L.IN
    win.extend_from_slice(&r[SEG_SPINE_WIDTH + r_window..SEG_SPINE_WIDTH + 2 * r_window]); // R.OUT
    win
}

/// **THE MIXED-WIDTH CLEAN-HANDOFF MERGE NODE** — the parent-segment producer for the single
/// `C_last → R` boundary of a multi-round automatafl turn, where the LEFT child (the folded conflict
/// braid) carries an `l_window`-lane RoundState window and the RIGHT child (the folded clean round)
/// carries a NARROWER `r_window`-lane `[board ‖ marks ‖ auto]` window.
///
/// This is the analogue of [`segment_combine_expose_with_board_window`] for two children whose
/// windows have DIFFERENT widths. It runs the SAME three teeth, mixed-width:
///
/// ```text
///   (1) STATE CONTINUITY: L.last_new8 == R.first_old8            ← the cell tooth (unchanged)
///   (3) CLEAN HANDOFF:    L.OUT[0..handoff] == R.IN[0..handoff]  ← board||marks only; drop the rest
///   (2) parent segment:   [L.first_old8 ‖ R.last_new8 ‖ L.count+R.count ‖ H(L.acc ++ R.acc)]
///   (4) parent window:    [L.IN(l_window) ‖ R.OUT(r_window)]     ← MIXED width, carried to the root
/// ```
///
/// The handoff connects ONLY `board ‖ marks` (`handoff` = 18 at n = 11); `L.OUT`'s `locked ‖ waiting
/// ‖ auto` are consumed at the clean round, not carried into Leg R, so a differing locked lane does
/// not break it (by design, [`board_window_clean_handoff_connects`]). A disagreeing `board`-or-`marks`
/// lane is a per-lane `connect` CONFLICT ⇒ the node is UNSAT ⇒ no root ⇒ the light client never
/// receives a verifying artifact — the C→R analogue of the mid seam.
///
/// The parent re-exposes `SEG_WIDTH + l_window + r_window` lanes — the MIXED window. This node is
/// TERMINAL (the root of a multi-round turn); nothing merges above it, so the mixed exposure is read
/// only by the verifier's segment tooth (exact equality against the carried claim), never re-fed to
/// [`exposed_board_window`] (which assumes a uniform `SEG_WIDTH + 2W` shape).
pub(crate) fn segment_combine_expose_with_clean_handoff(
    cb: &mut p3_circuit::CircuitBuilder<RecursionChallenge>,
    left_apt: &[Vec<p3_recursion::Target>],
    right_apt: &[Vec<p3_recursion::Target>],
    left_idx: usize,
    right_idx: usize,
    l_window: usize,
    r_window: usize,
    handoff: usize,
    left_vk_cap: &[p3_recursion::Target],
    right_vk_cap: &[p3_recursion::Target],
) {
    let l = left_apt
        .get(left_idx)
        .expect("left segment instance present");
    let r = right_apt
        .get(right_idx)
        .expect("right segment instance present");
    debug_assert!(
        l.len() >= SEG_SPINE_WIDTH + 2 * l_window && r.len() >= SEG_SPINE_WIDTH + 2 * r_window
    );
    debug_assert!(handoff > 0 && handoff <= l_window.min(r_window));
    let vk_spine = combine_vk_spine(cb, l, r, left_vk_cap, right_vk_cap, SEG_VK_SPINE_FIRST);

    // (1) STATE CONTINUITY — the cell tooth, unchanged.
    for k in 0..SEG_ANCHOR_WIDTH {
        cb.connect(l[SEG_LAST_NEW + k], r[SEG_FIRST_OLD + k]);
    }

    // (3) CLEAN HANDOFF (board||marks prefix) + (4) the parent MIXED window.
    let window = clean_handoff_seam_and_window(cb, l, r, l_window, r_window, handoff);

    // (2) parent segment — identical math to the plain / board-window combine.
    let count = cb.add(l[SEG_COUNT], r[SEG_COUNT]);
    let mut acc_inputs = Vec::with_capacity(2 * SEG_DIGEST_WIDTH);
    acc_inputs.extend_from_slice(&l[SEG_DIGEST_FIRST..SEG_DIGEST_FIRST + SEG_DIGEST_WIDTH]);
    acc_inputs.extend_from_slice(&r[SEG_DIGEST_FIRST..SEG_DIGEST_FIRST + SEG_DIGEST_WIDTH]);
    let acc = seg_poseidon_commit(cb, &acc_inputs);
    let mut parent = Vec::with_capacity(SEG_SPINE_WIDTH + l_window + r_window);
    parent.extend_from_slice(&l[SEG_FIRST_OLD..SEG_FIRST_OLD + SEG_ANCHOR_WIDTH]);
    parent.extend_from_slice(&r[SEG_LAST_NEW..SEG_LAST_NEW + SEG_ANCHOR_WIDTH]);
    parent.push(count);
    parent.extend_from_slice(&acc);
    parent.extend_from_slice(&vk_spine);
    parent.extend_from_slice(&window);
    debug_assert_eq!(parent.len(), SEG_SPINE_WIDTH + l_window + r_window);
    cb.expose_as_public_output(&parent);
}

/// The board-window width a segment-carrying proof's exposed claim declares: `0` for a plain
/// 25-lane segment, `W` for a `[segment ‖ IN(W) ‖ OUT(W)]` exposure.
///
/// Fail-closed: a lane count that is neither `SEG_WIDTH` nor `SEG_WIDTH + 2W` cannot be read as
/// either shape and is an `Err` — never truncated into a plain segment (which would silently drop
/// the seam) nor padded into a window.
pub(crate) fn exposed_board_window(
    proof: &p3_circuit_prover::BatchStarkProof<DreggRecursionConfig>,
) -> Result<usize, String> {
    let lanes = proof
        .non_primitives
        .iter()
        .find(|e| e.op_type.as_str() == "expose_claim")
        .map(|e| e.public_values.len())
        .ok_or_else(|| "aggregation child carries no exposed claim table".to_string())?;
    if lanes == SEG_SPINE_WIDTH {
        return Ok(0);
    }
    if lanes < SEG_SPINE_WIDTH || (lanes - SEG_SPINE_WIDTH) % 2 != 0 {
        return Err(format!(
            "aggregation child exposes {lanes} claim lane(s): neither a plain segment+spine \
             ({SEG_SPINE_WIDTH}) nor a board-window segment+spine ({SEG_SPINE_WIDTH} + 2W) — \
             refused fail-closed. A {SEG_WIDTH}-lane child is a PRE-SPINE artifact: it carries no \
             VK spine, so its subtree's circuit identity cannot be certified and it is refused \
             rather than folded without one"
        ));
    }
    Ok((lanes - SEG_SPINE_WIDTH) / 2)
}

/// Build a [`RecursionInput::BatchStark`] from a BARE [`BatchStarkProof`] (the host mirror of
/// [`RecursionOutput::into_recursion_input_pinned`], which is a method on the OWNED output). This is
/// what lets the merge primitive run on a proof that arrived WITHOUT its prover-only
/// `Rc<CircuitProverData>` — i.e. a proof that crossed a thread / GPU / machine boundary as the
/// `Send`, serde [`BatchStarkProof`] (exactly the verify-sufficient subset
/// [`WholeChainProofBytes`] ships). It threads the proof's genuine per-table public values
/// (lever (b)) and pins the child's preprocessed commitment in-circuit (lever (a)).
pub(crate) fn batch_to_pinned_input(
    proof: &p3_circuit_prover::BatchStarkProof<DreggRecursionConfig>,
    expected_commit: RecursionCommit,
) -> RecursionInput<'_, DreggRecursionConfig, BatchOnly> {
    let num_primitive = p3_circuit_prover::batch_stark_prover::NUM_PRIMITIVE_TABLES;
    // `Val<DreggRecursionConfig>` is the p3-native BabyBear (`P3BabyBear`), NOT the dregg-circuit
    // `BabyBear` alias — `non_primitives[].public_values` and the `table_public_inputs` field both
    // carry the native field.
    let mut tpi: Vec<Vec<P3BabyBear>> = vec![Vec::new(); num_primitive];
    for entry in &proof.non_primitives {
        tpi.push(entry.public_values.clone());
    }
    RecursionInput::BatchStark {
        proof,
        common_data: &proof.stark_common,
        table_public_inputs: tpi,
        expected_preprocessed_commit: Some(expected_commit),
    }
}

/// **THE FARMABLE MERGE PRIMITIVE — one scan-state merge node, over `Send` currency.**
///
/// Aggregate TWO segment-carrying child [`BatchStarkProof`]s into ONE parent
/// [`RecursionOutput`], combining their ordered segments in-circuit via
/// [`segment_combine_expose`] and pinning each child's VK identity in-band
/// ([`batch_to_pinned_input`]). This is the per-node body of [`aggregate_tree`] lifted into a PURE,
/// side-effect-free function whose inputs (`&BatchStarkProof`) and result-of-interest (the output's
/// `.0`) are `Send`/serde — so independent merge nodes are FARMABLE to a worker / GPU / machine pool
/// ([`crate::merge_pool`]). The result's prover-only `Rc<CircuitProverData>` (`.1`) is never read by
/// any downstream merge OR by verification (every reader takes `root.0`), so a pool worker may drop
/// it and ship back only the `BatchStarkProof`.
///
/// It reads each child's segment instance index ([`expose_claim_instance_index`]) and preprocessed
/// commitment (its VK core) directly from the bare proof, builds the pinned recursion inputs, and
/// proves the aggregation layer with the segment-combine hook. The math is IDENTICAL to the serial
/// tree node, so the parallel root equals the serial root.
pub(crate) fn merge_two_segment_proofs(
    left: &p3_circuit_prover::BatchStarkProof<DreggRecursionConfig>,
    right: &p3_circuit_prover::BatchStarkProof<DreggRecursionConfig>,
    config: &DreggRecursionConfig,
    _backend: &p3_recursion::FriRecursionBackendForExt<
        D,
        16,
        8,
        p3_recursion::ops::Poseidon2Config,
    >,
    _params: &ProveNextLayerParams,
) -> Result<RecursionOutput<DreggRecursionConfig>, TurnChainError> {
    let left_idx =
        expose_claim_instance_index(left).ok_or_else(|| TurnChainError::RecursionFailed {
            reason: "left aggregation child carries no segment (expose_claim) table".to_string(),
        })?;
    let right_idx =
        expose_claim_instance_index(right).ok_or_else(|| TurnChainError::RecursionFailed {
            reason: "right aggregation child carries no segment (expose_claim) table".to_string(),
        })?;

    // LEVER (a) — extract each child's preprocessed commitment (its VK-identity core) and pin it
    // in-band; a from-scratch prover folding a proof of a DIFFERENT circuit is refused fail-closed.
    let left_commit = left
        .stark_common
        .preprocessed
        .as_ref()
        .map(|gp| gp.commitment.clone())
        .ok_or_else(|| TurnChainError::RecursionFailed {
            reason: "left aggregation child carries no preprocessed commitment to pin \
                     (its circuit identity cannot be bound in-band) — refused fail-closed"
                .to_string(),
        })?;
    let right_commit = right
        .stark_common
        .preprocessed
        .as_ref()
        .map(|gp| gp.commitment.clone())
        .ok_or_else(|| TurnChainError::RecursionFailed {
            reason: "right aggregation child carries no preprocessed commitment to pin \
                     (its circuit identity cannot be bound in-band) — refused fail-closed"
                .to_string(),
        })?;

    // THE COMBINE MODE, derived from the children's own exposed shapes (never a caller flag a
    // forging prover could clear): both plain ⇒ byte-identical to the deployed merge; both
    // `[segment ‖ IN(W) ‖ OUT(W)]` ⇒ the board-window merge, which ALSO connects
    // `left.OUT == right.IN`. A MIXED pair is refused fail-closed — silently degrading to the
    // plain combine would drop the seam exactly where a forger wants it dropped.
    let left_window =
        exposed_board_window(left).map_err(|reason| TurnChainError::RecursionFailed {
            reason: format!("left {reason}"),
        })?;
    let right_window =
        exposed_board_window(right).map_err(|reason| TurnChainError::RecursionFailed {
            reason: format!("right {reason}"),
        })?;
    if left_window != right_window {
        return Err(TurnChainError::RecursionFailed {
            reason: format!(
                "aggregation children declare different board-window widths ({left_window} vs \
                 {right_window}) — a chain cannot mix board-window and plain segment turns; \
                 refused fail-closed rather than folded without the seam"
            ),
        });
    }
    let window = left_window;

    let left_input = batch_to_pinned_input(left, left_commit);
    let right_input = batch_to_pinned_input(right, right_commit);

    let expose = move |cb: &mut p3_circuit::CircuitBuilder<RecursionChallenge>,
                       left_apt: &[Vec<p3_recursion::Target>],
                       right_apt: &[Vec<p3_recursion::Target>],
                       left_vk_cap: &[p3_recursion::Target],
                       right_vk_cap: &[p3_recursion::Target]| {
        segment_combine_expose_with_board_window(
            cb,
            left_apt,
            right_apt,
            left_idx,
            right_idx,
            window,
            left_vk_cap,
            right_vk_cap,
        );
    };

    prove_recursion_aggregation_auto_with_expose(&left_input, &right_input, config, Some(&expose))
        .map_err(|e| TurnChainError::RecursionFailed {
            reason: format!("aggregation layer failed: {e}"),
        })
}

/// **THE MIXED-WIDTH CLEAN-HANDOFF MERGE PRIMITIVE — the `C_last → R` fold node.**
///
/// The sibling of [`merge_two_segment_proofs`] for the ONE boundary the deployed same-width merge
/// refuses: the LEFT child (the folded conflict braid) exposes a UNIFORM `l_window`-lane RoundState
/// window (`SEG_WIDTH + 2·l_window` lanes), the RIGHT child (the folded clean round) exposes a
/// UNIFORM but NARROWER `r_window`-lane window (`SEG_WIDTH + 2·r_window` lanes), and this node stitches
/// them via [`segment_combine_expose_with_clean_handoff`] — connecting the shared `board ‖ marks`
/// prefix (`handoff` lanes) and re-exposing the parent MIXED window `[L.IN(l_window) ‖ R.OUT(r_window)]`.
///
/// FAIL-CLOSED ON SHAPE (item (3) of the braid): each child's window is read from its OWN exposed
/// shape (never a caller flag a forger could clear); both must be windowed; `handoff` must be nonzero
/// and fit inside both windows. A same-width pair is NOT this node's job — it is refused here and
/// belongs to [`merge_two_segment_proofs`]; a mixed pair is refused THERE and belongs here. The two
/// merge primitives partition cleanly, so a forger cannot present a mixed pair to the same-width node
/// (dropping the seam) nor a same-width pair to the weaker prefix-only handoff.
///
/// The caller (the multi-round-turn driver) supplies `handoff = roundstate_window_n11::HANDOFF_LANES`
/// (18 = `board(9) ‖ marks(9)`) — the semantic contract that the connected lanes ARE board+marks on
/// both sides (both windows are authored `board`-first then `marks`).
///
/// This node is TERMINAL — the root of a multi-round turn. Its mixed exposure is read only by the
/// verifier's segment tooth, never re-fed to [`exposed_board_window`].
pub(crate) fn merge_clean_handoff_segment_proofs(
    left: &p3_circuit_prover::BatchStarkProof<DreggRecursionConfig>,
    right: &p3_circuit_prover::BatchStarkProof<DreggRecursionConfig>,
    handoff: usize,
    config: &DreggRecursionConfig,
    _backend: &p3_recursion::FriRecursionBackendForExt<
        D,
        16,
        8,
        p3_recursion::ops::Poseidon2Config,
    >,
    _params: &ProveNextLayerParams,
) -> Result<RecursionOutput<DreggRecursionConfig>, TurnChainError> {
    let left_idx =
        expose_claim_instance_index(left).ok_or_else(|| TurnChainError::RecursionFailed {
            reason: "left clean-handoff child carries no segment (expose_claim) table".to_string(),
        })?;
    let right_idx =
        expose_claim_instance_index(right).ok_or_else(|| TurnChainError::RecursionFailed {
            reason: "right clean-handoff child carries no segment (expose_claim) table".to_string(),
        })?;

    // LEVER (a) — pin each child's preprocessed commitment (its VK-identity core) in-band.
    let left_commit = left
        .stark_common
        .preprocessed
        .as_ref()
        .map(|gp| gp.commitment.clone())
        .ok_or_else(|| TurnChainError::RecursionFailed {
            reason: "left clean-handoff child carries no preprocessed commitment to pin — refused \
                     fail-closed"
                .to_string(),
        })?;
    let right_commit = right
        .stark_common
        .preprocessed
        .as_ref()
        .map(|gp| gp.commitment.clone())
        .ok_or_else(|| TurnChainError::RecursionFailed {
            reason:
                "right clean-handoff child carries no preprocessed commitment to pin — refused \
                     fail-closed"
                    .to_string(),
        })?;

    // THE MIXED SHAPE, derived from the children's OWN exposed windows (never a caller flag).
    let l_window =
        exposed_board_window(left).map_err(|reason| TurnChainError::RecursionFailed {
            reason: format!("left {reason}"),
        })?;
    let r_window =
        exposed_board_window(right).map_err(|reason| TurnChainError::RecursionFailed {
            reason: format!("right {reason}"),
        })?;
    if l_window == 0 || r_window == 0 {
        return Err(TurnChainError::RecursionFailed {
            reason: format!(
                "clean-handoff merge requires BOTH children to carry a state window (left {l_window}, \
                 right {r_window}); a plain-segment child has no board||marks to hand off — refused \
                 fail-closed"
            ),
        });
    }
    if l_window == r_window {
        return Err(TurnChainError::RecursionFailed {
            reason: format!(
                "clean-handoff merge is for a MIXED-width C->R boundary; both children expose a \
                 {l_window}-lane window — a same-width pair folds through merge_two_segment_proofs \
                 (the whole-window seam), never the weaker board||marks-prefix handoff; refused \
                 fail-closed"
            ),
        });
    }
    if handoff == 0 || handoff > l_window.min(r_window) {
        return Err(TurnChainError::RecursionFailed {
            reason: format!(
                "clean-handoff prefix {handoff} does not fit both windows (left {l_window}, right \
                 {r_window}); the handoff must be exactly the board||marks lanes — refused fail-closed"
            ),
        });
    }

    let left_input = batch_to_pinned_input(left, left_commit);
    let right_input = batch_to_pinned_input(right, right_commit);

    let expose = move |cb: &mut p3_circuit::CircuitBuilder<RecursionChallenge>,
                       left_apt: &[Vec<p3_recursion::Target>],
                       right_apt: &[Vec<p3_recursion::Target>],
                       left_vk_cap: &[p3_recursion::Target],
                       right_vk_cap: &[p3_recursion::Target]| {
        segment_combine_expose_with_clean_handoff(
            cb,
            left_apt,
            right_apt,
            left_idx,
            right_idx,
            l_window,
            r_window,
            handoff,
            left_vk_cap,
            right_vk_cap,
        );
    };

    prove_recursion_aggregation_auto_with_expose(&left_input, &right_input, config, Some(&expose))
        .map_err(|e| TurnChainError::RecursionFailed {
            reason: format!("clean-handoff aggregation layer failed: {e}"),
        })
}

/// **THE MIXED-WIDTH FOLD DRIVER — stitch the conflict braid to the clean round in ONE root.**
///
/// A multi-round automatafl turn folds in a SHAPED tree, not a flat balanced one:
///
/// ```text
///   [ aggregate_tree(conflict leaves) ]  --clean-handoff-merge--  [ aggregate_tree(clean leaves) ]
///              ↑ uniform l_window                                        ↑ uniform r_window
///                                    ↘   ROOT: mixed [C_first.IN(l) ‖ R_last.OUT(r)]   ↙
/// ```
///
/// The conflict leaves (each a Leg C `[segment ‖ IN(l_window) ‖ OUT(l_window)]`) fold through the
/// deployed width-generic [`aggregate_tree`] — the uniform whole-`l_window` seam — to a conflict
/// sub-root; the clean leaves fold likewise to a clean sub-root at `r_window`; and the ONE
/// [`merge_clean_handoff_segment_proofs`] node connects their shared `board ‖ marks` prefix
/// (`handoff` lanes), drops `locked ‖ waiting ‖ auto`, and re-exposes the mixed root window. This is
/// the composition the M7 finding named as absent — the clean handoff is no longer a bare connect
/// primitive but the top node of a real fold DAG.
///
/// The two sub-folds are UNIFORM (the deployed merge), so only the single top node is new. The root
/// is TERMINAL (its mixed exposure is read by the verifier's segment tooth, never re-merged).
///
/// The caller supplies the handoff (18 = `board ‖ marks` at n = 11). This returns the mixed ROOT;
/// [`prove_clean_handoff_chain_recursive`] wraps it into a verifying [`WholeChainProof`] — it folds
/// the whole-turn segment host mirror in THIS shape (`combine_seg(fold(conflict), fold(clean))`, not
/// the flat [`compute_root_segment`]), carries the mixed board window from
/// [`clean_handoff_chain_claim`] / [`board_window_of_chain_with_clean_handoff`], and attaches the
/// Lean-emitted binding proof. The one REMAINING residual is the resolve-marks 20-lane clean leaf
/// that mints a UNIFORM clean sub-chain (a marks-carrying step descriptor, Lean-authored, being
/// emitted separately) — until it lands the clean sub-chain is mixed-width (Leg RM 20 ∘ Leg A 11) and
/// the assembler's host board-window mirror refuses it fail-closed.
pub fn fold_clean_handoff_root(
    conflict_leaves: Vec<RecursionOutput<DreggRecursionConfig>>,
    clean_leaves: Vec<RecursionOutput<DreggRecursionConfig>>,
    handoff: usize,
    config: &DreggRecursionConfig,
    backend: &p3_recursion::FriRecursionBackendForExt<D, 16, 8, p3_recursion::ops::Poseidon2Config>,
    params: &ProveNextLayerParams,
) -> Result<RecursionOutput<DreggRecursionConfig>, TurnChainError> {
    if conflict_leaves.is_empty() {
        return Err(TurnChainError::RecursionFailed {
            reason: "clean-handoff fold: the conflict braid has no leaves".to_string(),
        });
    }
    if clean_leaves.is_empty() {
        return Err(TurnChainError::RecursionFailed {
            reason: "clean-handoff fold: the clean round has no leaves".to_string(),
        });
    }
    // Each sub-chain folds UNIFORMLY through the deployed width-generic merge (whole-window seam).
    let conflict_root = aggregate_tree(conflict_leaves, config, backend, params)?;
    let clean_root = aggregate_tree(clean_leaves, config, backend, params)?;
    // The ONE new node: the mixed-width clean handoff, deriving each side's width from its own
    // exposed shape and connecting only the board||marks prefix.
    merge_clean_handoff_segment_proofs(
        &conflict_root.0,
        &clean_root.0,
        handoff,
        config,
        backend,
        params,
    )
}

/// **THE HOST-SIDE CLAIM a clean-handoff root will EXPOSE** — the four segment fields plus the
/// mixed board window a [`WholeChainProof`] built by [`prove_clean_handoff_chain_recursive`] carries.
///
/// Computed WITHOUT the recursion fold (no proving): the segment is the shaped fold
/// `combine(fold(conflict), fold(clean))`, and the board window is the mixed
/// `[C_first.IN(l_window) ‖ R_last.OUT(r_window)]` — exactly what the verifier's segment + board-window
/// teeth ([`verify_turn_chain_recursive_from_parts_with_board_window`] (4)+(5)) compare the root's
/// exposure against. Separated from the fold so a fast structural test can assert the assembler's
/// carried claim without the tens-of-minutes real fold.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CleanHandoffChainClaim {
    /// The chain's 8-felt genesis anchor — the FIRST conflict turn's `first_old8`.
    pub genesis_root: [BabyBear; SEG_ANCHOR_WIDTH],
    /// The chain's 8-felt final anchor — the LAST clean turn's `last_new8`.
    pub final_root: [BabyBear; SEG_ANCHOR_WIDTH],
    /// The 8-felt ordered-history digest `H(conflict.acc ++ clean.acc)` — the shaped-tree fold.
    pub chain_digest: [BabyBear; SEG_DIGEST_WIDTH],
    /// The total folded turns — `conflict.len() + clean.len()`.
    pub num_turns: usize,
    /// The MIXED board window `[C_first.IN(l_window) ‖ R_last.OUT(r_window)]` — the genesis RoundState
    /// (32 lanes at n = 11) and the clean round's narrower final state.
    pub board_window: BoardWindow,
}

/// **THE MIXED BOARD WINDOW a clean-handoff root exposes, from the per-turn declared windows** — the
/// PURE host mirror the fast structural test drives with no leg minting and no proving.
///
/// `windows` are the chain's per-turn `(IN, OUT)` windows in order (the conflict braid's uniform
/// `l_window`-lane RoundState windows, then the clean sub-chain's uniform `r_window`-lane windows).
/// Folds them through the SAME [`fold_declared_windows`] core the assembler's host claim
/// ([`clean_handoff_chain_claim`]) uses, allowing the ONE `C_last → R` width change where only the
/// leading `handoff` `board ‖ marks` lanes are compared. Returns `[first.IN ‖ last.OUT]`.
///
/// This is what makes the assembler's window logic testable in milliseconds: fill the conflict Leg C
/// traces + the clean Leg RM trace directly (no door mint), extract their declared windows, and assert
/// the mixed `[32 ‖ r_window]` result — the exact seam the in-circuit
/// [`segment_combine_expose_with_clean_handoff`] connects, surfaced without the real fold.
pub fn clean_handoff_root_board_window(
    windows: &[(Vec<BabyBear>, Vec<BabyBear>)],
    handoff: usize,
) -> Result<BoardWindow, TurnChainError> {
    if windows.len() < 2 {
        return Err(TurnChainError::RecursionFailed {
            reason: format!(
                "clean-handoff window fold needs at least 2 turns (a conflict round and a clean \
                 round); got {}",
                windows.len()
            ),
        });
    }
    fold_declared_windows(windows, Some(handoff))
        .map_err(|reason| TurnChainError::RecursionFailed { reason })
}

/// **THE HOST CLAIM a clean-handoff `WholeChainProof` will carry** — the segment (genesis / final /
/// digest / count) and the mixed board window, computed from the conflict + clean turns WITHOUT
/// proving.
///
/// The shaped tree is `[fold(conflict)] --clean-handoff-- [fold(clean)]`, so its exposed segment is
/// `combine_seg(compute_root_segment(conflict), compute_root_segment(clean))` — the SAME segment math
/// the top [`segment_combine_expose_with_clean_handoff`] node runs (count additivity, ordered-digest
/// fold, span `[C.first_old8 ‖ R.last_new8]`). The board window is the mixed
/// `[C_first.IN ‖ R_last.OUT]` from [`compute_root_board_window_inner`], which allows the ONE C→R
/// width change.
///
/// Fail-closed BEFORE any proving on: a broken whole-chain door continuity (the `C_last → R` segment
/// seam the top node's tooth (1) enforces in-circuit), a chain whose clean sub-chain is NOT uniform
/// width (more than one board-window width change ⇒ the clean sub-chain is not yet the uniform
/// `r_window` interface — the blocked-on-step-marks residual), or a board-or-marks prefix mismatch at
/// the handoff.
pub fn clean_handoff_chain_claim(
    conflict_turns: &[&FinalizedTurn],
    clean_turns: &[&FinalizedTurn],
    handoff: usize,
) -> Result<CleanHandoffChainClaim, TurnChainError> {
    if conflict_turns.is_empty() {
        return Err(TurnChainError::RecursionFailed {
            reason: "clean-handoff claim: the conflict braid has no turns".to_string(),
        });
    }
    if clean_turns.is_empty() {
        return Err(TurnChainError::RecursionFailed {
            reason: "clean-handoff claim: the clean round has no turns".to_string(),
        });
    }
    // The whole chain in order — continuity, the segment, and the board window all span it.
    let all: Vec<&FinalizedTurn> = conflict_turns
        .iter()
        .copied()
        .chain(clean_turns.iter().copied())
        .collect();

    // The whole-chain door continuity (`prev.new_root8 == next.old_root8`), INCLUDING the C_last → R
    // boundary the top clean-handoff node's tooth (1) enforces in-circuit. Fail-closed here so a
    // broken seam costs milliseconds, not the real fold.
    generate_chain_trace_rotated_continuity(&all)?;

    // The shaped root segment: fold each sub-chain uniformly, then combine (the SAME math the top
    // node runs — count additivity + ordered-digest fold over the two sub-roots' segments).
    let conflict_seg = compute_root_segment(conflict_turns);
    let clean_seg = compute_root_segment(clean_turns);
    let root_seg = combine_seg(conflict_seg, clean_seg);

    // The mixed board window `[C_first.IN ‖ R_last.OUT]` (fail-closed on >1 width change / broken
    // handoff prefix). `None` would mean no turn declares a window — a multi-round automatafl turn
    // always does, so a `None` here is a malformed chain.
    let board_window = compute_root_board_window_inner(&all, Some(handoff))?.ok_or_else(|| {
        TurnChainError::RecursionFailed {
            reason:
                "clean-handoff claim: no turn declares a board window (a multi-round automatafl \
                     turn must carry the RoundState / board||marks windows)"
                    .to_string(),
        }
    })?;

    Ok(CleanHandoffChainClaim {
        genesis_root: root_seg.first_old8,
        final_root: root_seg.last_new8,
        chain_digest: root_seg.acc,
        num_turns: all.len(),
        board_window,
    })
}

/// **THE CLEAN-HANDOFF WHOLE-CHAIN ASSEMBLER — the sibling of [`prove_turn_chain_recursive`] for a
/// MULTI-ROUND automatafl turn.** Fold a conflict braid (uniform `l_window` RoundState Leg C leaves)
/// and its terminating clean round (uniform `r_window` `[board ‖ marks ‖ …]` leaves) into ONE
/// verifiable [`WholeChainProof`] whose ROOT is the mixed-width clean-handoff node.
///
/// This is the prover-side glue the M7 finding named as absent (`MultiRoundTurn` type doc, residual
/// (2)): [`fold_clean_handoff_root`] yields only a bare `RecursionOutput`, and the light client
/// already accepts a mixed-width board window
/// ([`verify_turn_chain_recursive_from_parts_with_board_window`] tooth (5)) — this assembles the
/// root + the shaped-tree host claim + the binding descriptor proof into the whole artifact, exactly
/// as [`prove_chain_core_rotated_with_fold`] does for the uniform fold, but with the shaped tree and
/// the mixed window.
///
/// The tail MIRRORS `prove_chain_core_rotated_with_fold` (host admission, the retained
/// Lean-emitted binding proof over the whole chain, the `WholeChainProof` assembly), differing only
/// in the TREE SHAPE: the two sub-chains fold UNIFORMLY through the deployed width-generic
/// [`aggregate_tree`], and the ONE new [`merge_clean_handoff_segment_proofs`] top node stitches their
/// shared `board ‖ marks` prefix (`handoff` = 18 at n = 11). Every host claim is computed fail-closed
/// by [`clean_handoff_chain_claim`] BEFORE a single leaf is proven.
///
/// The clean leaves MUST already be doored at the GLOBAL nonce offset (continuing the conflict
/// braid's nonce run) so the `C_last → R` segment continuity holds — [`fold_clean_handoff_root`]'s
/// top node connects `conflict_root.last_new8 == clean_root.first_old8`, the fixture legs' linear
/// chain. The caller ([`dregg_multiway_tug::fold::fold_clean_handoff_match`]) mints them so.
///
/// SLOW (the deployed recursive fold). BLOCKED at the host board-window mirror TODAY when the clean
/// sub-chain is MIXED-width (Leg RM 20-lane ∘ Leg A 11-lane) — [`compute_root_board_window_inner`]
/// refuses the second width change — until the marks-carrying step descriptor lands and the clean
/// sub-chain is uniform `r_window` = 20. That refusal is the honest blocked-on-step-marks signal,
/// not a fake green.
pub fn prove_clean_handoff_chain_recursive(
    conflict_turns: &[FinalizedTurn],
    clean_turns: &[FinalizedTurn],
    handoff: usize,
) -> Result<WholeChainProof, TurnChainError> {
    if conflict_turns.is_empty() {
        return Err(TurnChainError::RecursionFailed {
            reason: "clean-handoff fold: the conflict braid has no turns".to_string(),
        });
    }
    if clean_turns.is_empty() {
        return Err(TurnChainError::RecursionFailed {
            reason: "clean-handoff fold: the clean round has no turns".to_string(),
        });
    }

    // (1) HOST ADMISSION — descriptor-verify every turn, selector-bound (identical discipline to
    // `prove_turn_chain_recursive`; the rotated leaf re-proof is the soundness boundary).
    for (i, t) in conflict_turns.iter().enumerate() {
        verify_descriptor_participant(&t.participant)
            .map_err(|reason| TurnChainError::TurnProofInvalid { index: i, reason })?;
    }
    for (j, t) in clean_turns.iter().enumerate() {
        verify_descriptor_participant(&t.participant).map_err(|reason| {
            TurnChainError::TurnProofInvalid {
                index: conflict_turns.len() + j,
                reason,
            }
        })?;
    }

    // CODEX #5 count-lane bound (num_turns < p so the exposed count lane cannot wrap mod p).
    let num_turns = conflict_turns.len() + clean_turns.len();
    if (num_turns as u64) >= BABY_BEAR_MODULUS as u64 {
        return Err(TurnChainError::RecursionFailed {
            reason: format!(
                "num_turns {num_turns} >= BabyBear modulus {BABY_BEAR_MODULUS} (count lane would \
                 wrap mod p)"
            ),
        });
    }

    // (2) THE HOST CLAIM the mixed root will expose — the shaped-tree segment + the mixed board
    // window, all fail-closed BEFORE any proving (a broken C→R seam, a non-uniform clean sub-chain,
    // or a broken handoff prefix is caught here in milliseconds).
    let conflict_refs: Vec<&FinalizedTurn> = conflict_turns.iter().collect();
    let clean_refs: Vec<&FinalizedTurn> = clean_turns.iter().collect();
    let claim = clean_handoff_chain_claim(&conflict_refs, &clean_refs, handoff)?;

    // The ONE FRI engine the whole rotated tree runs at (inner proof + leaf-wrap + aggregation).
    let config = ir2_leaf_wrap_config();
    // ⚑ THE FOLD ENGINE, DERIVED. A leaf wrap now emits at `recursion_layer_over(config)`'s mint
    // knobs, so every node above it verifies at those — one more application of the same rule,
    // which is its fixed point. See [`turn_chain_root_config`].
    let fold_config = recursion_layer_over(&recursion_layer_over(&config));
    let backend = create_recursion_backend();
    let params = ProveNextLayerParams::default();

    // (3) THE RETAINED binding proof over the WHOLE chain — carried for the byte envelope / struct
    // API (and its scalar genesis/final/count tooth), NOT a soundness dependency (the segment tooth
    // over the root's exposure is what binds the claim). Identical role to the uniform fold.
    let all: Vec<&FinalizedTurn> = conflict_refs
        .iter()
        .copied()
        .chain(clean_refs.iter().copied())
        .collect();
    let binding_proof = prove_chain_binding_descriptor_rotated(&all)?;

    // (4) MINT each sub-chain's leaves at its GLOBAL chain position (so the state-binding node's door
    // matches the leg the fold mints), then fold the SHAPED tree: each sub-chain UNIFORMLY through
    // the deployed width-generic `aggregate_tree`, then the ONE mixed-width clean-handoff top node.
    let mut conflict_leaves: Vec<RecursionOutput<DreggRecursionConfig>> =
        Vec::with_capacity(conflict_turns.len());
    for (i, t) in conflict_turns.iter().enumerate() {
        conflict_leaves.push(mint_rotated_turn_leaf(i, t, &config)?);
    }
    let mut clean_leaves: Vec<RecursionOutput<DreggRecursionConfig>> =
        Vec::with_capacity(clean_turns.len());
    for (j, t) in clean_turns.iter().enumerate() {
        clean_leaves.push(mint_rotated_turn_leaf(
            conflict_turns.len() + j,
            t,
            &config,
        )?);
    }
    let root = fold_clean_handoff_root(
        conflict_leaves,
        clean_leaves,
        handoff,
        &fold_config,
        &backend,
        &params,
    )?;

    Ok(WholeChainProof {
        root,
        binding_proof,
        genesis_root: claim.genesis_root,
        final_root: claim.final_root,
        chain_digest: claim.chain_digest,
        num_turns: claim.num_turns,
        board_window: Some(claim.board_window),
    })
}

/// Fold a vector of batch-STARK proofs to ONE via 2-to-1 aggregation layers.
/// (Same binary-tree fold as [`joint_turn_recursive`](crate::joint_turn_recursive).)
///
/// Each internal node delegates to [`merge_two_segment_proofs`] — the SAME farmable primitive the
/// parallel scan-state driver ([`crate::merge_pool::aggregate_tree_scan_state`]) drains from its
/// merge-pool — so the serial root and the parallel root are byte-identical.
fn aggregate_tree(
    mut proofs: Vec<RecursionOutput<DreggRecursionConfig>>,
    config: &DreggRecursionConfig,
    backend: &p3_recursion::FriRecursionBackendForExt<D, 16, 8, p3_recursion::ops::Poseidon2Config>,
    params: &ProveNextLayerParams,
) -> Result<RecursionOutput<DreggRecursionConfig>, TurnChainError> {
    if proofs.is_empty() {
        return Err(TurnChainError::RecursionFailed {
            reason: "no leaves to aggregate".to_string(),
        });
    }
    while proofs.len() > 1 {
        let mut next_level: Vec<RecursionOutput<DreggRecursionConfig>> =
            Vec::with_capacity(proofs.len().div_ceil(2));
        let mut i = 0;
        while i + 1 < proofs.len() {
            // THE SEGMENT COMBINE (close of the mixed-root hole): delegate to the SAME farmable
            // per-node primitive the parallel scan-state driver drains — both children carry an
            // ordered segment `[first_old, last_new, count, acc]` in their `expose_claim` table;
            // [`merge_two_segment_proofs`] reads both, pins each child's VK identity in-band
            // (lever (a)+(b)), combines the segments soundly (continuity + count + ordered-digest),
            // and exposes the parent segment. There is no separate binding leaf — the whole-chain
            // claim is the fold of the REAL descriptor leaves' segments.
            let out =
                merge_two_segment_proofs(&proofs[i].0, &proofs[i + 1].0, config, backend, params)?;
            next_level.push(out);
            i += 2;
        }
        if i < proofs.len() {
            next_level.push(proofs.pop().unwrap());
        }
        proofs = next_level;
    }
    Ok(proofs.pop().unwrap())
}

/// The largest power of two `<= w`, floored at 2 — the EFFECTIVE streaming window. Powers of two
/// are REQUIRED for shape identity: a window sub-root must cover exactly one balanced-tree
/// level-k node span `[j*2^k, min((j+1)*2^k, K))`, which only aligns when the window is `2^k`.
/// Rounding DOWN respects the caller's memory budget (never proves more leaves at once than
/// asked).
fn floor_pow2_window(w: usize) -> usize {
    let w = w.max(2);
    1usize << (usize::BITS - 1 - w.leading_zeros())
}

/// **THE BOUNDED-MEMORY STREAMING FOLD SCHEDULE** — generic over the folded value, so the PROOF
/// driver ([`aggregate_tree_streaming`]), the HOST segment mirror ([`fold_host_segs_streaming`]),
/// and the shape/residency tests all run the ONE schedule.
///
/// The schedule reproduces [`aggregate_tree`]'s balanced tree EXACTLY (same node set, same
/// pairing, same odd-tail promotion) while keeping only O(W + log2(K/W)) values live:
///
///   1. **Window**: materialize leaves `[start, start+W)` (the ONLY place leaves are resident —
///      at most W at once) and fold them to ONE sub-root via `fold_window`. A full window of
///      `W = 2^k` leaves is a PERFECT dyadic subtree = the balanced tree's level-k node; the
///      final partial window is the balanced tree's clipped tail node (its internal balanced
///      fold matches the global one because `start` is always a multiple of `2^k`).
///   2. **Carry (binary counter / Merkle-mountain-range)**: push the sub-root onto a stack of
///      `(weight, value)`; while the top has EQUAL weight, pop it and merge `(popped, incoming)`
///      — the popped subtree is the one immediately LEFT of the incoming. Weights double, so the
///      stack holds at most `log2(#windows) + 1` sub-roots (the binary decomposition of the
///      window count).
///   3. **Finalize (suffix fold, right-to-left)**: fold the stack from the TOP (rightmost)
///      down, each popped entry merged as the LEFT child. This reproduces the balanced loop's
///      odd-tail promotion (the leftover is promoted to the END of the next level, so trailing
///      partial subtrees combine rightmost-first).
///
/// Shape identity is witnessed EXHAUSTIVELY (every `n <= 300` x window set, against the free —
/// maximally shape-sensitive — combine) by `streaming_schedule_matches_balanced_tree_shape`;
/// it is LOAD-BEARING because the segment digest `acc = H(L.acc ++ R.acc)` is not associative
/// (`ordered_digest_combine_is_not_associative`): identical shape is the ONLY way a
/// streaming root exposes the identical chain digest.
fn streaming_fold_schedule<T, E>(
    num_leaves: usize,
    window: usize,
    mut leaf: impl FnMut(usize) -> Result<T, E>,
    mut fold_window: impl FnMut(Vec<T>) -> Result<T, E>,
    mut merge: impl FnMut(T, T) -> Result<T, E>,
) -> Result<T, E> {
    assert!(num_leaves >= 1, "streaming fold requires at least one leaf");
    let w = floor_pow2_window(window);
    let mut stack: Vec<(usize, T)> = Vec::new();
    let mut start = 0usize;
    while start < num_leaves {
        let end = (start + w).min(num_leaves);
        // (1) THE WINDOW: prove/materialize <= W leaves ...
        let mut buf = Vec::with_capacity(end - start);
        for i in start..end {
            buf.push(leaf(i)?);
        }
        // ... and fold them to ONE sub-root. `buf` is MOVED in and fully consumed — THIS is
        // where the window's leaf values are dropped; they never coexist with the next window.
        let sub = if buf.len() == 1 {
            buf.pop().expect("single-leaf window")
        } else {
            fold_window(buf)?
        };
        // (2) THE CARRY: merge equal-weight neighbors eagerly (popped = LEFT of incoming).
        let mut cur = sub;
        let mut weight = 1usize;
        while stack
            .last()
            .is_some_and(|(top_weight, _)| *top_weight == weight)
        {
            let (_, left) = stack.pop().expect("equal-weight top just observed");
            cur = merge(left, cur)?;
            weight *= 2;
        }
        stack.push((weight, cur));
        start = end;
    }
    // (3) THE SUFFIX FINALIZE: right-to-left; each popped entry is LEFT of the accumulator.
    let (_, mut acc) = stack.pop().expect("at least one window was folded");
    while let Some((_, left)) = stack.pop() {
        acc = merge(left, acc)?;
    }
    Ok(acc)
}

/// **THE BOUNDED-MEMORY STREAMING sibling of [`aggregate_tree`].** Interleaves leaf PROVING with
/// folding via [`streaming_fold_schedule`]: prove a window of `<= W` leaves (`mint_leaf`), fold
/// it to ONE sub-root with [`aggregate_tree`] itself, fold the sub-root into the binary-counter
/// carry stack via [`merge_two_segment_proofs`], and DROP the window before the next leaf is
/// proven.
///
/// Peak resident recursion proofs are `~1.5*W` (the window fold's per-level transient: a level
/// vector stays alive while its `next_level` is built) plus `log2(K/W) + 1` carry-stack
/// sub-roots plus one merge in flight — **independent of K**, versus O(K) for the resident
/// collect-then-fold path. `W = 2` degenerates to an (almost) pure sequential fold; a large `W`
/// approaches the resident tree.
///
/// Because the schedule reproduces the balanced tree's exact shape and every node runs the SAME
/// [`merge_two_segment_proofs`], the streaming root exposes the IDENTICAL segment
/// `[first_old, last_new, count, acc]` as [`aggregate_tree`]'s root (and is expected
/// byte-identical, deterministic proving being what `scan_state_root_equals_serial_root`
/// already witnesses across execution orders) — so it verifies against the same
/// [`RecursionVk`] anchor via the unchanged [`verify_turn_chain_recursive`].
fn aggregate_tree_streaming(
    num_leaves: usize,
    window: usize,
    mint_leaf: impl FnMut(usize) -> Result<RecursionOutput<DreggRecursionConfig>, TurnChainError>,
    config: &DreggRecursionConfig,
    backend: &p3_recursion::FriRecursionBackendForExt<D, 16, 8, p3_recursion::ops::Poseidon2Config>,
    params: &ProveNextLayerParams,
) -> Result<RecursionOutput<DreggRecursionConfig>, TurnChainError> {
    if num_leaves == 0 {
        return Err(TurnChainError::RecursionFailed {
            reason: "no leaves to aggregate".to_string(),
        });
    }
    streaming_fold_schedule(
        num_leaves,
        window,
        mint_leaf,
        |buf| aggregate_tree(buf, config, backend, params),
        |left, right| {
            // A carry/suffix merge consumes BOTH children (owned; dropped on return) and yields
            // the fresh parent — never more than one extra proof in flight.
            merge_two_segment_proofs(&left.0, &right.0, config, backend, params)
        },
    )
}

/// Verify the whole-chain artifact against a caller-held trust anchor.
/// Cost is independent of the number of folded turns. Three teeth, in order
/// (see the module docs for what each one guarantees, precisely):
///
///   1. **VK pin** — recompute the presented root's verifier-key fingerprint
///      and compare it to `expected_vk` (the anchor an honest setup
///      distributed). A root proof of a different circuit — the from-scratch
///      aggregation route — is refused here, BEFORE any cryptographic check
///      trusts the proof's self-described circuit data.
///   2. **The root** — the single root batch-STARK proof verifies.
///   3. **The segment tooth** — the root's exposed ORDERED SEGMENT
///      `[first_old, last_new, count, acc]` (derived by construction from the
///      real descriptor leaves and combined up the tree) must equal the carried
///      `[genesis_root, final_root, num_turns, chain_digest]`. This closes the
///      mixed-root hole: a root that executed history A cannot expose B's
///      endpoints, so a B-claim against an A-execution is refused. (The carried
///      binding proof is NO LONGER a soundness dependency.)
pub fn verify_turn_chain_recursive(
    proof: &WholeChainProof,
    expected_vk: &RecursionVk,
) -> Result<(), TurnChainError> {
    verify_turn_chain_recursive_from_parts_with_board_window(
        &proof.root.0,
        &proof.binding_proof,
        proof.genesis_root,
        proof.final_root,
        proof.chain_digest,
        proof.num_turns,
        proof.board_window.as_ref(),
        expected_vk,
    )
}

/// The verify core, taking the VERIFY-SUFFICIENT PARTS directly instead of a whole
/// [`WholeChainProof`] value.
///
/// This is the byte-path's verifier: a [`WholeChainProof`] cannot be reconstructed
/// from bytes because its `root.1` (`Rc<CircuitProverData>`) is prover-only and not
/// serde — but the verifier never reads `root.1`. The three teeth use only
/// `root.0` (the root [`BatchStarkProof`]), the chain-binding `Proof`, and the four
/// public scalars, which is exactly this signature. [`verify_turn_chain_recursive`]
/// is a thin wrapper that forwards a whole value's parts here, and
/// [`verify_whole_chain_proof_bytes`] decodes a [`WholeChainProofBytes`] envelope and
/// calls this — so the in-memory and over-wire paths share ONE verifier body.
///
/// The teeth, in order (identical to [`verify_turn_chain_recursive`]):
///   1. **VK pin** — recompute the root's verifier-key fingerprint and compare to
///      `expected_vk` (a foreign-circuit root is refused before any check trusts it).
///   2. **The root** — the single root batch-STARK proof verifies.
///   3. **The segment tooth** — the root's exposed ordered segment `[first_old,
///      last_new, count, acc]` (built from the real descriptor leaves, combined up
///      the tree) must equal the carried `[genesis_root, final_root, num_turns,
///      chain_digest]`. (The carried binding proof is NOT a soundness dependency.)
#[allow(clippy::too_many_arguments)]
pub fn verify_turn_chain_recursive_from_parts(
    root_proof: &p3_circuit_prover::BatchStarkProof<DreggRecursionConfig>,
    binding_proof: &TurnChainBindingProof,
    genesis_root: [BabyBear; SEG_ANCHOR_WIDTH],
    final_root: [BabyBear; SEG_ANCHOR_WIDTH],
    chain_digest: [BabyBear; SEG_DIGEST_WIDTH],
    num_turns: usize,
    expected_vk: &RecursionVk,
) -> Result<(), TurnChainError> {
    verify_turn_chain_recursive_from_parts_with_board_window(
        root_proof,
        binding_proof,
        genesis_root,
        final_root,
        chain_digest,
        num_turns,
        None,
        expected_vk,
    )
}

/// **THE BOARD-WINDOW VERIFIER** — [`verify_turn_chain_recursive_from_parts`] with the two-leg
/// fold's carried `[first.IN ‖ last.OUT]` claim.
///
/// The segment tooth compares the root's exposure for EXACT equality against the carried claim, so
/// the shape is fail-closed in BOTH directions by construction:
///
///   * a board-window root (55 lanes at W = 11) presented with `board_window: None` builds a
///     25-lane `expected` and is REFUSED — which is precisely why the deployed verifier could not
///     silently ship lanes nobody checks;
///   * a carried window against a plain 33-lane root is REFUSED too (the exposure is short).
///
/// When the window IS carried and matches, the light client has, in addition to the four chain
/// claims: the state the chain STARTED from and the state it REACHED, as bound lanes of the same
/// proof. For automatafl those are the packed genesis and final boards plus the automaton
/// coordinate — and since the pack is injective, they decode to the actual positions in the clear.
#[allow(clippy::too_many_arguments)]
pub fn verify_turn_chain_recursive_from_parts_with_board_window(
    root_proof: &p3_circuit_prover::BatchStarkProof<DreggRecursionConfig>,
    binding_proof: &TurnChainBindingProof,
    genesis_root: [BabyBear; SEG_ANCHOR_WIDTH],
    final_root: [BabyBear; SEG_ANCHOR_WIDTH],
    chain_digest: [BabyBear; SEG_DIGEST_WIDTH],
    num_turns: usize,
    board_window: Option<&BoardWindow>,
    expected_vk: &RecursionVk,
) -> Result<(), TurnChainError> {
    // (0) THE COUNT BOUND — the verify-side twin of the fold's `num_turns < p` refusal.
    //
    // Both comparison sites below embed the count as ONE BabyBear lane
    // (`BabyBear::new(num_turns as u32)`), and `BabyBear::new` reduces mod p while `as u32`
    // truncates mod 2^32. Without this branch every `n + kp` and `n + k*2^32` is the SAME lane as
    // `n`, so an inflated claim passes all four teeth unchanged — measured, on a real fold, at
    // `circuit-prove/tests/num_turns_alias_probe.rs`. The prover refused this at `:2593`, `:3021`,
    // `:3432` and `:5249`; the VERIFIER did not, which is the half that matters, because the
    // attacker is the party holding the artifact.
    //
    // This one branch covers `verify_turn_chain_recursive` (in-memory),
    // `verify_turn_chain_recursive_from_parts`, `verify_turn_chain_recursive_from_blobs` (the
    // `pg-dregg` seam, which takes the count as a bare `usize` and never passes a decode gate) and
    // `verify_whole_chain_proof_bytes`. The byte paths ALSO refuse at
    // `WholeChainProofBytes::from_postcard` — deliberately both, since the blob seam has no
    // envelope and the in-memory seam has no wire.
    if (num_turns as u64) >= BABY_BEAR_MODULUS as u64 {
        return Err(TurnChainError::ClaimedPublicsUnattested {
            reason: format!(
                "num_turns {num_turns} >= BabyBear modulus {BABY_BEAR_MODULUS}: the count lane \
                 would wrap mod p, making this claim indistinguishable from {} — refused",
                (num_turns as u64) % (BABY_BEAR_MODULUS as u64)
            ),
        });
    }

    // (1) VK pin.
    let found = whole_chain_anchor(root_proof)?;
    if found != *expected_vk {
        return Err(TurnChainError::VkFingerprintMismatch {
            expected: expected_vk.to_hex(),
            found: found.to_hex(),
        });
    }

    // (2) The Lean-emitted scalar turn-chain descriptor. The exact four PIs were serialized with
    // the proof because `verify_vm_descriptor2` takes them separately; the verifier neither
    // reconstructs a digest it cannot see nor trusts values extracted from the proof. The scalar
    // endpoints/count must agree with the corresponding carried wide claims. The fourth PI is this
    // descriptor's own sequential hash-chain digest; the batch proof binds it directly. The root's
    // distinct 8-felt ordered-segment digest is checked by tooth (4) below.
    let binding_pis = binding_proof.pis();
    let expected_scalar = [
        genesis_root[0],
        final_root[0],
        BabyBear::new(num_turns as u32),
    ];
    if binding_pis[..3] != expected_scalar {
        return Err(TurnChainError::ClaimedPublicsUnattested {
            reason: format!(
                "binding descriptor publics {:?} do not match carried scalar genesis/final/count {:?}",
                &binding_pis[..3],
                expected_scalar
            ),
        });
    }
    let binding_desc = descriptor_by_name(TURN_CHAIN_BINDING_NAME).ok_or_else(|| {
        TurnChainError::ClaimedPublicsUnattested {
            reason: format!(
                "Lean-emitted descriptor {TURN_CHAIN_BINDING_NAME:?} is not registered"
            ),
        }
    })?;
    verify_vm_descriptor2(&binding_desc, &binding_proof.proof, &binding_pis).map_err(|reason| {
        TurnChainError::ClaimedPublicsUnattested {
            reason: format!("Lean-emitted turn-chain descriptor proof failed: {reason}"),
        }
    })?;

    // (3) The root. ⚑ **THIS MOVED, AND IT IS THE ONE THING A CONSUMER MUST RE-PIN.** The root
    // batch proof is produced by `aggregate_tree`, and every node above a leaf now mints at
    // [`turn_chain_root_config`] — `create_recursion_config`'s `(log_blowup 3, 38 queries,
    // query_pow 14)`. It used to be `ir2_leaf_wrap_config`'s `(6, 19, 16)`, because a leaf wrap
    // inherited its CHILD's engine and handed that engine to the whole tower. Verifying under
    // the old one now fails `QueryProofCountMismatch { expected: 19, got: 38 }` — the honest
    // failure, in the direction opposite to the one this comment used to warn about. ⚠ The
    // recursion VK fingerprint rotates with it: a fold circuit that verifies a 38-query child at
    // a 2^23 domain is a DIFFERENT circuit from one that verifies a 19-query child at 2^26.
    verify_recursive_batch_proof_with_config(root_proof, &turn_chain_root_config())
        .map_err(|reason| TurnChainError::RecursionFailed { reason })?;

    // (4) THE SEGMENT TOOTH (the close of the IVC mixed-root hole). The root proof carries an
    // `expose_claim` non-primitive table whose `public_values` are the root's ORDERED SEGMENT
    // `[first_old, last_new, count, acc]`. That segment is built BY CONSTRUCTION from the real
    // descriptor leaves: each leaf's `first_old`/`last_new` are bound in-circuit to its
    // descriptor proof's verified rotated roots, and the combine at each aggregation node
    // enforces state continuity (`L.last_new == R.first_old`), count additivity, and the
    // ordered-digest fold (`acc = H(L.acc, R.acc)`) — re-exposed up to the root. So the
    // root-exposed segment is the WHOLE-CHAIN claim derived from the ACTUAL execution. The
    // carried claim must match it exactly. There is NO separate binding leaf to swap: a root
    // that executed history A cannot expose B's endpoints, so a B-claim against an A-execution
    // FAILS here (`genesis = A.first_old != B.genesis`, etc.).
    let exposed = root_exposed_claims(root_proof).ok_or_else(|| {
        TurnChainError::ClaimedPublicsUnattested {
            reason: "root proof carries no exposed segment table (segment channel absent)"
                .to_string(),
        }
    })?;
    // The exposure is `[segment(SEG_WIDTH) ‖ vk_spine(VK_SPINE_WIDTH) ‖ IN(W) ‖ OUT(W)]`. The
    // spine lanes are NOT compared here — they are compared by tooth (1), inside
    // `whole_chain_anchor`, against the caller-held anchor. Splicing them out keeps this ONE
    // exact-equality over the values the CALLER actually carries, so a shape mismatch still falls
    // out of it fail-closed instead of needing its own branch.
    if exposed.len() < SEG_SPINE_WIDTH {
        return Err(TurnChainError::ClaimedPublicsUnattested {
            reason: format!(
                "root exposes {} claim lane(s), fewer than the {SEG_SPINE_WIDTH} a segment + VK \
                 spine needs — pre-spine artifact, refused",
                exposed.len()
            ),
        });
    }
    let exposed: Vec<BabyBear> = exposed[..SEG_WIDTH]
        .iter()
        .copied()
        .chain(exposed[SEG_SPINE_WIDTH..].iter().copied())
        .collect();
    let mut expected = Vec::with_capacity(SEG_WIDTH);
    expected.extend_from_slice(&genesis_root);
    expected.extend_from_slice(&final_root);
    expected.push(BabyBear::new(num_turns as u32));
    expected.extend_from_slice(&chain_digest);
    // (5) THE BOARD-WINDOW TOOTH. Appended to the SAME exact-equality comparison, so both
    // shape mismatches (55-lane root / no carried window, and carried window / 33-lane root)
    // fall out of it fail-closed rather than needing their own conditional.
    if let Some(w) = board_window {
        // A UNIFORM two-leg / conflict root carries equal-width halves; a MIXED clean-handoff root
        // (a multi-round automatafl turn) legitimately carries `first.IN` (the 32-lane genesis
        // RoundState) WIDER than `last.OUT` (the clean round's narrower final state). So the halves
        // may differ in width — what is refused is an EMPTY half (a window that cannot express any
        // endpoint). The real gate is the exact-equality check below: `first.IN ‖ last.OUT` is
        // appended to `expected` and compared to the root's genuine exposure, so a carried window
        // that is not the fold of the real leaves (wrong width, wrong lanes, dropped lanes) fails
        // there regardless of the halves' relative widths.
        if w.first_in.is_empty() || w.last_out.is_empty() {
            return Err(TurnChainError::ClaimedPublicsUnattested {
                reason: format!(
                    "carried board window is malformed ({} IN lanes, {} OUT lanes) — an empty \
                     window half cannot be the fold of a two-leg / clean-handoff seam",
                    w.first_in.len(),
                    w.last_out.len()
                ),
            });
        }
        expected.extend_from_slice(&w.first_in);
        expected.extend_from_slice(&w.last_out);
    }
    if exposed != expected {
        return Err(TurnChainError::ClaimedPublicsUnattested {
            reason: format!(
                "root-exposed segment {exposed:?} != carried claim {expected:?} \
                 (the carried claim is not the fold of the real descriptor leaves)"
            ),
        });
    }

    Ok(())
}

// ============================================================================
// The 2-step inductive core of the UNBOUNDED accumulator.
// ============================================================================

/// The inductive core of a continuous (unbounded) accumulator:
/// `fold_two_turns(running, next) -> new_running`.
///
/// This proves the *binary* step that, iterated, gives the unbounded loop:
/// given a proof of "turns 1..N executed and the root advanced to `mid_root`"
/// and the next finalized turn `(mid_root -> new_root)`, produce a proof of
/// "turns 1..N+1 executed and the root advanced to `new_root`". The two leaves
/// (running summary + next turn) are wrapped and aggregated into one batch
/// proof — the same fold the K-fold tree applies at each internal node.
///
/// ## What this IS
///
/// A genuine 2-to-1 recursive fold over real in-circuit-verified leaves, with
/// the temporal binding (`prev.new_root == next.old_root`) enforced by the root's
/// ordered segment over the 2-turn window. Iterating it left-to-right over a
/// finalized stream reproduces [`prove_turn_chain_recursive`]'s result. The artifact also carries
/// a directly verified Lean-emitted binding descriptor proof.
///
/// ## What the UNBOUNDED driver still needs (named open)
///
/// To make the running proof itself *constant memory* across an unbounded
/// stream — i.e. fold `running_proof ∘ next_turn` where `running_proof` is the
/// PREVIOUS fold's output re-verified IN-CIRCUIT — the running batch proof must
/// be fed back as a [`BatchOnly`] recursion input to the next layer (the fork's
/// `into_recursion_input::<BatchOnly>` already supports this; it is what
/// [`aggregate_tree`] uses internally). The open work is the *driver*: a
/// persistent accumulator struct that (a) holds the single running
/// `RecursionOutput`, (b) on each `poll_finalized_blocks` tick builds the next
/// turn leaf + a 2-row Lean-emitted binding descriptor proof for
/// `running.final_root -> new_root`, and (c) re-aggregates `running ∘ turn` into the new
/// running output. The cryptographic machinery is all present and exercised
/// here; what remains is wiring it to the node's live finality stream and
/// persisting the running output across restarts.
pub fn fold_two_turns(
    running: &FinalizedTurn,
    next: &FinalizedTurn,
) -> Result<WholeChainProof, TurnChainError> {
    // The 2-turn window IS a turn chain of length 2 — reuse the proven path
    // (by reference: the descriptor proof artifact is move-only, so the window
    // borrows the turns instead of cloning them).
    let window: [&FinalizedTurn; 2] = [running, next];
    let mut selectors = Vec::with_capacity(2);
    for (i, t) in window.iter().enumerate() {
        let s = verify_descriptor_participant(&t.participant)
            .map_err(|reason| TurnChainError::TurnProofInvalid { index: i, reason })?;
        selectors.push(s);
    }
    prove_chain_core_rotated(&window, &selectors)
}

// ============================================================================
// Tests
// ============================================================================
//
// Bucket-F (PATH-PRESERVE Phase 5a): the in-lib `#[cfg(test)] mod tests` (the K-fold,
// broken-order, ungated-forged-post-commit, stub-leaf, foreign-circuit-VK-pin,
// in-circuit-wrap, and 2-step-inductive teeth) RELOCATED to the integration test
// `circuit/tests/ivc_turn_chain_rotated.rs`, which can mint the mandatory ROTATED
// participant through `dregg_turn_prover::rotation_witness::mint_rotated_participant_leg`
// (the circuit lib cannot — it has no `dregg-cell` / `dregg-turn` dependency, the cycle).
//
// The `streaming_fold_tests` below are DIFFERENT in kind: pure host math over the fold
// SCHEDULE and the host segment combine — no proving, no rotated participant minting — so
// they live in-lib (the Bucket-F relocation applied only to teeth that must mint legs).

#[cfg(test)]
mod streaming_fold_tests {
    use super::*;

    #[test]
    fn direct_ir2_vk_correlation_refuses_low4_and_every_wrong_leg_vk_limb() {
        // SAME direct descriptor/leaf identity in both cases.  The deployed
        // leg's low4 prefix is insufficient even when it agrees, and a future
        // full-width leg with one changed lane is also refused.
        let direct_vk8 = core::array::from_fn(|i| BabyBear::new(100 + i as u32));
        let low4 = &direct_vk8[..4];
        let err = require_direct_ir2_leg_vk8(low4, direct_vk8).unwrap_err();
        assert_eq!(err, DIRECT_IR2_VK8_REFUSAL);

        for lane in 0..DEPLOYED_CUSTOM_PROGRAM_VK_PI_LEN {
            let mut wrong_leg_vk8 = direct_vk8;
            wrong_leg_vk8[lane] += BabyBear::ONE;
            let err = require_direct_ir2_leg_vk8(&wrong_leg_vk8, direct_vk8).unwrap_err();
            assert!(err.contains("leg program VK8 differs"), "lane {lane}");
        }

        require_direct_ir2_leg_vk8(&direct_vk8, direct_vk8)
            .expect("the full-width exact identity is the only admitted boundary");
    }

    /// The FREE combine: a symbolic tree that records shape and nothing else — maximally
    /// shape-sensitive. If the streaming schedule builds the same symbolic tree as the balanced
    /// loop, then ANY per-node combine (including the non-associative ordered Poseidon digest)
    /// produces identical values on both schedules.
    #[derive(Clone, PartialEq, Eq, Debug)]
    enum ShapeTree {
        Leaf(usize),
        Br(Box<ShapeTree>, Box<ShapeTree>),
    }

    fn br(l: ShapeTree, r: ShapeTree) -> ShapeTree {
        ShapeTree::Br(Box::new(l), Box::new(r))
    }

    /// [`aggregate_tree`]'s loop, transcribed verbatim over symbolic trees (pair adjacent
    /// left-to-right; odd tail promoted unchanged to the END of the next level).
    fn balanced_reference(mut level: Vec<ShapeTree>) -> ShapeTree {
        assert!(!level.is_empty());
        while level.len() > 1 {
            let mut next = Vec::with_capacity(level.len().div_ceil(2));
            let mut i = 0;
            while i + 1 < level.len() {
                next.push(br(level[i].clone(), level[i + 1].clone()));
                i += 2;
            }
            if i < level.len() {
                next.push(level.pop().expect("odd tail"));
            }
            level = next;
        }
        level.pop().expect("root")
    }

    /// THE SHAPE-IDENTITY WITNESS (exhaustive): for every chain length `n <= 300` and a window
    /// sweep (including non-powers-of-two, which floor), the streaming schedule builds EXACTLY
    /// the balanced tree. This is what licenses the streaming root exposing the identical
    /// (shape-sensitive) chain digest.
    #[test]
    fn streaming_schedule_matches_balanced_tree_shape() {
        for n in 1..=300usize {
            let reference = balanced_reference((0..n).map(ShapeTree::Leaf).collect());
            for window in [2usize, 3, 4, 5, 6, 7, 8, 12, 16, 32, 64, 128, 300] {
                let streamed: Result<ShapeTree, core::convert::Infallible> =
                    streaming_fold_schedule(
                        n,
                        window,
                        |i| Ok(ShapeTree::Leaf(i)),
                        |buf| Ok(balanced_reference(buf)),
                        |l, r| Ok(br(l, r)),
                    );
                let streamed = match streamed {
                    Ok(t) => t,
                };
                assert_eq!(
                    streamed, reference,
                    "shape diverged at n={n} window={window}"
                );
            }
        }
    }

    fn synthetic_seg(i: usize) -> HostSeg {
        let felt = |k: usize| {
            BabyBear::new(
                (i as u32)
                    .wrapping_mul(0x9e37)
                    .wrapping_add(k as u32 * 131 + 7)
                    % BABY_BEAR_MODULUS,
            )
        };
        let old8 = core::array::from_fn(felt);
        let new8 = core::array::from_fn(|k| felt(k + SEG_ANCHOR_WIDTH));
        leaf_seg(old8, new8)
    }

    /// The segment-level witness over the REAL combine ([`combine_seg`], Poseidon2 acc): the
    /// streaming host mirror equals the balanced host mirror. Because the digest is NOT
    /// associative, this equality holds ONLY via exact shape identity — a schedule bug would
    /// flip `acc` and fail here (and, in production, at the prover's fail-closed schedule
    /// guard before any proving).
    #[test]
    fn streaming_host_segment_equals_balanced_host_segment() {
        for n in 1..=96usize {
            let segs: Vec<HostSeg> = (0..n).map(synthetic_seg).collect();
            let reference = fold_host_segs_balanced(segs.clone());
            for window in [2usize, 3, 4, 8, 16, 96] {
                assert_eq!(
                    fold_host_segs_streaming(&segs, window),
                    reference,
                    "host segment diverged at n={n} window={window}"
                );
            }
        }
    }

    /// THE STANDING FINDING pinned as a test: [`combine_seg`] is associative in the endpoints
    /// and the count but NOT in the ordered digest `acc = H(L.acc ++ R.acc)` — `(a∘b)∘c` and
    /// `a∘(b∘c)` expose different digests. This is WHY the streaming fold must reproduce the
    /// balanced tree's shape instead of left-folding window sub-roots into one running
    /// accumulator (which WOULD change the whole-chain digest).
    #[test]
    fn ordered_digest_combine_is_not_associative() {
        let (a, b, c) = (synthetic_seg(1), synthetic_seg(2), synthetic_seg(3));
        let left = combine_seg(combine_seg(a, b), c);
        let right = combine_seg(a, combine_seg(b, c));
        assert_eq!(left.first_old8, right.first_old8);
        assert_eq!(left.last_new8, right.last_new8);
        assert_eq!(left.count, right.count);
        assert_ne!(
            left.acc, right.acc,
            "if acc were associative the shape constraint would be moot"
        );
    }

    /// THE O(W)-NOT-O(K) WITNESS: live-instance tokens through the schedule. Peak residency at
    /// n=512, W=8 must stay within the window + carry-stack bound (window W, carry stack
    /// log2(n/W) = 6, +1 in flight) — decisively sublinear in n. (The proof driver adds the
    /// window fold's internal ~W/2 per-level transient on top; still O(W).)
    #[test]
    fn streaming_schedule_peak_residency_is_window_bounded() {
        use std::cell::Cell;
        use std::rc::Rc;

        struct Token {
            live: Rc<Cell<(usize, usize)>>,
        }
        impl Token {
            fn new(live: &Rc<Cell<(usize, usize)>>) -> Self {
                let (current, peak) = live.get();
                let current = current + 1;
                live.set((current, peak.max(current)));
                Token { live: live.clone() }
            }
        }
        impl Drop for Token {
            fn drop(&mut self) {
                let (current, peak) = self.live.get();
                self.live.set((current - 1, peak));
            }
        }

        let (n, w) = (512usize, 8usize);
        let live = Rc::new(Cell::new((0usize, 0usize)));
        let folded: Result<Token, core::convert::Infallible> = streaming_fold_schedule(
            n,
            w,
            |_i| Ok(Token::new(&live)),
            |buf| {
                drop(buf); // the window fold consumes its window
                Ok(Token::new(&live))
            },
            |l, r| {
                drop((l, r)); // a merge consumes both children
                Ok(Token::new(&live))
            },
        );
        let root = match folded {
            Ok(t) => t,
        };
        let (_, peak) = live.get();
        drop(root);
        assert_eq!(live.get().0, 0, "every token dropped");
        // window (8) + carry stack (<= log2(512/8) = 6) + 1 in flight = 15; allow slack but
        // stay decisively sublinear.
        assert!(
            peak <= w + 7 + 1,
            "peak {peak} exceeded the O(W + log2(n/W)) bound"
        );
        assert!(peak * 8 < n, "peak {peak} is not sublinear in n={n}");
    }

    #[test]
    fn floor_pow2_window_floors() {
        for (input, expect) in [
            (0usize, 2usize),
            (1, 2),
            (2, 2),
            (3, 2),
            (4, 4),
            (5, 4),
            (7, 4),
            (8, 8),
            (9, 8),
            (1023, 512),
            (1024, 1024),
        ] {
            assert_eq!(
                floor_pow2_window(input),
                expect,
                "floor_pow2_window({input})"
            );
        }
    }

    // -----------------------------------------------------------------------------------------
    // THE MIXED-WIDTH CLEAN-HANDOFF HOST MIRROR (`fold_declared_windows`, the C->R boundary).
    // -----------------------------------------------------------------------------------------

    /// Synthetic per-turn window of `width` lanes filled from a base value (so distinct turns'
    /// windows are distinguishable). `PI value = base + lane`.
    fn syn_win(base: u32, width: usize) -> Vec<BabyBear> {
        (0..width as u32).map(|k| BabyBear::new(base + k)).collect()
    }

    /// The conflict-braid RoundState width and the clean round's `[board||marks||auto]` width, and
    /// the `board||marks` handoff prefix — the n = 11, P = 2 layout the M7 braid folds.
    const RS_W: usize = 32; // roundStateWindowLanes 11 2
    const CLEAN_W: usize = 20; // board(9) || marks(9) || auto(2)
    const HANDOFF_W: usize = 18; // board(9) || marks(9)

    /// **THE MIXED-WIDTH HOST MIRROR ACCEPTS AN HONEST C(32)->R(20) TURN.** A conflict braid whose
    /// rounds chain on the whole 32-lane window, handing off to a clean round on the 18-lane
    /// board||marks prefix, folds to the MIXED root window `[C_first.IN(32) ‖ R_last.OUT(20)]`.
    #[test]
    fn clean_handoff_host_mirror_accepts_an_honest_mixed_turn() {
        // Two conflict rounds (uniform 32) + one clean round (20). The 32-lane seam chains the
        // conflict rounds; the 18-lane prefix chains C_last.OUT -> R.IN.
        let c0_in = syn_win(100, RS_W);
        let c0_out = syn_win(200, RS_W);
        let c1_in = c0_out.clone(); // C_0.OUT == C_1.IN (uniform 32-lane seam)
        let c1_out = syn_win(300, RS_W);
        // The clean round's IN shares C_1.OUT's board||marks prefix (18) then has its own auto tail.
        let mut r_in = c1_out[..HANDOFF_W].to_vec();
        r_in.extend(syn_win(900, CLEAN_W - HANDOFF_W));
        let r_out = syn_win(500, CLEAN_W);

        let wins = vec![
            (c0_in.clone(), c0_out.clone()),
            (c1_in, c1_out.clone()),
            (r_in, r_out.clone()),
        ];
        let w = fold_declared_windows(&wins, Some(HANDOFF_W)).expect("honest mixed turn folds");
        assert_eq!(w.first_in, c0_in, "root IN = genesis RoundState (32 lanes)");
        assert_eq!(
            w.last_out, r_out,
            "root OUT = clean round's final state (20 lanes)"
        );
        assert_eq!(w.first_in.len(), RS_W);
        assert_eq!(w.last_out.len(), CLEAN_W);
    }

    /// **THE LOAD-BEARING NEGATIVE — A MISMATCHED marks IN THE HANDOFF IS REFUSED.** Forging ANY of
    /// the 18 board||marks prefix lanes at the C->R boundary breaks the clean-handoff seam (the host
    /// analogue of the in-circuit `WitnessConflict`).
    #[test]
    fn clean_handoff_host_mirror_refuses_a_mismatched_board_or_marks_lane() {
        let c_in = syn_win(100, RS_W);
        let c_out = syn_win(200, RS_W);
        let mut r_in = c_out[..HANDOFF_W].to_vec();
        r_in.extend(syn_win(900, CLEAN_W - HANDOFF_W));
        let r_out = syn_win(500, CLEAN_W);

        for lane in 0..HANDOFF_W {
            let mut forged = r_in.clone();
            forged[lane] += BabyBear::ONE; // R claims a board/marks lane C_last did not produce.
            let wins = vec![(c_in.clone(), c_out.clone()), (forged, r_out.clone())];
            let err = fold_declared_windows(&wins, Some(HANDOFF_W))
                .expect_err("a forged board||marks handoff lane must be refused");
            assert!(
                err.contains("clean-handoff seam broken"),
                "handoff lane {lane} must name the broken clean-handoff seam, got: {err}"
            );
        }
    }

    /// A differing `locked ‖ waiting ‖ auto` lane (PAST the 18-lane prefix) does NOT break the
    /// handoff — those tables are consumed at the clean round, not carried into Leg R. This mirrors
    /// `board_window_clean_handoff_connects` leaving the dropped lanes free.
    #[test]
    fn clean_handoff_host_mirror_ignores_dropped_lanes_past_the_prefix() {
        let c_in = syn_win(100, RS_W);
        let c_out = syn_win(200, RS_W);
        // R.IN's board||marks prefix agrees; its auto tail (lanes 18..20) differs freely.
        let mut r_in = c_out[..HANDOFF_W].to_vec();
        r_in.extend(syn_win(7777, CLEAN_W - HANDOFF_W)); // an auto tail C_last.OUT never dictated
        let r_out = syn_win(500, CLEAN_W);
        let wins = vec![(c_in, c_out), (r_in, r_out)];
        fold_declared_windows(&wins, Some(HANDOFF_W))
            .expect("a differing dropped (auto) lane must NOT break the clean handoff");
    }

    /// The mirror models a SINGLE C->R boundary: a chain with more than one window-width change is
    /// refused fail-closed.
    #[test]
    fn clean_handoff_host_mirror_refuses_more_than_one_width_change() {
        // 32 -> 20 -> 32: two width changes.
        let a_out = syn_win(200, RS_W);
        let mut b_in = a_out[..HANDOFF_W].to_vec();
        b_in.extend(syn_win(900, CLEAN_W - HANDOFF_W));
        let b_out = syn_win(300, CLEAN_W);
        let mut c_in = b_out[..HANDOFF_W].to_vec();
        c_in.extend(syn_win(1000, RS_W - HANDOFF_W));
        let wins = vec![
            (syn_win(100, RS_W), a_out),
            (b_in, b_out),
            (c_in, syn_win(400, RS_W)),
        ];
        let err = fold_declared_windows(&wins, Some(HANDOFF_W))
            .expect_err("two width changes must be refused");
        assert!(
            err.contains("more than one window-width change"),
            "got: {err}"
        );
    }

    /// The uniform path (`clean_handoff == None`) is byte-for-byte the pre-generalization behavior:
    /// an honest same-width chain folds, and a broken whole-window seam names "board-window seam
    /// broken" (the phrasing the deployed two-leg canaries match).
    #[test]
    fn uniform_path_is_unchanged_by_the_generalization() {
        let a_in = syn_win(1, 11);
        let a_out = syn_win(50, 11);
        let b_in = a_out.clone();
        let b_out = syn_win(90, 11);
        let honest = vec![(a_in.clone(), a_out.clone()), (b_in, b_out.clone())];
        let w = fold_declared_windows(&honest, None).expect("honest uniform chain folds");
        assert_eq!(w.first_in, a_in);
        assert_eq!(w.last_out, b_out);

        let mut broken_b_in = a_out.clone();
        broken_b_in[0] += BabyBear::ONE;
        let broken = vec![(a_in, a_out), (broken_b_in, b_out)];
        let err =
            fold_declared_windows(&broken, None).expect_err("a broken uniform seam is refused");
        assert!(err.contains("board-window seam broken"), "got: {err}");
    }
}

// ============================================================================
// THE BOARD-WINDOW SEAM CANARIES — the mechanism, at the constraint level.
// ============================================================================
//
// A REAL two-leg n=11 fold is tens of minutes (two custom leaves of 1273 and 680 columns, each
// with its own recursion wrap, plus the aggregation tree), so the end-to-end gate is `#[ignore]`d
// in `dreggnet-game-board/tests/two_leg_board_window.rs`. What runs HERE is the mechanism the
// whole design rests on, exercised at the level where it is decidable in milliseconds:
// `board_window_connects` is witness-slot ALIASING, so a broken seam is a `WitnessConflict` — a
// witness that does not exist, not a soft constraint a clever prover satisfies another way.
//
// SAY IT PLAINLY: these canaries pin the CONNECT. They do NOT show that a full deployed n=11 fold
// of a forged mid fails; only
// `two_leg_board_window.rs::a_mismatched_mid_does_not_fold_on_the_deployed_prover` settles that,
// and it has not been run. (Note: `prove_11x11.rs::mismatched_mid_fold_probe_11x11` is NOT that
// gate — it builds leaves on the Rust-AIR path, which declares no window, so this seam never
// reaches it.)
#[cfg(test)]
mod board_window_seam_tests {
    use super::*;
    use p3_circuit::CircuitBuilder;

    /// Build a bare circuit carrying two children's exposed claims as public inputs, wire ONLY the
    /// board-window seam between them, and try to drive it with `left`/`right` lane values. `Ok`
    /// iff a witness exists.
    fn run_seam(
        window: usize,
        left: &[u32],
        right: &[u32],
    ) -> Result<(), p3_circuit::errors::CircuitError> {
        let mut cb: CircuitBuilder<RecursionChallenge> = CircuitBuilder::new();
        let l: Vec<p3_recursion::Target> = cb.alloc_public_inputs(left.len(), "left_claim");
        let r: Vec<p3_recursion::Target> = cb.alloc_public_inputs(right.len(), "right_claim");
        board_window_connects(&mut cb, &l, &r, window);
        let circuit = cb.build().expect("the seam-only circuit builds");
        let mut runner = circuit.runner();
        let pubs: Vec<RecursionChallenge> = left
            .iter()
            .chain(right.iter())
            .map(|v| RecursionChallenge::from(P3BabyBear::from_u64(*v as u64)))
            .collect();
        runner.set_public_inputs(&pubs)?;
        runner.run().map(|_| ())
    }

    /// An honest automatafl leaf pair's claim lanes: `[segment(25) ‖ IN(11) ‖ OUT(11)]`, with the
    /// window halves filled from `win_in` / `win_out`.
    fn claim(seed: u32, win_in: &[u32], win_out: &[u32]) -> Vec<u32> {
        let mut c: Vec<u32> = (0..SEG_SPINE_WIDTH as u32).map(|k| seed + k).collect();
        c.extend_from_slice(win_in);
        c.extend_from_slice(win_out);
        c
    }

    /// The automatafl window width: `pack(9) ‖ auto(2)`.
    const W: usize = 11;

    /// **THE HONEST SEAM.** `R_i.OUT == A_i.IN` (the mid seam — `hseamPack ∧ hseamAutoX ∧
    /// hseamAutoY`) has a witness. Non-vacuous: the two children's lanes are DISTINCT public
    /// inputs (distinct expressions, distinct witness slots until the connect unions them), so the
    /// `a == b` early-out in `connect` never fires and every one of the 11 lanes is a real union.
    #[test]
    fn an_honest_mid_seam_has_a_witness() {
        let mid: Vec<u32> = (0..W as u32).map(|k| 7000 + 13 * k).collect();
        let old: Vec<u32> = (0..W as u32).map(|k| 100 + k).collect();
        let new: Vec<u32> = (0..W as u32).map(|k| 900 + k).collect();
        // Leg R: old -> mid.   Leg A: mid -> new.
        run_seam(W, &claim(1, &old, &mid), &claim(50, &mid, &new))
            .expect("an honest R.OUT == A.IN seam must be satisfiable");
    }

    /// **THE LOAD-BEARING NEGATIVE — A MISMATCHED MID IS UNSAT.** Leg A is fed a board Leg R did
    /// NOT produce. Every single lane of the window is load-bearing: forging ANY ONE of the 9 pack
    /// lanes or either automaton lane is a `WitnessConflict`. This is the mechanism that
    /// `mismatched_mid_diverges_board_roots_but_not_cell_continuity_11x11` records as ABSENT from
    /// the deployed cell-continuity tooth.
    #[test]
    fn every_forged_mid_lane_is_a_witness_conflict() {
        let mid: Vec<u32> = (0..W as u32).map(|k| 7000 + 13 * k).collect();
        let old: Vec<u32> = (0..W as u32).map(|k| 100 + k).collect();
        let new: Vec<u32> = (0..W as u32).map(|k| 900 + k).collect();

        for lane in 0..W {
            let mut forged = mid.clone();
            forged[lane] += 1; // Leg A claims it consumed a DIFFERENT board / automaton.
            let err = run_seam(W, &claim(1, &old, &mid), &claim(50, &forged, &new))
                .expect_err("a forged mid lane must have NO witness");
            assert!(
                matches!(
                    err,
                    p3_circuit::errors::CircuitError::WitnessConflict { .. }
                ),
                "forged mid lane {lane} must be a per-lane connect CONFLICT (UNSAT node, no root, \
                 no verifying artifact) — got {err:?}"
            );
        }
    }

    /// The SAME rule one level up is the INTER-ROUND CARRY: `A_i.OUT == R_{i+1}.IN`. A board
    /// substituted between rounds is the same conflict — which is exactly why the design needs no
    /// second mechanism for G2.
    #[test]
    fn a_substituted_board_between_rounds_is_a_witness_conflict() {
        let b0: Vec<u32> = (0..W as u32).map(|k| 100 + k).collect();
        let b1: Vec<u32> = (0..W as u32).map(|k| 400 + k).collect();
        let b2: Vec<u32> = (0..W as u32).map(|k| 900 + k).collect();
        run_seam(W, &claim(1, &b0, &b1), &claim(50, &b1, &b2))
            .expect("the honest inter-round carry is satisfiable");

        let mut substituted = b1.clone();
        substituted[0] += 1;
        let err = run_seam(W, &claim(1, &b0, &b1), &claim(50, &substituted, &b2))
            .expect_err("a substituted inter-round board must have NO witness");
        assert!(matches!(
            err,
            p3_circuit::errors::CircuitError::WitnessConflict { .. }
        ));
    }

    /// `window == 0` connects NOTHING — the plain-segment path every non-automatafl chain runs is
    /// untouched by this seam (the byte-identity requirement: the ordered digest is
    /// shape-sensitive).
    #[test]
    fn a_zero_window_connects_nothing() {
        let a: Vec<u32> = (0..SEG_SPINE_WIDTH as u32).collect();
        let b: Vec<u32> = (100..100 + SEG_SPINE_WIDTH as u32).collect();
        run_seam(0, &a, &b).expect("window 0 imposes no seam at all");
    }

    /// The lane arithmetic the whole design is stated in: a plain child exposes `SEG_SPINE_WIDTH`, a
    /// board-window child `SEG_SPINE_WIDTH + 2W`, and the automatafl `W = 11` gives the 47/46 pair the
    /// verifier and the leaf were extended to. Because the two windows are carried SIDE BY SIDE
    /// (never one), a genuine windowed exposure is always `SEG_SPINE_WIDTH` plus an EVEN number — which
    /// is what lets [`exposed_board_window`] recover `W` from the lane count alone and refuse any
    /// other shape instead of truncating it into a plain segment (silently dropping the seam) or
    /// padding it into a window.
    ///
    /// NOT tested here: [`exposed_board_window`] itself, which reads a real `BatchStarkProof` and
    /// so needs a prove.
    #[test]
    fn the_two_leg_lane_arithmetic_is_unambiguous() {
        // Two independent constants, both pinned: the segment itself is unchanged at 25, and the
        // spine adds exactly the 8 `vk_spine` lanes a fold node now exposes. Pinning only the sum
        // would let a future edit move one and compensate in the other without anything going red.
        assert_eq!(
            SEG_WIDTH, 25,
            "the segment exposure, unchanged by the spine"
        );
        assert_eq!(SEG_SPINE_WIDTH, 33, "segment + the 8 vk_spine lanes");
        assert_eq!(
            SEG_SPINE_WIDTH + 2 * W,
            55,
            "the board-window root exposure"
        );
        assert_eq!(
            crate::custom_leaf_adapter::custom_board_window_claim_len(W),
            46,
            "the board-window leaf exposure"
        );
        for w in 1..64usize {
            assert_eq!(
                (SEG_SPINE_WIDTH + 2 * w - SEG_SPINE_WIDTH) % 2,
                0,
                "a windowed exposure is SEG_SPINE_WIDTH plus an EVEN count at every W"
            );
        }
    }

    // ========================================================================
    // THE ROUNDSTATE SEAM (M5) — the whole-RoundState conflict chain and the
    // board+marks clean handoff, at the constraint level.
    // ========================================================================
    //
    // The mechanism above is width-GENERIC (`board_window_connects` takes `window: usize`), so the
    // conflict chain rides it unchanged at W = 32. What is genuinely new is the CLEAN HANDOFF
    // (`board_window_clean_handoff_connects`): two legs of DIFFERENT widths, connected on their
    // shared `board ‖ marks` prefix only. These canaries pin BOTH connects at the level where a
    // broken seam is decidable in milliseconds — a `WitnessConflict`, a witness that does not exist.

    /// The RoundState window width the conflict chain carries: `board(9) ‖ marks(9) ‖ locked(10) ‖
    /// waiting(2) ‖ auto(2)` = `roundStateWindowLanes 11 2`.
    const RS: usize = 32;
    /// The board+marks prefix the CLEAN handoff carries; `locked ‖ waiting ‖ auto` sit past it.
    const HANDOFF: usize = 18;
    /// The marks sub-window sits at lanes `[9, 18)` of the RoundState window (after the 9-lane board).
    const MARKS_LO: usize = 9;
    const MARKS_HI: usize = 18;

    /// **THE HONEST CONFLICT SEAM (C→C).** `C_k.OUT == C_{k+1}.IN` over the WHOLE 32-lane
    /// RoundState window has a witness. Non-vacuous: the two children's window lanes are DISTINCT
    /// public inputs, so every one of the 32 connects is a real union, not a `a == a` early-out.
    #[test]
    fn an_honest_roundstate_conflict_seam_has_a_witness() {
        let mid: Vec<u32> = (0..RS as u32).map(|k| 5000 + 7 * k).collect();
        let old: Vec<u32> = (0..RS as u32).map(|k| 100 + k).collect();
        let new: Vec<u32> = (0..RS as u32).map(|k| 900 + k).collect();
        run_seam(RS, &claim(1, &old, &mid), &claim(50, &mid, &new))
            .expect("an honest C_k.OUT == C_{k+1}.IN RoundState seam must be satisfiable");
    }

    /// **THE LOAD-BEARING NEGATIVE — A MISMATCHED marksOut IS UNSAT.** `C_{k+1}` is fed a marks
    /// overlay `C_k` did NOT produce. This is the MARKS analogue of
    /// `every_forged_mid_lane_is_a_witness_conflict`: every one of the 9 marks lanes is
    /// load-bearing, and forging ANY ONE is a per-lane `connect` conflict (UNSAT node ⇒ no root ⇒
    /// no verifying artifact). Per-leaf validity cannot catch it — only the seam can.
    #[test]
    fn a_mismatched_marks_out_in_the_roundstate_seam_is_a_witness_conflict() {
        let mid: Vec<u32> = (0..RS as u32).map(|k| 5000 + 7 * k).collect();
        let old: Vec<u32> = (0..RS as u32).map(|k| 100 + k).collect();
        let new: Vec<u32> = (0..RS as u32).map(|k| 900 + k).collect();
        for lane in MARKS_LO..MARKS_HI {
            let mut forged = mid.clone();
            forged[lane] += 1; // C_{k+1} claims a DIFFERENT marksIn than C_k produced as marksOut.
            let err = run_seam(RS, &claim(1, &old, &mid), &claim(50, &forged, &new))
                .expect_err("a forged marks lane must have NO witness");
            assert!(
                matches!(
                    err,
                    p3_circuit::errors::CircuitError::WitnessConflict { .. }
                ),
                "forged marks lane {lane} must be a per-lane connect CONFLICT — got {err:?}"
            );
        }
    }

    /// Build a bare circuit carrying a WIDE conflict child (`l_window`-lane windows) and a CLEAN
    /// child (`r_window`-lane windows), wire ONLY the clean handoff between them, and try to drive
    /// it. The conflict child's OUT window is `l_out`; the clean child's IN window is `r_in`.
    fn run_handoff(
        l_window: usize,
        r_window: usize,
        handoff: usize,
        l_out: &[u32],
        r_in: &[u32],
    ) -> Result<(), p3_circuit::errors::CircuitError> {
        // left  = seg(25) ‖ IN_l(l_window) ‖ OUT_l(l_window)   (IN_l is irrelevant to the handoff)
        let mut left: Vec<u32> = (0..SEG_SPINE_WIDTH as u32).map(|k| 1 + k).collect();
        left.extend((0..l_window as u32).map(|k| 40_000 + k));
        left.extend_from_slice(l_out);
        // right = seg(25) ‖ IN_r(r_window) ‖ OUT_r(r_window)   (OUT_r is irrelevant to the handoff)
        let mut right: Vec<u32> = (0..SEG_SPINE_WIDTH as u32).map(|k| 60_000 + k).collect();
        right.extend_from_slice(r_in);
        right.extend((0..r_window as u32).map(|k| 90_000 + k));

        let mut cb: CircuitBuilder<RecursionChallenge> = CircuitBuilder::new();
        let l: Vec<p3_recursion::Target> = cb.alloc_public_inputs(left.len(), "left_claim");
        let r: Vec<p3_recursion::Target> = cb.alloc_public_inputs(right.len(), "right_claim");
        board_window_clean_handoff_connects(&mut cb, &l, &r, l_window, handoff);
        let circuit = cb.build().expect("the handoff-only circuit builds");
        let mut runner = circuit.runner();
        let pubs: Vec<RecursionChallenge> = left
            .iter()
            .chain(right.iter())
            .map(|v| RecursionChallenge::from(P3BabyBear::from_u64(*v as u64)))
            .collect();
        runner.set_public_inputs(&pubs)?;
        runner.run().map(|_| ())
    }

    /// **THE CLEAN HANDOFF (C→R) CONNECTS board ‖ marks AND DROPS locked ‖ waiting.** With the
    /// conflict round's board+marks prefix equal to the clean round's, the handoff is satisfiable;
    /// a differing locked/waiting/auto lane (past the prefix) leaves it satisfiable — those tables
    /// are CONSUMED at the clean round, not carried; and a differing board-or-marks lane (inside
    /// the prefix) is a `WitnessConflict`, the same force as the conflict seam.
    #[test]
    fn the_clean_handoff_connects_board_and_marks_and_drops_locked_waiting() {
        // A clean round's window whose leading 18 lanes are board ‖ marks (then, say, auto).
        let r_window = 20usize;
        let c_out: Vec<u32> = (0..RS as u32).map(|k| 3000 + k).collect();
        let mut r_in: Vec<u32> = c_out[..HANDOFF].to_vec(); // board ‖ marks AGREE
        r_in.extend((HANDOFF as u32..r_window as u32).map(|k| 8000 + k));

        // Honest: the board ‖ marks prefixes agree.
        run_handoff(RS, r_window, HANDOFF, &c_out, &r_in)
            .expect("an honest clean handoff (board ‖ marks agree) must be satisfiable");

        // A differing LOCKED / WAITING / AUTO lane of C_last.OUT does NOT break the handoff — it is
        // consumed at the clean round, not carried into Leg R.
        for lane in HANDOFF..RS {
            let mut c2 = c_out.clone();
            c2[lane] += 1;
            run_handoff(RS, r_window, HANDOFF, &c2, &r_in).unwrap_or_else(|e| {
                panic!(
                    "a differing dropped lane {lane} (locked/waiting/auto) must NOT break the \
                     clean handoff — it is consumed, not carried — got {e:?}"
                )
            });
        }

        // A differing BOARD-or-MARKS lane (inside the connected prefix) DOES break it.
        for lane in 0..HANDOFF {
            let mut c2 = c_out.clone();
            c2[lane] += 1;
            let err = run_handoff(RS, r_window, HANDOFF, &c2, &r_in)
                .expect_err("a board/marks disagreement across the clean handoff has NO witness");
            assert!(
                matches!(
                    err,
                    p3_circuit::errors::CircuitError::WitnessConflict { .. }
                ),
                "clean-handoff lane {lane} (board ‖ marks) must be a connect CONFLICT — got {err:?}"
            );
        }
    }

    /// The RoundState lane arithmetic the M5 generalization is stated in, and the fail-closed shape
    /// the (already width-generic) verifier recovers. A conflict-round LEAF exposes `24 + 2·32 =
    /// 88` claim lanes; a conflict-round segment ROOT exposes `25 + 2·32 = 89`; and
    /// [`exposed_board_window`] recovers `W = 32` from the 89-lane count alone (no verifier change
    /// was needed — the seam was width-generic; only the DECLARATION and the clean handoff are new).
    #[test]
    fn the_roundstate_lane_arithmetic_is_unambiguous() {
        assert_eq!(RS, 32, "roundStateWindowLanes 11 2");
        assert_eq!(SEG_SPINE_WIDTH + 2 * RS, 97, "the RoundState root exposure");
        assert_eq!(
            crate::custom_leaf_adapter::custom_board_window_claim_len(RS),
            88,
            "the RoundState leaf exposure (commitment(8) ‖ old8 ‖ new8 ‖ IN(32) ‖ OUT(32))"
        );
        // The generic recovery `exposed_board_window` performs: (lanes - SEG_SPINE_WIDTH) / 2.
        assert_eq!((SEG_SPINE_WIDTH + 2 * RS - SEG_SPINE_WIDTH) / 2, RS);
        assert_eq!(HANDOFF, 18, "the clean handoff carries board(9) ‖ marks(9)");
        // The clean handoff must be STRICTLY narrower than the round-state window — it drops
        // `locked ‖ waiting ‖ auto`, and a handoff as wide as the window would mean it dropped
        // nothing and the two seams are the same seam. Two constants: a build obligation.
        const _: () = assert!(
            HANDOFF < RS,
            "the clean handoff must be strictly narrower than the RoundState window"
        );
    }

    /// The clean round's `[board(9) ‖ marks(9) ‖ auto(2)]` window width (the resolve-marks leg's
    /// interface the mixed handoff hands off TO).
    const CLEAN_W: usize = 20;

    /// Drive the MERGE NODE's board-visible half (`clean_handoff_seam_and_window` — the seam +
    /// parent MIXED-window carry) in a bare `CircuitBuilder`: a left conflict child (`l_window`-lane
    /// windows), a right clean child (`r_window`-lane windows), the clean-handoff seam wired between
    /// them. `Ok` iff a witness exists. (No `expose_as_public_output` — that needs the recursion
    /// config's `enable_expose_claim`; the seam is what a broken handoff violates.)
    fn run_merge_node(
        l_window: usize,
        r_window: usize,
        handoff: usize,
        l_out: &[u32],
        r_in: &[u32],
    ) -> Result<(), p3_circuit::errors::CircuitError> {
        // left  = seg(25) ‖ IN_l(l_window) ‖ OUT_l(l_window)
        let mut left: Vec<u32> = (0..SEG_SPINE_WIDTH as u32).map(|k| 1 + k).collect();
        left.extend((0..l_window as u32).map(|k| 40_000 + k));
        left.extend_from_slice(l_out);
        // right = seg(25) ‖ IN_r(r_window) ‖ OUT_r(r_window)
        let mut right: Vec<u32> = (0..SEG_SPINE_WIDTH as u32).map(|k| 60_000 + k).collect();
        right.extend_from_slice(r_in);
        right.extend((0..r_window as u32).map(|k| 90_000 + k));

        let mut cb: CircuitBuilder<RecursionChallenge> = CircuitBuilder::new();
        let l: Vec<p3_recursion::Target> = cb.alloc_public_inputs(left.len(), "left_claim");
        let r: Vec<p3_recursion::Target> = cb.alloc_public_inputs(right.len(), "right_claim");
        let _window = clean_handoff_seam_and_window(&mut cb, &l, &r, l_window, r_window, handoff);
        let circuit = cb.build().expect("the merge-node circuit builds");
        let mut runner = circuit.runner();
        let pubs: Vec<RecursionChallenge> = left
            .iter()
            .chain(right.iter())
            .map(|v| RecursionChallenge::from(P3BabyBear::from_u64(*v as u64)))
            .collect();
        runner.set_public_inputs(&pubs)?;
        runner.run().map(|_| ())
    }

    /// **THE MIXED-WIDTH MERGE NODE (C→R): the parent produces `[L.IN(32) ‖ R.OUT(20)]` and seams
    /// board||marks.** This is the M7-finding closure — the clean handoff is no longer a bare connect
    /// primitive but wired into a parent-segment producer. Two halves are canaried:
    ///
    ///   * STRUCTURAL: the parent MIXED window `clean_handoff_seam_and_window` carries is EXACTLY
    ///     `[L.IN(l_window) ‖ R.OUT(r_window)]`, in order — the 32-lane genesis RoundState followed by
    ///     the 20-lane clean-round final state, `SEG_SPINE_WIDTH + 32 + 20 = 77` root lanes total.
    ///   * SEAM: an honest C(32)→R(20) handoff (board||marks agree) is satisfiable; a mismatched
    ///     board-or-marks lane is a `WitnessConflict` (UNSAT node ⇒ no root ⇒ no verifying artifact);
    ///     a differing dropped `locked ‖ waiting ‖ auto` lane leaves it satisfiable (consumed at the
    ///     clean round, not carried).
    #[test]
    fn the_mixed_width_merge_node_carries_the_mixed_window_and_seams_board_marks() {
        // ---- STRUCTURAL: the parent window IS [L.IN(l_window) ‖ R.OUT(r_window)], in that order.
        {
            let mut cb: CircuitBuilder<RecursionChallenge> = CircuitBuilder::new();
            let l: Vec<p3_recursion::Target> =
                cb.alloc_public_inputs(SEG_SPINE_WIDTH + 2 * RS, "left_claim");
            let r: Vec<p3_recursion::Target> =
                cb.alloc_public_inputs(SEG_SPINE_WIDTH + 2 * CLEAN_W, "right_claim");
            let window = clean_handoff_seam_and_window(&mut cb, &l, &r, RS, CLEAN_W, HANDOFF);
            assert_eq!(
                window.len(),
                RS + CLEAN_W,
                "the parent MIXED window is L.IN(32) ‖ R.OUT(20) = 52 lanes; the root exposes \
                 SEG_SPINE_WIDTH + 52 = {} lanes",
                SEG_SPINE_WIDTH + RS + CLEAN_W
            );
            let mut expected: Vec<p3_recursion::Target> =
                l[SEG_SPINE_WIDTH..SEG_SPINE_WIDTH + RS].to_vec();
            expected
                .extend_from_slice(&r[SEG_SPINE_WIDTH + CLEAN_W..SEG_SPINE_WIDTH + 2 * CLEAN_W]);
            assert_eq!(
                window, expected,
                "the parent window selects L.IN (the genesis RoundState) then R.OUT (the clean \
                 round's final state), lane for lane"
            );
        }

        // ---- SEAM: honest accepts; mismatched board||marks is a WitnessConflict; dropped lanes free.
        let c_out: Vec<u32> = (0..RS as u32).map(|k| 3000 + k).collect();
        let mut r_in: Vec<u32> = c_out[..HANDOFF].to_vec(); // board ‖ marks AGREE
        r_in.extend((HANDOFF as u32..CLEAN_W as u32).map(|k| 8000 + k));

        run_merge_node(RS, CLEAN_W, HANDOFF, &c_out, &r_in)
            .expect("an honest mixed C(32)->R(20) merge node (board||marks agree) is satisfiable");

        for lane in HANDOFF..RS {
            let mut c2 = c_out.clone();
            c2[lane] += 1;
            run_merge_node(RS, CLEAN_W, HANDOFF, &c2, &r_in).unwrap_or_else(|e| {
                panic!(
                    "a differing dropped lane {lane} (locked/waiting/auto) must NOT break the mixed \
                     merge node — it is consumed, not carried — got {e:?}"
                )
            });
        }

        for lane in 0..HANDOFF {
            let mut c2 = c_out.clone();
            c2[lane] += 1;
            let err = run_merge_node(RS, CLEAN_W, HANDOFF, &c2, &r_in).expect_err(
                "a board/marks disagreement across the mixed merge node has NO witness",
            );
            assert!(
                matches!(
                    err,
                    p3_circuit::errors::CircuitError::WitnessConflict { .. }
                ),
                "mixed-merge-node board||marks lane {lane} must be a per-lane connect CONFLICT — \
                 got {err:?}"
            );
        }
    }
}
