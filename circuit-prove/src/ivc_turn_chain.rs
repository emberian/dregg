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
//! 1. **[`TurnChainBindingAir`]** (one row per folded position): binds the
//!    sequential chain AND the running ordered-history digest. Each row carries
//!    `[old_root, new_root, acc_in, acc_out, idx, is_real, real_count]` plus the
//!    per-row Poseidon2 permutation aux block, with constraints:
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
//!    A trace whose turns are reordered, or that drops/inserts a turn, breaks
//!    continuity and is UNSAT; a forged `chain_digest` has no satisfying Poseidon2
//!    witness; a forged `num_turns` mismatches the real-row count — those are the
//!    load-bearing rejections.
//!
//! 2. **The recursion tree (Gold) — REAL leaves.** Each finalized turn's leaf
//!    is the **Lean-descriptor EffectVM AIR itself** ([`EffectVmDescriptorAir`],
//!    the graduated ONE-circuit cutover constraint set: Poseidon2 state-commit
//!    hash sites, per-row gates, transition continuity, `OLD_COMMIT`/`NEW_COMMIT`
//!    PI bindings, balance range checks), re-proven as a recursion-compatible
//!    uni-STARK over the **same 186-column execution trace** the turn's
//!    production rotated IR-v2 batch proof (the retired v1 `EffectVmP3Proof`)
//!    attests, then wrapped in its own **in-circuit verifier layer**
//!    (uni->batch via `build_and_prove_next_layer`). The chain-binding leaf is
//!    wrapped too, and all batch leaves are pairwise aggregated up a binary tree
//!    (`build_and_prove_aggregation_layer`, chained via [`BatchOnly`]) to ONE
//!    root batch-STARK proof. The verifier checks ONLY the root; its cost is
//!    independent of K.
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
//!   2. **Claimed-publics attestation** — the carried `genesis_root` /
//!      `final_root` / `num_turns` / `chain_digest` must verify as the public
//!      inputs of the carried chain-binding uni-STARK
//!      (`WholeChainProof::binding_proof`, the same statement the fold wraps
//!      in-circuit). Fiat–Shamir binds all four PIs into that proof, so
//!      relabeling any carried field is refused outright.
//!   3. **The root** — `verify_recursive_batch_proof` on the single root.
//!
//! ## CRITICAL HOLES #1/#2/#6 — CLOSED by the ordered SEGMENT ACCUMULATOR (2026-06-24)
//!
//! A cross-model adversarial review (`docs/CODEX-IVC-SOUNDNESS-REVIEW.md` +
//! `CODEX-IVC-REVIEW-2.md`) found a forged whole-chain claim the verifier ACCEPTS: a
//! root that EXECUTED history A paired with a whole-chain CLAIM for a different history
//! B. The root cause was that the chain claim came from a SEPARATE `TurnChainBindingAir`
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
//! teeth (`binding_air_forged_digest_unsat` / `binding_air_forged_num_turns_unsat`) all
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
//! - **Child-circuit identity under the VK pin (fork follow-up — CLOSED).** [`aggregate_tree`]
//!   now folds EVERY child (descriptor leaf or interior aggregation node) through the fork's
//!   `into_recursion_input_pinned` path: each child's own preprocessed commitment (its
//!   VK-identity core — the Merkle cap binding its static op-list) is baked as a CONSTANT the
//!   parent aggregation circuit `connect`s its child-commitment targets to. A foreign-circuit
//!   child is refused in-band either way — keep the honest constant and the foreign child's
//!   in-circuit preprocessed-trace FRI check is UNSAT (its real commitment ≠ the pinned
//!   constant); bake the foreign commitment and the parent op-list changes, so the ROOT
//!   preprocessed commitment changes and the root VK fingerprint (tooth 1) stops matching the
//!   honest anchor. The pinned constants live in every node's op-list up to the root, so the
//!   root VK pin TRANSITIVELY certifies the whole tree's leaf-circuit identity — the leaf VK no
//!   longer rests on a same-shape argument. (Previously pinned only on the online
//!   [`crate::accumulator`] fixed-point path; the balanced-tree K-fold is now pinned too.)
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

use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_baby_bear::BabyBear as P3BabyBear;
use p3_field::{PrimeCharacteristicRing, PrimeField32};
use p3_matrix::dense::RowMajorMatrix;
use p3_recursion::{
    BatchOnly, ProveNextLayerParams, RecursionInput, RecursionOutput,
    build_and_prove_aggregation_layer_with_expose, build_and_prove_next_layer,
    build_and_prove_next_layer_with_expose,
};

use crate::joint_turn_aggregation::{
    CarrierWitness, DescriptorParticipant, verify_descriptor_participant,
};
use crate::plonky3_recursion_impl::recursive::{
    DreggRecursionConfig, RecursionCompatibleProof, create_recursion_backend,
    recursion_vk_fingerprint, verify_recursive_batch_proof_with_config,
};
use dregg_circuit::descriptor_ir2::Ir2BatchProof;
use dregg_circuit::field::BabyBear;
use dregg_circuit::plonky3_prover::{
    POSEIDON2_PERM_AUX_COLS, POSEIDON2_WIDTH, poseidon2_permute_aux_witness, poseidon2_permute_expr,
};
use dregg_circuit::poseidon2::hash_4_to_1;

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
/// (`docs/FAITHFUL-STATE-COMMITMENT.md`, `docs/deos/COMMITMENT-WAIST-CENSUS.md` #1) widened it
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
    /// **The claimed chain publics are unattested.** The carried
    /// `genesis_root`/`final_root`/`num_turns`/`chain_digest` failed to
    /// verify as the public inputs of the carried chain-binding proof —
    /// a relabeled (spliced) public claim.
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
// TurnChainBindingAir: the sequential (temporal) chain binding.
// ============================================================================

// Column layout of the chain-binding trace (one row per folded position).
//
// SOUNDNESS NOTE (#2 fix): the running digest `acc_out` is NO LONGER a free
// witness column. Each row carries the FULL in-circuit Poseidon2 permutation aux
// block, and `acc_out` is forced to be `poseidon2([acc_in, old_root, new_root,
// idx, 4, 0..])[0]` — exactly the `hash_4_to_1` the trace generator computes.
// A forged `chain_digest` (a tampered `acc_out` on the last row) therefore has
// no satisfying witness, and a forged `num_turns` is rejected by the real-row
// counter binding (`real_count[last] == num_turns`).
pub(crate) const COL_OLD_ROOT: usize = 0;
pub(crate) const COL_NEW_ROOT: usize = 1;
const COL_ACC_IN: usize = 2;
pub(crate) const COL_ACC_OUT: usize = 3;
const COL_IDX: usize = 4;
const COL_IS_REAL: usize = 5;
const COL_REAL_COUNT: usize = 6;
/// First column of the per-row Poseidon2 permutation aux block.
const BINDING_AUX0: usize = 7;
/// Total binding-AIR trace width: 7 scalar columns + the Poseidon2 aux block.
const BINDING_WIDTH: usize = BINDING_AUX0 + POSEIDON2_PERM_AUX_COLS;
/// The arity domain-separation tag `hash_4_to_1` seeds at state position 4.
const HASH_ARITY_TAG: u32 = 4;

/// AIR binding the finalized turn order AND the running ordered-history digest.
/// One row per folded position: `[old_root, new_root, acc_in, acc_out, idx,
/// is_real, real_count, <Poseidon2 aux block>]`.
///
/// Public inputs `[genesis_root, final_root, num_turns, chain_digest]`.
///
/// Constraints:
///   1. chain continuity (transition): `new_root[i] == old_root[i+1]` — the
///      temporal tooth. A reordered/dropped/inserted turn breaks this and is
///      UNSAT.
///   2. first row `old_root == genesis_root`.
///   3. last row `new_root == final_root`.
///   4. running digest continuity: `acc_out[i] == acc_in[i+1]`; first row
///      `acc_in == 0`; last row `acc_out == chain_digest`.
///   5. **per-row hash binding (THE #2 fix):** `acc_out == poseidon2([acc_in,
///      old_root, new_root, idx], arity=4)[0]`, the genuine in-circuit Poseidon2
///      (the SAME arithmetization `P3MerklePoseidon2Air` uses, via
///      [`poseidon2_permute_expr`]). `acc_out` is no longer free — a forged
///      `chain_digest` has no satisfying witness.
///   6. **idx counter:** `idx == 0` on the first row, `idx[i+1] == idx[i] + 1`
///      on transitions — the hash is POSITIONALLY bound (rows cannot be
///      permuted without breaking the digest).
///   7. **num_turns binding:** `is_real` is boolean and monotone non-increasing
///      (real rows first, then padding); `real_count` runs the cumulative count
///      of real rows; the last row pins `real_count == num_turns`. A forged
///      `num_turns` (≠ the real folded count) is UNSAT.
///
/// The digest commits to the ordered (old_root, new_root, idx) triples, so two
/// distinct finalized histories with the same endpoints still yield distinct
/// digests, and a reordering moves `idx` and so the digest.
pub struct TurnChainBindingAir;

impl<F: PrimeCharacteristicRing + Sync> BaseAir<F> for TurnChainBindingAir {
    fn width(&self) -> usize {
        BINDING_WIDTH
    }

    fn num_public_values(&self) -> usize {
        4 // [genesis_root, final_root, num_turns, chain_digest]
    }

    fn main_next_row_columns(&self) -> Vec<usize> {
        // Next-row reads: old_root (continuity), acc_in (digest chain), idx
        // (counter), is_real (monotonicity), real_count (cumulative count).
        vec![
            COL_OLD_ROOT,
            COL_ACC_IN,
            COL_IDX,
            COL_IS_REAL,
            COL_REAL_COUNT,
        ]
    }
}

impl<AB: AirBuilder> Air<AB> for TurnChainBindingAir
where
    AB::F: PrimeField32,
{
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let local = main.current_slice();
        let next = main.next_slice();

        let old_root: AB::Expr = local[COL_OLD_ROOT].into();
        let new_root: AB::Expr = local[COL_NEW_ROOT].into();
        let acc_in: AB::Expr = local[COL_ACC_IN].into();
        let acc_out: AB::Expr = local[COL_ACC_OUT].into();
        let idx: AB::Expr = local[COL_IDX].into();
        let is_real: AB::Expr = local[COL_IS_REAL].into();
        let real_count: AB::Expr = local[COL_REAL_COUNT].into();
        let next_old_root: AB::Expr = next[COL_OLD_ROOT].into();
        let next_acc_in: AB::Expr = next[COL_ACC_IN].into();
        let next_idx: AB::Expr = next[COL_IDX].into();
        let next_is_real: AB::Expr = next[COL_IS_REAL].into();
        let next_real_count: AB::Expr = next[COL_REAL_COUNT].into();

        let public_values = builder.public_values();
        let genesis_root: AB::Expr = public_values[0].into();
        let final_root: AB::Expr = public_values[1].into();
        let num_turns: AB::Expr = public_values[2].into();
        let chain_digest: AB::Expr = public_values[3].into();

        // Constraint 1 (THE temporal tooth): chain continuity. Each turn's
        // new_root must be the next turn's old_root.
        builder
            .when_transition()
            .assert_zero(new_root.clone() - next_old_root);

        // Constraint 2: first row old_root == genesis_root.
        builder
            .when_first_row()
            .assert_zero(old_root.clone() - genesis_root);

        // Constraint 3: last row new_root == final_root.
        builder
            .when_last_row()
            .assert_zero(new_root.clone() - final_root);

        // Constraint 4: running digest chain.
        builder.when_first_row().assert_zero(acc_in.clone());
        builder
            .when_transition()
            .assert_zero(acc_out.clone() - next_acc_in);
        builder
            .when_last_row()
            .assert_zero(acc_out.clone() - chain_digest);

        // Constraint 5 (THE #2 FIX): per-row hash binding. The running digest is
        // FORCED to be the genuine Poseidon2 of `[acc_in, old_root, new_root,
        // idx]` with the arity-4 domain tag — byte-identical to the trace
        // generator's `hash_4_to_1`. `acc_out` is no longer a free column.
        let aux: &[AB::Var] = &local[BINDING_AUX0..BINDING_AUX0 + POSEIDON2_PERM_AUX_COLS];
        let arity_tag = AB::F::from_u32(HASH_ARITY_TAG);
        let input_state: [AB::Expr; POSEIDON2_WIDTH] = core::array::from_fn(|i| match i {
            0 => acc_in.clone(),
            1 => old_root.clone(),
            2 => new_root.clone(),
            3 => idx.clone(),
            4 => AB::Expr::from(arity_tag),
            _ => AB::Expr::ZERO,
        });
        let digest = poseidon2_permute_expr(builder, input_state, aux);
        builder.assert_zero(acc_out - digest);

        // Constraint 6: idx is a positional counter (0, 1, 2, ...).
        builder.when_first_row().assert_zero(idx.clone());
        builder
            .when_transition()
            .assert_zero(next_idx - (idx + AB::Expr::ONE));

        // Constraint 7: num_turns is the count of REAL (non-padding) rows.
        //   - is_real is boolean;
        //   - is_real is monotone non-increasing (real rows first, then padding):
        //     a 0->1 transition is forbidden, so `next_is_real * (1 - is_real) == 0`;
        //   - real_count starts at is_real[0] and accumulates is_real;
        //   - the last row pins real_count == num_turns.
        builder.assert_bool(is_real.clone());
        builder
            .when_transition()
            .assert_zero(next_is_real.clone() * (AB::Expr::ONE - is_real.clone()));
        builder
            .when_first_row()
            .assert_zero(real_count.clone() - is_real);
        builder
            .when_transition()
            .assert_zero(next_real_count - (real_count.clone() + next_is_real));
        builder.when_last_row().assert_zero(real_count - num_turns);
    }
}

// ============================================================================
// Trace generation for the chain binding.
// ============================================================================
//
// Bucket-F (PATH-PRESERVE Phase 5a): the v1 `generate_chain_trace` /
// `generate_chain_trace_unchecked` (which read v1 OLD/NEW_COMMIT at PI 0/4) are DELETED.
// The rotated fold builds its binding trace via `generate_chain_trace_rotated` (reading the
// ROTATED commitments at PI 34/35).

pub(crate) fn trace_to_matrix(trace: &[Vec<BabyBear>]) -> RowMajorMatrix<P3BabyBear> {
    debug_assert!(
        trace.iter().all(|row| row.len() == BINDING_WIDTH),
        "binding trace rows must all be {BINDING_WIDTH} wide"
    );
    let values: Vec<P3BabyBear> = trace
        .iter()
        .flat_map(|row| row.iter().map(|&v| to_p3(v)))
        .collect();
    RowMajorMatrix::new(values, BINDING_WIDTH)
}

/// Read a finalized turn's chain roots from its mandatory ROTATED leg (PI 34/35).
///
/// Bucket-F (PATH-PRESERVE Phase 5a): the rotated leg is MANDATORY — `FinalizedTurn` carries
/// exactly one [`crate::joint_turn_aggregation::RotatedParticipantLeg`], so reading its roots is
/// infallible (no v1 fallback leg, no `Option`).
fn rotated_roots(t: &FinalizedTurn) -> (BabyBear, BabyBear) {
    let leg = &t.participant.rotated;
    (leg.old_root(), leg.new_root())
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

/// Fold the per-turn leaf segments into the ROOT segment using the SAME pairwise
/// left-to-right binary tree (with odd-element carry) that [`aggregate_tree`] runs
/// in-circuit — so the host-computed root `[first_old8, last_new8, count, acc]`
/// equals what the root proof exposes.
fn compute_root_segment(turns: &[&FinalizedTurn]) -> HostSeg {
    let mut level: Vec<HostSeg> = turns
        .iter()
        .map(|t| {
            let (o8, n8) = turn_anchors8(t);
            leaf_seg(o8, n8)
        })
        .collect();
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

/// [`generate_chain_trace`] reading the ROTATED chain roots (PI 34/35) instead of the v1
/// OLD/NEW_COMMIT (PI 0/4). The binding leaf the rotated fold wraps therefore commits to the
/// rotated v9 commitments.
fn generate_chain_trace_rotated(
    turns: &[&FinalizedTurn],
) -> Result<(Vec<Vec<BabyBear>>, Vec<BabyBear>, BabyBear), TurnChainError> {
    if turns.len() < 2 {
        return Err(TurnChainError::TooFewTurns { count: turns.len() });
    }
    for i in 1..turns.len() {
        let (_, prev_new) = rotated_roots(turns[i - 1]);
        let (this_old, _) = rotated_roots(turns[i]);
        if prev_new != this_old {
            return Err(TurnChainError::ChainBreak {
                index: i,
                expected_old_root: prev_new.0,
                found_old_root: this_old.0,
            });
        }
    }
    let n = turns.len();
    let padded_len = n.next_power_of_two().max(2);
    let mut trace: Vec<Vec<BabyBear>> = Vec::with_capacity(padded_len);
    let mut acc = BabyBear::ZERO;
    let mut real_count = BabyBear::ZERO;
    for (i, t) in turns.iter().enumerate() {
        let (old_root, new_root) = rotated_roots(t);
        let idx = BabyBear::new(i as u32);
        real_count += BabyBear::ONE;
        let (acc_out, row) = binding_row(
            old_root, new_root, acc, idx, /* is_real */ true, real_count,
        );
        trace.push(row);
        acc = acc_out;
    }
    let final_root = trace.last().unwrap()[COL_NEW_ROOT];
    for i in n..padded_len {
        let idx = BabyBear::new(i as u32);
        // Padding rows carry is_real = 0 (real_count frozen at n) and continue the
        // genuine hash chain over the (final_root, final_root, idx) triple.
        let (acc_out, row) = binding_row(
            final_root, final_root, acc, idx, /* is_real */ false, real_count,
        );
        trace.push(row);
        acc = acc_out;
    }
    let genesis_root = trace[0][COL_OLD_ROOT];
    let chain_digest = trace.last().unwrap()[COL_ACC_OUT];
    let pis = vec![
        genesis_root,
        final_root,
        BabyBear::new(n as u32),
        chain_digest,
    ];
    let digest = pis[3];
    Ok((trace, pis, digest))
}

/// Build one wide binding-trace row and return `(acc_out, row)`.
///
/// `acc_out = hash_4_to_1([acc_in, old_root, new_root, idx])` — the SAME digest the
/// in-circuit constraint forces — and the Poseidon2 aux block is the genuine
/// intermediate-state witness [`poseidon2_permute_expr`] checks round-by-round,
/// seeded from `[acc_in, old_root, new_root, idx, 4, 0..]` (the `hash_4_to_1`
/// state).
pub(crate) fn binding_row(
    old_root: BabyBear,
    new_root: BabyBear,
    acc_in: BabyBear,
    idx: BabyBear,
    is_real: bool,
    real_count: BabyBear,
) -> (BabyBear, Vec<BabyBear>) {
    let acc_out = hash_4_to_1(&[acc_in, old_root, new_root, idx]);

    let mut input_state = [BabyBear::ZERO; POSEIDON2_WIDTH];
    input_state[0] = acc_in;
    input_state[1] = old_root;
    input_state[2] = new_root;
    input_state[3] = idx;
    input_state[4] = BabyBear::new(HASH_ARITY_TAG);
    let aux = poseidon2_permute_aux_witness(input_state);
    debug_assert_eq!(aux.len(), POSEIDON2_PERM_AUX_COLS);
    // The aux block's final state[0] IS the digest (the gadget returns state[0]).
    debug_assert_eq!(aux[POSEIDON2_PERM_AUX_COLS - POSEIDON2_WIDTH], acc_out);

    let mut row = Vec::with_capacity(BINDING_WIDTH);
    row.push(old_root); // COL_OLD_ROOT
    row.push(new_root); // COL_NEW_ROOT
    row.push(acc_in); // COL_ACC_IN
    row.push(acc_out); // COL_ACC_OUT
    row.push(idx); // COL_IDX
    row.push(if is_real {
        BabyBear::ONE
    } else {
        BabyBear::ZERO
    }); // COL_IS_REAL
    row.push(real_count); // COL_REAL_COUNT
    row.extend_from_slice(&aux); // BINDING_AUX0..
    debug_assert_eq!(row.len(), BINDING_WIDTH);
    (acc_out, row)
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
const IR2_INNER_LOG_BLOWUP: usize = 6;
const IR2_INNER_LOG_FINAL_POLY_LEN: usize = 0;
const IR2_INNER_COMMIT_POW_BITS: usize = 0;
const IR2_INNER_QUERY_POW_BITS: usize = 16;

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
pub fn ir2_leaf_wrap_config() -> DreggRecursionConfig {
    // Fixed `IR2_INNER_*` knobs ⇒ identical config on every call; build once per thread and clone
    // on access (Arc-backed, cheap). `thread_local` sidesteps any `Sync` requirement; the cached
    // value is identical to a fresh `create_recursion_config_for_inner_fri(..)` at these constants.
    thread_local! {
        static LEAF_WRAP_CONFIG: DreggRecursionConfig =
            crate::plonky3_recursion_impl::recursive::create_recursion_config_for_inner_fri(
                IR2_INNER_LOG_BLOWUP,
                IR2_INNER_LOG_FINAL_POLY_LEN,
                IR2_INNER_COMMIT_POW_BITS,
                IR2_INNER_QUERY_POW_BITS,
            );
    }
    LEAF_WRAP_CONFIG.with(|c| c.clone())
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
        config,
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
/// `custom_proof_commitment` at IR2 PI slots 46..49 (the Lean `customPiExposure`); calling this
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
                       apt: &[Vec<p3_recursion::Target>]| {
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
        config,
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

    let backend = create_recursion_backend();

    // The expose hook: the main instance (instance 0) carries the descriptor PIs. Build the two
    // 8-felt anchor blocks (genuine wide tail, or replicated single felt for a narrow leg), the
    // per-turn digest seed over them, and expose the 8-wide segment.
    let expose = move |cb: &mut p3_circuit::CircuitBuilder<RecursionChallenge>,
                       apt: &[Vec<p3_recursion::Target>]| {
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
        let mut seg = Vec::with_capacity(SEG_WIDTH);
        seg.extend_from_slice(&first_old8);
        seg.extend_from_slice(&last_new8);
        seg.push(count);
        seg.extend_from_slice(&acc);
        debug_assert_eq!(seg.len(), SEG_WIDTH);
        cb.expose_as_public_output(&seg);
    };

    build_and_prove_next_layer_with_expose::<
        DreggRecursionConfig,
        dregg_circuit::descriptor_ir2::Ir2Air,
        _,
        D,
    >(
        &input,
        config,
        &backend,
        &ProveNextLayerParams::default(),
        Some(&expose),
    )
    .map_err(|e| format!("rotated native-batch segment leaf-wrap failed: {e:?}"))
}

/// **THE DUAL-EXPOSE CUSTOM LEG LEAF (deployed custom-binding half #1).** Wrap one rotated
/// `customVmDescriptor2R24` finalized-turn batch in-circuit exactly like
/// [`prove_descriptor_leaf_rotated_with_segment`] AND expose, through ONE `expose_claim` table,
/// BOTH:
///
///   * the constant-size ordered chain SEGMENT `[first_old8, last_new8, count, acc]` (lanes
///     `[0 .. SEG_WIDTH)`), bound in-circuit to the descriptor's real rotated roots, and
///   * the leg's CLAIMED `custom_proof_commitment` at IR2 PI
///     `[CUSTOM_COMMIT_PI_LO .. CUSTOM_COMMIT_PI_LO+CUSTOM_COMMIT_LEN)` (lanes
///     `[SEG_WIDTH .. SEG_WIDTH+CUSTOM_COMMIT_LEN)`), read from the same FRI-bound
///     `air_public_targets` the segment endpoints come from.
///
/// The commitment lanes are APPENDED AFTER the segment, so a downstream segment consumer that
/// reads only `[0 .. SEG_WIDTH)` (the host segment tooth, the plain `aggregate_tree` combine)
/// sees the identical segment a [`prove_descriptor_leaf_rotated_with_segment`] leaf would expose.
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
///     `[0 .. SEG_WIDTH)`), bound in-circuit to the descriptor's real rotated roots, and
///   * the leg's CLAIMED teeth at IR2 PI `[claim_pi_lo .. claim_pi_lo+claim_len)` (lanes
///     `[SEG_WIDTH .. SEG_WIDTH+claim_len)`), read from the same FRI-bound `air_public_targets`.
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
/// wide rotated-commit anchors), exactly as the custom commitment sits at 46..49 ahead of them —
/// never appended past `n - 2*SEG_ANCHOR_WIDTH`, or the wide-anchor sourcing would read the teeth
/// as the rotated commits.
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

    let backend = create_recursion_backend();

    let expose = move |cb: &mut p3_circuit::CircuitBuilder<RecursionChallenge>,
                       apt: &[Vec<p3_recursion::Target>]| {
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
        let mut claim = Vec::with_capacity(SEG_WIDTH + claim_len);
        claim.extend_from_slice(&first_old8);
        claim.extend_from_slice(&last_new8);
        claim.push(count);
        claim.extend_from_slice(&acc);
        debug_assert_eq!(claim.len(), SEG_WIDTH);
        // -- The CLAIMED teeth (lanes [SEG_WIDTH .. SEG_WIDTH+claim_len)), read from the leaf's
        // own FRI-bound descriptor PIs (not free scalars).
        for k in 0..claim_len {
            claim.push(main[claim_pi_lo + k]);
        }
        debug_assert_eq!(claim.len(), SEG_WIDTH + claim_len);
        cb.expose_as_public_output(&claim);
    };

    build_and_prove_next_layer_with_expose::<
        DreggRecursionConfig,
        dregg_circuit::descriptor_ir2::Ir2Air,
        _,
        D,
    >(
        &input,
        config,
        &backend,
        &ProveNextLayerParams::default(),
        Some(&expose),
    )
    .map_err(|e| format!("rotated dual-expose custom leaf-wrap failed: {e:?}"))
}

// ============================================================================
// The whole-chain IVC artifact (K-fold).
// ============================================================================

/// The Gold whole-chain artifact: ONE succinct recursive proof attesting that
/// **all** K finalized-turn leaves AND the sequential chain-binding leaf
/// verified in-circuit. The verifier checks only the root; cost is independent
/// of K.
pub struct WholeChainProof {
    /// The single root batch-STARK proof (the whole tree folded to one).
    pub root: RecursionOutput<DreggRecursionConfig>,
    /// The chain-binding uni-STARK (the SAME statement the fold wraps
    /// in-circuit as the binding leaf), carried so the verifier can check the
    /// claimed publics below AGAINST A PROOF instead of trusting bare fields:
    /// Fiat–Shamir binds `[genesis_root, final_root, num_turns, chain_digest]`
    /// into this proof, so relabeling any of them is refused at verify time.
    pub binding_proof: RecursionCompatibleProof,
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
        recursion_vk_fingerprint(&self.root.0)
    }

    /// Serialize the VERIFY-SUFFICIENT subset of this proof into a versioned byte
    /// envelope ([`WholeChainProofBytes`]) that round-trips over a wire.
    ///
    /// A whole [`WholeChainProof`] is NOT byte-encodable: its `root.1`
    /// (`Rc<CircuitProverData>`) is prover-chaining data with no serde and no
    /// verifier use. The envelope therefore carries only what
    /// [`verify_turn_chain_recursive_from_parts`] reads — the root
    /// [`BatchStarkProof`] (`root.0`), the chain-binding `Proof`, and the four
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
/// artifact (`docs/PG-DREGG.md` §10.2, `WEB-FORWARD.md` §7).
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
    /// Postcard bytes of `WholeChainProof.binding_proof` — the chain-binding
    /// uni-STARK `Proof`. Tooth 2 verifies the four publics AS its public inputs.
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
    /// The number of finalized turns folded.
    pub num_turns: u64,
}

/// The on-the-wire version tag of [`WholeChainProofBytes`]. Bumped on any layout
/// change so an old producer's bytes are refused (fail-closed) not misread.
///
/// **v2** (codex re-review #3): `chain_digest` widened from one `u32` to
/// `[u32; SEG_DIGEST_WIDTH]` — the multi-felt Poseidon2 commitment.
/// **v3** (FAITHFUL-FLOOR lift): the state endpoints `genesis_root`/`final_root` widened from one
/// `u32` to `[u32; SEG_ANCHOR_WIDTH]` (8-felt anchors), and `SEG_DIGEST_WIDTH` widened 4→8.
pub const WHOLE_CHAIN_PROOF_ENVELOPE_V1: u16 = 3;

impl WholeChainProofBytes {
    /// Project a [`WholeChainProof`] to its verify-sufficient byte envelope.
    pub fn from_proof(proof: &WholeChainProof) -> Self {
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
            num_turns: proof.num_turns as u64,
        }
    }

    /// Encode to wire bytes (postcard). Infallible on a well-formed value.
    pub fn to_postcard(&self) -> Vec<u8> {
        postcard::to_allocvec(self).expect("WholeChainProofBytes postcard-encodes")
    }

    /// Decode from wire bytes. Fail-closed: empty input, a malformed body, a wrong
    /// version, or an empty proof component is an `Err` — never a silently-accepted
    /// half-envelope.
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
        Ok(env)
    }

    /// Decode the two opaque blobs into the concrete recursion proof types.
    /// Fail-closed on a blob that does not deserialize into its target type.
    fn decode_parts(
        &self,
    ) -> Result<
        (
            p3_circuit_prover::BatchStarkProof<DreggRecursionConfig>,
            RecursionCompatibleProof,
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
        let binding_proof: RecursionCompatibleProof = postcard::from_bytes(&self.binding_proof)
            .map_err(|e| TurnChainError::EnvelopeDecode {
                reason: format!("binding Proof does not decode: {e}"),
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
    verify_turn_chain_recursive_from_parts(
        &root_proof,
        &binding_proof,
        core::array::from_fn(|i| BabyBear::new(env.genesis_root[i])),
        core::array::from_fn(|i| BabyBear::new(env.final_root[i])),
        core::array::from_fn(|i| BabyBear::new(env.chain_digest[i])),
        env.num_turns as usize,
        expected_vk,
    )
}

/// **Verify from the two OPAQUE proof-component blobs + publics** — the seam a
/// downstream that cannot name the p3 proof types (e.g. `pg-dregg`, which does not
/// depend on `p3-circuit-prover`) plugs into.
///
/// `root_blob` is the postcard of the root [`BatchStarkProof`] (`WholeChainProof.
/// root.0`) and `binding_blob` the postcard of the chain-binding `Proof`
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
    let binding_proof: RecursionCompatibleProof =
        postcard::from_bytes(binding_blob).map_err(|e| TurnChainError::EnvelopeDecode {
            reason: format!("binding Proof blob does not decode: {e}"),
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
/// must be the next turn's `old_root` — the temporal binding the chain leaf
/// enforces both host-side and in-circuit.
///
/// Steps:
///   1. host admission: every turn's production descriptor proof verifies
///      SELECTOR-BOUND through the Lean descriptor verifier
///      ([`verify_descriptor_participant`]) — this also determines each turn's
///      descriptor selector;
///   2. host-side: >= 2 turns, sequential continuity;
///   3. prove the chain-binding leaf (rejects a broken order in-circuit too);
///   4. re-prove each turn's REAL descriptor AIR over its OWN execution trace
///      as a recursion-compatible uni-STARK ([`prove_descriptor_leaf`]);
///   5. wrap every leaf in its own IN-CIRCUIT verifier layer (uni->batch) —
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
/// uni-STARK `EffectVmDescriptorAir` wrap. The whole tree (binding leaf + aggregation) runs at
/// the ONE wrap config, exactly as the aggregation gate
/// (`rotation_batchstark_leaf_smoke::two_rotated_leaves_aggregate_at_wrap_config`) proves it
/// folds. Every turn MUST carry a rotated leg (`participant.rotated == Some`); a missing leg
/// fails closed.
///
/// The temporal binding is read from the ROTATED commitments (PI 34/35 — the rotated trace's
/// before/after `state_commit` carriers), so the chain continuity tooth
/// (`prev.new_root == next.old_root`) binds the rotated v9 commitment.
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
    // GROUND THE VERIFIER LEG against the Lean-emitted welded registry. The WIDE single-domain weld
    // (`-umem-wide-welded-staged`, NOT the multidomain twin) has a committed, Lean-grounded descriptor
    // set ([`WIDE_UMEM_WELD_REGISTRY_TSV`], the verified `EffectVmEmitUMemWeldWide.weldedWideRegistry`).
    // For such a leg we REQUIRE the carried descriptor to be byte-equal to a registry member and verify
    // the proof against THAT member — so a producer cannot carry an off-registry welded descriptor (the
    // ungrounded gap the missing verifier leg left). The narrow / wide-multidomain weld forms keep
    // their carried-descriptor admission (separate staged forms, out of this registry's scope).
    let is_wide_single = leg.descriptor.name.ends_with(WIDE_UMEM_WELD_SUFFIX)
        && !leg
            .descriptor
            .name
            .ends_with(WIDE_UMEM_MULTIDOMAIN_WELD_SUFFIX);
    let verify_desc = if is_wide_single {
        use dregg_circuit::descriptor_ir2::parse_vm_descriptor2;
        use dregg_circuit::effect_vm_descriptors::WIDE_UMEM_WELD_REGISTRY_TSV;
        let grounded = WIDE_UMEM_WELD_REGISTRY_TSV.lines().find_map(|line| {
            let json = line.splitn(3, '\t').nth(2)?;
            let desc = parse_vm_descriptor2(json).ok()?;
            if desc == leg.descriptor {
                Some(desc)
            } else {
                None
            }
        });
        match grounded {
            Some(d) => d,
            None => {
                return Err(TurnChainError::TurnProofInvalid {
                    index,
                    reason: format!(
                        "WIDE welded leg descriptor '{}' is NOT a member of the Lean-emitted \
                         WIDE_UMEM_WELD_REGISTRY (off-registry welded descriptor refused)",
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
    let backend = create_recursion_backend();
    let params = ProveNextLayerParams::default();

    // The carried binding proof (defense-in-depth host witness; NOT folded into the root — the
    // segment tooth over the root's exposed segment binds the claim).
    let (binding_inner, _binding_pis) = prove_chain_binding_leaf_rotated(&refs)?;

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
    let root = aggregate_tree(batch_leaves, &config, &backend, &params)?;

    Ok(WholeChainProof {
        root,
        binding_proof: binding_inner,
        genesis_root,
        final_root,
        chain_digest,
        num_turns: turns.len(),
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

    let backend = create_recursion_backend();

    let expose = move |cb: &mut p3_circuit::CircuitBuilder<RecursionChallenge>,
                       apt: &[Vec<p3_recursion::Target>]| {
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
        debug_assert_eq!(seg.len(), WIDE_SEG_WIDTH);
        cb.expose_as_public_output(&seg);
    };

    build_and_prove_next_layer_with_expose::<
        DreggRecursionConfig,
        dregg_circuit::descriptor_ir2::Ir2Air,
        _,
        D,
    >(
        &input,
        config,
        &backend,
        &ProveNextLayerParams::default(),
        Some(&expose),
    )
    .map_err(|e| format!("rotated native-batch WIDE segment leaf-wrap failed: {e:?}"))
}

/// Fold a vector of WIDE-segment-carrying batch-STARK proofs to ONE via 2-to-1 aggregation
/// layers, combining the WIDE segments in-circuit at each node (8-felt continuity + count
/// additivity + ordered-digest fold) — the 8-felt twin of [`aggregate_tree`].
fn aggregate_tree_wide(
    mut proofs: Vec<RecursionOutput<DreggRecursionConfig>>,
    config: &DreggRecursionConfig,
    backend: &p3_recursion::FriRecursionBackendForExt<D, 16, 8, p3_recursion::ops::Poseidon2Config>,
    params: &ProveNextLayerParams,
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

            let left = proofs[i].into_recursion_input::<BatchOnly>();
            let right = proofs[i + 1].into_recursion_input::<BatchOnly>();

            let expose = move |cb: &mut p3_circuit::CircuitBuilder<RecursionChallenge>,
                               left_apt: &[Vec<p3_recursion::Target>],
                               right_apt: &[Vec<p3_recursion::Target>]| {
                let l = left_apt
                    .get(left_idx)
                    .expect("left wide segment instance present");
                let r = right_apt
                    .get(right_idx)
                    .expect("right wide segment instance present");
                debug_assert!(l.len() >= WIDE_SEG_WIDTH && r.len() >= WIDE_SEG_WIDTH);

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
                let mut parent = Vec::with_capacity(WIDE_SEG_WIDTH);
                parent.extend_from_slice(&l[WSEG_FIRST_OLD..WSEG_FIRST_OLD + WIDE_ANCHOR_WIDTH]);
                parent.extend_from_slice(&r[WSEG_LAST_NEW..WSEG_LAST_NEW + WIDE_ANCHOR_WIDTH]);
                parent.push(count);
                parent.extend_from_slice(&acc);
                debug_assert_eq!(parent.len(), WIDE_SEG_WIDTH);
                cb.expose_as_public_output(&parent);
            };

            let out = build_and_prove_aggregation_layer_with_expose::<
                DreggRecursionConfig,
                BatchOnly,
                BatchOnly,
                _,
                D,
            >(&left, &right, config, backend, params, None, Some(&expose))
            .map_err(|e| TurnChainError::RecursionFailed {
                reason: format!("wide aggregation layer failed: {e:?}"),
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
/// There is no carried binding leaf (the single-felt `TurnChainBindingAir` binds PI 34/35,
/// which the wide form retires to zero) — the wide segment tooth over the root's exposed
/// segment is the sole binding, exactly as the codex ordered-segment-accumulator close intends.
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
        recursion_vk_fingerprint(&self.root.0)
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
    let root = aggregate_tree_wide(batch_leaves, &config, &backend, &params)?;

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
///   2. **The root** — the single root batch-STARK proof verifies under [`ir2_leaf_wrap_config`].
///   3. **The WIDE segment tooth** — the root's exposed ordered WIDE segment
///      `[first_old8, last_new8, count, acc]` (built BY CONSTRUCTION from the real wide
///      descriptor leaves and combined up the tree with 8-felt continuity) must equal the carried
///      `[genesis_root8, final_root8, num_turns, chain_digest]`. A root that executed history A
///      cannot expose B's 8-felt endpoints, so a B-claim against an A-execution is refused.
pub fn verify_wide_turn_chain_recursive(
    proof: &WideWholeChainProof,
    expected_vk: &RecursionVk,
) -> Result<(), TurnChainError> {
    // (1) VK pin.
    let found = recursion_vk_fingerprint(&proof.root.0);
    if found != *expected_vk {
        return Err(TurnChainError::VkFingerprintMismatch {
            expected: expected_vk.to_hex(),
            found: found.to_hex(),
        });
    }

    // (2) the root (at the rotated leaf-wrap config — the SAME FRI engine the whole wide tree
    //     runs at).
    verify_recursive_batch_proof_with_config(&proof.root.0, &ir2_leaf_wrap_config())
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
/// PI 47..54). REGEN-RIDER: the committed `WIDE_REGISTRY_STAGED_TSV` row still carries the
/// pre-pin shape; the fold arm admits a leg only when its descriptor actually carries these
/// pins ([`carrier_claim_pins_admitted`]), so until the big-bang descriptor regen lands the
/// arm stays fail-closed on deployed legs.
pub const FACTORY_CHILD_VK_PI_LO: usize = 47;
/// The hatchery leg's `contract_hash8` claim PI base — the SECOND octet cohort on the same
/// `factoryV3Carriers` descriptor (AFTER-block limbs `B_CONTRACT_HASH_OCTET..+8`, PI 55..62;
/// the hatchery carrier rides factory's `CreateCellFromFactory` leg). Same regen-rider note.
pub const HATCHERY_CONTRACT_HASH_PI_LO: usize = 55;
/// The sovereign leg's `KEY_COMMIT` teeth claim PI base — **NATIVE**: the committed wide
/// registry row (`CarrierComposed.makeSovereignV3DeployedWide`, the v12 big-bang regen) pins
/// the 4 teeth columns (113..=116) at PI 58..61 (record-pin8 54 + the 4 dsl rc, THEN the
/// teeth, ahead of the 16 wide anchors 62..77) and welds them in-AIR to the committed
/// `B_PUBKEY8` octet via the KEY_COMMIT chip gate (Lean keystone
/// `makeSovereignV3DeployedWide_publishes_key_commit`). The fold arm admits only a leg whose
/// descriptor genuinely pins these slots, so a mismatched convention fails closed.
pub const SOVEREIGN_KEY_COMMIT_PI_LO: usize = 58;
/// The membership leg's `(sender_leaf, authorized_root)` claim PI base — **NATIVE**: the
/// committed wide transfer row (`CarrierComposed.transferV3MembershipWide`, the v12 big-bang
/// regen) pins the two teeth columns (past the carriers, 1771..1772) at PI 50..51 (the bare
/// rotated 46 + the 4 dsl rc, THEN the teeth, ahead of the anchors 52..67 — Lean keystone
/// `transferV3MembershipWide_publishes_teeth`). PI-EXPOSURE leg only (the FOLD edge binds;
/// the in-AIR welds stay the named `MembershipAuthRootEdge` seams). Same fail-closed
/// admission discipline.
pub const MEMBERSHIP_CLAIM_PI_LO: usize = 50;
/// The bridge leg's felt mint-hash claim PI — **NATIVE**: the committed mint row
/// (`mintV3BridgeHash`, the STEP-3/4 regen) pins the mint row's `param0` (`prmCol 0` — since
/// the STEP-1 executor re-align, the FELT-domain `note_spend_mint_hash_felt` over the six
/// compressed felts `apply_bridge_mint` enforces the note-spend STARK against) at PI 46 on
/// the FIRST row (Lean keystone `withMintHashPin_publishes`; rc rides 47..50, wide anchors
/// 51..66). ONE lane binds the whole spend tuple: the identity is the leaf's in-AIR
/// `hash_fact` chain over its own PI-pinned `(nullifier, root, value_lo, asset, dest_fed,
/// value_hi)`. Same fail-closed admission discipline.
pub const BRIDGE_MINT_HASH_PI: usize = 46;
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
pub const DECO_PAYMENT_HASH_PI: usize = 46;
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
pub fn dsl_rc_claim_pi_lo(
    desc: &dregg_circuit::descriptor_ir2::EffectVmDescriptor2,
) -> Result<usize, String> {
    use dregg_circuit::descriptor_ir2::VmConstraint2;
    use dregg_circuit::effect_vm::trace_rotated::{C_DFA_RC_OFF, CAVEAT_BASE};
    use dregg_circuit::lean_descriptor_air::{VmConstraint, VmRow};

    let rc_col0 = CAVEAT_BASE + C_DFA_RC_OFF;
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

/// The rotated fold core: like [`prove_chain_core`] but mints rotated native-batch leaves and
/// runs the whole tree at [`ir2_leaf_wrap_config`].
fn prove_chain_core_rotated(
    turns: &[&FinalizedTurn],
    selectors: &[usize],
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

    // The ONE FRI engine the whole rotated tree runs at (inner proof + leaf-wrap +
    // aggregation), so the in-circuit FRI verifier params match every child's FRI engine.
    let config = ir2_leaf_wrap_config();
    let backend = create_recursion_backend();
    let params = ProveNextLayerParams::default();

    // The carried binding proof is RETAINED for byte-envelope/struct API compatibility and as a
    // host-side defense-in-depth witness of the ordered chain — but it is NO LONGER a soundness
    // dependency of `verify_turn_chain_recursive` (see its tooth list: the segment tooth (4) over
    // the root's exposed segment is what binds the claim now). It is NOT folded into the root.
    let (binding_inner, _binding_pis) = prove_chain_binding_leaf_rotated(turns)?;

    let mut batch_leaves: Vec<RecursionOutput<DreggRecursionConfig>> =
        Vec::with_capacity(turns.len());

    // One rotated descriptor leaf per finalized turn, EACH carrying its ordered segment
    // (first_old/last_new bound to the descriptor's real roots, count=1, acc=H(old,new)).
    //
    // THE CARRIER WITNESS SOCKET (Step-2 of the uniform carrier build): the per-turn fold branch
    // is picked by matching the leg's `carrier_witness`.
    //
    // CUSTOM-BINDING DEPLOYED WIRE (the ONE deployed carrier arm): a turn whose leg carries a
    // `CarrierWitness::Custom` bundle (a `Custom`-effect turn, `customVmDescriptor2R24`) does NOT
    // get the plain segment leaf. Instead it gets a DUAL-EXPOSE leaf (segment ++ claimed
    // `custom_proof_commitment` PI 46..49) folded against the RE-PROVEN custom sub-proof leaf
    // through `prove_custom_binding_node_segmented` — the binding `connect`s the leg's claimed
    // commitment to the sub-proof's genuine in-circuit commitment IN the recursion tree (so a
    // forged claim with no backing sub-proof is UNSAT) and re-exposes the SAME segment, so the
    // node folds into `aggregate_tree` like any segment leaf. This makes the custom binding REAL
    // for a pure light client (the premise of `CustomBindingFromFold.custom_binding_from_fold` is
    // now TRUE on the deployed path).
    //
    // THE CARRIER ARMS: ALL SEVEN are FOLD-WIRED — custom + the four v12 carriers (factory /
    // hatchery / sovereign / membership) + dsl + bridge. Each mints a dual-expose leaf at its
    // claim PI slots (gated by `carrier_claim_pins_admitted`, which REFUSES a leg whose
    // descriptor does not carry the STEP-3 claim pins — the big-bang regen tie) and binds the
    // re-proven carrier leaf under its segment-preserving binding node. A turn that WANTS the
    // re-exec rung carries `carrier_witness: None` (the sanctioned path, identical to today's
    // non-carrier turns). There is deliberately NO wildcard arm, so a new variant is a compile
    // error here (the wave must decide its fold branch).
    for (i, t) in turns.iter().enumerate() {
        let leg = &t.participant.rotated;
        let wrapped = match &leg.carrier_witness {
            Some(CarrierWitness::Custom(bundle)) => {
                let dual = prove_descriptor_leaf_dual_expose(
                    &leg.descriptor,
                    &leg.proof,
                    &leg.public_inputs,
                    &config,
                )
                .map_err(|reason| TurnChainError::TurnProofInvalid { index: i, reason })?;
                let custom_leaf = crate::custom_leaf_adapter::prove_custom_leaf_with_commitment(
                    &bundle.program,
                    &bundle.witness_values,
                    bundle.num_rows,
                    &bundle.public_inputs,
                    &config,
                )
                .map_err(|reason| TurnChainError::TurnProofInvalid {
                    index: i,
                    reason: format!("custom sub-proof leaf mint failed: {reason}"),
                })?;
                crate::joint_turn_recursive::prove_custom_binding_node_segmented(
                    &dual,
                    &custom_leaf,
                    &config,
                )
                .map_err(|e| TurnChainError::TurnProofInvalid {
                    index: i,
                    reason: format!("segmented custom-binding node failed: {e:?}"),
                })?
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
                    &config,
                    BRIDGE_MINT_HASH_PI,
                    BRIDGE_MINT_HASH_CLAIM_LEN,
                )
                .map_err(|reason| TurnChainError::TurnProofInvalid { index: i, reason })?;
                let backing = crate::note_spend_leaf_adapter::prove_note_spend_leaf_with_claim(
                    &bundle.note_spend,
                    &bundle.public_inputs,
                    &config,
                )
                .map_err(|reason| TurnChainError::TurnProofInvalid {
                    index: i,
                    reason: format!("bridge note-spend backing leaf mint failed: {reason}"),
                })?;
                crate::note_spend_leaf_adapter::prove_note_spend_mint_binding_node_segmented(
                    &dual, &backing, &config,
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
                    &config,
                    DECO_PAYMENT_HASH_PI,
                    DECO_PAYMENT_HASH_CLAIM_LEN,
                )
                .map_err(|reason| TurnChainError::TurnProofInvalid { index: i, reason })?;
                let backing = crate::deco_leaf_adapter::prove_deco_leaf_with_claim(
                    &bundle.witness,
                    &bundle.public_inputs,
                    &config,
                )
                .map_err(|reason| TurnChainError::TurnProofInvalid {
                    index: i,
                    reason: format!("deco payment backing leaf mint failed: {reason}"),
                })?;
                crate::deco_leaf_adapter::prove_deco_payment_binding_node_segmented(
                    &dual, &backing, &config,
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
                use dregg_circuit::effect_vm::trace_rotated::{
                    C_DFA_RC_OFF, CAVEAT_BASE, DFA_RC_LEN,
                };
                use dregg_circuit::lean_descriptor_air::VmRow;
                let rc_lo = dsl_rc_claim_pi_lo(&leg.descriptor)
                    .map_err(|reason| TurnChainError::TurnProofInvalid { index: i, reason })?;
                carrier_claim_pins_admitted(
                    &leg.descriptor,
                    &leg.public_inputs,
                    rc_lo,
                    DFA_RC_LEN,
                    "dsl",
                    Some((CAVEAT_BASE + C_DFA_RC_OFF, VmRow::Last)),
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
                    &config,
                    rc_lo,
                    DFA_RC_LEN,
                )
                .map_err(|reason| TurnChainError::TurnProofInvalid { index: i, reason })?;
                let dsl_leaf = crate::dsl_leaf_adapter::prove_dsl_leaf_with_commitment(
                    &bundle.program,
                    &bundle.witness_values,
                    bundle.num_rows,
                    &bundle.public_inputs,
                    &config,
                )
                .map_err(|reason| TurnChainError::TurnProofInvalid {
                    index: i,
                    reason: format!("dsl sub-proof leaf mint failed: {reason}"),
                })?;
                crate::dsl_leaf_adapter::prove_dsl_binding_node_segmented(&dual, &dsl_leaf, &config)
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
                    &config,
                    FACTORY_CHILD_VK_PI_LO,
                    crate::factory_leaf_adapter::FACTORY_CHILD_VK_CLAIM_LEN,
                )
                .map_err(|reason| TurnChainError::TurnProofInvalid { index: i, reason })?;
                let backing = crate::factory_leaf_adapter::prove_factory_leaf_with_child_vk_claim(
                    &bundle.backing,
                    &bundle.public_inputs,
                    &config,
                )
                .map_err(|reason| TurnChainError::TurnProofInvalid {
                    index: i,
                    reason: format!("factory backing leaf mint failed: {reason}"),
                })?;
                crate::factory_leaf_adapter::prove_factory_binding_node_segmented(
                    &dual, &backing, &config,
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
                    &config,
                    HATCHERY_CONTRACT_HASH_PI_LO,
                    crate::hatchery_leaf_adapter::HATCHERY_CONTRACT_CLAIM_LEN,
                )
                .map_err(|reason| TurnChainError::TurnProofInvalid { index: i, reason })?;
                let attestation =
                    crate::hatchery_leaf_adapter::prove_hatchery_leaf_with_contract_claim(
                        &bundle.attestation,
                        &bundle.public_inputs,
                        &config,
                    )
                    .map_err(|reason| TurnChainError::TurnProofInvalid {
                        index: i,
                        reason: format!("hatchery attestation leaf mint failed: {reason}"),
                    })?;
                crate::hatchery_leaf_adapter::prove_hatchery_binding_node_segmented(
                    &dual,
                    &attestation,
                    &config,
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
                    &config,
                    SOVEREIGN_KEY_COMMIT_PI_LO,
                    crate::sovereign_leaf_adapter::SOVEREIGN_KEY_CLAIM_LEN,
                )
                .map_err(|reason| TurnChainError::TurnProofInvalid { index: i, reason })?;
                let authority = crate::sovereign_leaf_adapter::prove_sovereign_leaf_with_key_claim(
                    &bundle.authority,
                    &bundle.public_inputs,
                    &config,
                )
                .map_err(|reason| TurnChainError::TurnProofInvalid {
                    index: i,
                    reason: format!("sovereign authority leaf mint failed: {reason}"),
                })?;
                crate::joint_turn_recursive::prove_sovereign_binding_node_segmented(
                    &dual, &authority, &config,
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
                    &config,
                    MEMBERSHIP_CLAIM_PI_LO,
                    crate::membership_leaf_adapter::MEMBERSHIP_CLAIM_LEN,
                )
                .map_err(|reason| TurnChainError::TurnProofInvalid { index: i, reason })?;
                let membership = crate::membership_leaf_adapter::prove_membership_leaf_with_claim(
                    &bundle.membership,
                    &bundle.public_inputs,
                    &config,
                )
                .map_err(|reason| TurnChainError::TurnProofInvalid {
                    index: i,
                    reason: format!("membership leaf mint failed: {reason}"),
                })?;
                crate::membership_leaf_adapter::prove_membership_binding_node_segmented(
                    &dual,
                    &membership,
                    &config,
                )
                .map_err(|e| TurnChainError::TurnProofInvalid {
                    index: i,
                    reason: format!("segmented membership-binding node failed: {e:?}"),
                })?
            }
            None => prove_descriptor_leaf_rotated_with_segment(
                &leg.descriptor,
                &leg.proof,
                &leg.public_inputs,
                &config,
            )
            .map_err(|reason| TurnChainError::TurnProofInvalid { index: i, reason })?,
        };
        batch_leaves.push(wrapped);
    }

    // Aggregate the segment-carrying descriptor leaves to ONE root, COMBINING the segments
    // in-circuit at each node (continuity + count + ordered-digest fold). The root's exposed
    // segment is the whole-chain `[genesis_root, final_root, num_turns, chain_digest]`.
    //
    // DEFAULT = the serial `aggregate_tree` (unchanged proving path). When `DREGG_MERGE_WORKERS` is
    // set, the PARALLEL scan-state driver folds the SAME DAG through the merge-pool (independent
    // merge nodes farmed to N workers) — byte-identical root, parallel path. This is the operator
    // throughput knob (aggregation was the serial cap; the merge is the farm-able unit).
    let root = if crate::merge_pool::parallel_aggregation_enabled() {
        crate::merge_pool::aggregate_tree_scan_state_configured(batch_leaves)?
    } else {
        aggregate_tree(batch_leaves, &config, &backend, &params)?
    };

    Ok(WholeChainProof {
        root,
        binding_proof: binding_inner,
        genesis_root,
        final_root,
        chain_digest,
        num_turns: turns.len(),
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

/// Build the chain-binding leaf reading the ROTATED chain roots (PI 34/35), at the wrap config.
///
/// **Bucket-F fix:** the binding-leaf inner proof MUST be minted at [`ir2_leaf_wrap_config`]
/// (log_blowup 6), the SAME FRI engine the whole rotated tree runs at — it is wrapped and
/// aggregated with the rotated descriptor leaves at that config, so proving it at the default
/// `create_recursion_config` (log_blowup 3) and then wrapping at the wrap config raises
/// `InvalidProofShape("Fewer siblings in proof than op_ids provided")` in-circuit.
fn prove_chain_binding_leaf_rotated(
    turns: &[&FinalizedTurn],
) -> Result<(RecursionCompatibleProof, Vec<BabyBear>), TurnChainError> {
    use crate::plonky3_recursion_impl::recursive::{
        prove_inner_for_air_with_config, verify_inner_for_air_with_config,
    };
    let (trace, pis, _digest) = generate_chain_trace_rotated(turns)?;
    let matrix = trace_to_matrix(&trace);
    let air = TurnChainBindingAir;
    let wrap_config = ir2_leaf_wrap_config();
    let proof = prove_inner_for_air_with_config(&air, matrix, &pis, &wrap_config);
    verify_inner_for_air_with_config(&air, &proof, &pis, &wrap_config)
        .map_err(|reason| TurnChainError::RecursionFailed { reason })?;
    Ok((proof, pis))
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
pub(crate) fn segment_combine_expose(
    cb: &mut p3_circuit::CircuitBuilder<RecursionChallenge>,
    left_apt: &[Vec<p3_recursion::Target>],
    right_apt: &[Vec<p3_recursion::Target>],
    left_idx: usize,
    right_idx: usize,
) {
    let l = left_apt
        .get(left_idx)
        .expect("left segment instance present");
    let r = right_apt
        .get(right_idx)
        .expect("right segment instance present");
    debug_assert!(l.len() >= SEG_WIDTH && r.len() >= SEG_WIDTH);

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
    let mut parent = Vec::with_capacity(SEG_WIDTH);
    parent.extend_from_slice(&l[SEG_FIRST_OLD..SEG_FIRST_OLD + SEG_ANCHOR_WIDTH]);
    parent.extend_from_slice(&r[SEG_LAST_NEW..SEG_LAST_NEW + SEG_ANCHOR_WIDTH]);
    parent.push(count);
    parent.extend_from_slice(&acc);
    debug_assert_eq!(parent.len(), SEG_WIDTH);
    cb.expose_as_public_output(&parent);
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
    backend: &p3_recursion::FriRecursionBackendForExt<D, 16, 8, p3_recursion::ops::Poseidon2Config>,
    params: &ProveNextLayerParams,
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

    let left_input = batch_to_pinned_input(left, left_commit);
    let right_input = batch_to_pinned_input(right, right_commit);

    let expose = move |cb: &mut p3_circuit::CircuitBuilder<RecursionChallenge>,
                       left_apt: &[Vec<p3_recursion::Target>],
                       right_apt: &[Vec<p3_recursion::Target>]| {
        segment_combine_expose(cb, left_apt, right_apt, left_idx, right_idx);
    };

    build_and_prove_aggregation_layer_with_expose::<
        DreggRecursionConfig,
        BatchOnly,
        BatchOnly,
        _,
        D,
    >(
        &left_input,
        &right_input,
        config,
        backend,
        params,
        None,
        Some(&expose),
    )
    .map_err(|e| TurnChainError::RecursionFailed {
        reason: format!("aggregation layer failed: {e:?}"),
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
    verify_turn_chain_recursive_from_parts(
        &proof.root.0,
        &proof.binding_proof,
        proof.genesis_root,
        proof.final_root,
        proof.chain_digest,
        proof.num_turns,
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
    binding_proof: &RecursionCompatibleProof,
    genesis_root: [BabyBear; SEG_ANCHOR_WIDTH],
    final_root: [BabyBear; SEG_ANCHOR_WIDTH],
    chain_digest: [BabyBear; SEG_DIGEST_WIDTH],
    num_turns: usize,
    expected_vk: &RecursionVk,
) -> Result<(), TurnChainError> {
    // The carried binding proof is NO LONGER a soundness dependency (the SEGMENT tooth below
    // binds the claim to the real descriptor leaves). It is retained in the artifact for byte
    // API compatibility and host-side defense-in-depth only; deliberately not re-verified here.
    let _ = binding_proof;

    // (1) VK pin.
    let found = recursion_vk_fingerprint(root_proof);
    if found != *expected_vk {
        return Err(TurnChainError::VkFingerprintMismatch {
            expected: expected_vk.to_hex(),
            found: found.to_hex(),
        });
    }

    // (2) The root. The root batch proof is produced by `aggregate_tree` at the rotated
    // leaf-wrap config (`ir2_leaf_wrap_config`, log_blowup 6 / 19 queries — the SAME FRI engine
    // the whole rotated tree runs at), NOT the default `create_recursion_config` (log_blowup 3 /
    // 38 queries). It MUST be verified under that same config, else FRI reconstruction expects
    // the wrong query count (`QueryProofCountMismatch { expected: 38, got: 19 }`).
    verify_recursive_batch_proof_with_config(root_proof, &ir2_leaf_wrap_config())
        .map_err(|reason| TurnChainError::RecursionFailed { reason })?;

    // (3) THE SEGMENT TOOTH (the close of the IVC mixed-root hole). The root proof carries an
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
    let mut expected = Vec::with_capacity(SEG_WIDTH);
    expected.extend_from_slice(&genesis_root);
    expected.extend_from_slice(&final_root);
    expected.push(BabyBear::new(num_turns as u32));
    expected.extend_from_slice(&chain_digest);
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
/// the temporal binding (`prev.new_root == next.old_root`) enforced by the
/// chain-binding leaf over the 2-turn window. Iterating it left-to-right over a
/// finalized stream reproduces [`prove_turn_chain_recursive`]'s result.
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
/// turn leaf + a 2-row chain-binding leaf binding `running.final_root ->
/// new_root`, and (c) re-aggregates `running ∘ {turn, binding}` into the new
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
// participant through `dregg_turn::rotation_witness::mint_rotated_participant_leg`
// (the circuit lib cannot — it has no `dregg-cell` / `dregg-turn` dependency, the cycle).
