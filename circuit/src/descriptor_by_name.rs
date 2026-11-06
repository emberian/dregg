//! **`descriptor_by_name`** — the descriptor-world analog of
//! [`crate::dsl::descriptors::circuit_for_air_name`] (Foundation 1).
//!
//! The StarkProof→descriptor-prover migration replaces the runtime AIR-name → `DslCircuit`
//! dispatch (`circuit_for_air_name`, a match over v1 `CircuitDescriptor` circuits) with a
//! dispatch into the IR-v2 descriptor world: each predicate kind's proof is re-expressed as an
//! [`EffectVmDescriptor2`] proven through [`crate::descriptor_ir2::prove_vm_descriptor2`] and
//! checked by [`crate::descriptor_ir2::verify_vm_descriptor2`]. This module is the production
//! dispatch table for that world.
//!
//! ## The #1 migration danger this closes
//!
//! A wrong or MISSING dispatch arm is a SILENT verify failure: the consumer that cannot find a
//! descriptor for a predicate must NEVER fall through to "accept". So [`descriptor_by_name`]
//! returns [`Option::None`] on a miss — never a stand-in descriptor, never a silent accept — and
//! every mapped name is covered by the round-trip test below (name → descriptor → decode →
//! well-formedness; and, for the membership family, real prove → verify).
//!
//! ## The predicate-kind → descriptor map (ground-truthed from the migration scout)
//!
//! | [`PredicateKind`] | descriptor(s) ([`descriptor_names_for_kind`])                          |
//! |-------------------|------------------------------------------------------------------------|
//! | `Dfa`             | `dfa-routing-toggle-2state::poseidon2-v1` (DfaRouting)                  |
//! | `Temporal`        | `dregg-temporal-predicate-gte::dsl-v1` (TemporalPredicate)             |
//! | `MerkleMembership`| `merkle-membership-depth2-4ary::poseidon2-v1` + the depth-GENERAL builder |
//! | `NonMembership`   | `dregg-membership-adjacency-wide::node8-v1` + `quantified-absence-…`    |
//! | `BlindedSet`      | `dregg-accumulator-nonrev-emit-v2`                                      |
//! | `BridgePredicate` | `dregg-predicate-arith-ge::threshold-v1` (+ the le/gt/lt/neq/inrange siblings) |
//! | `Custom`          | `dregg-effectvm-custom-v1` (customVmDescriptor2)                        |
//! | `PedersenEquality`| NONE — off-STARK Schnorr, no descriptor (returns `&[]` / `None`)        |
//!
//! ## Where the descriptors come from (byte-pinned)
//!
//! Each predicate descriptor is emitted from Lean (`metatheory/Dregg2/Circuit/Emit/*Emit.lean`)
//! and byte-pinned there by an `emitVmJson2` `#guard`. The consts below `include_str!` the
//! checked-in `circuit/descriptors/by-name/*.json` files and decode them via
//! [`crate::descriptor_ir2::parse_vm_descriptor2`].
//!
//! What ties those files to the Lean is `EmitByName.lean` + `scripts/emit-descriptors.sh`: every
//! by-name descriptor is now RE-DERIVED from its Lean author on each drift-check run
//! (`scripts/check-descriptor-drift.sh`), and `scripts/emit_descriptors.py`'s coverage check
//! recurses into `by-name/`, so a file no emitter reproduces is a routing-gap failure. This closed
//! a real hole: the by-name goldens used to reach disk by an UNGATED hand transcription of the Lean
//! `#guard` string, and `predicate-arith.json` had drifted through it to a 5-wide re-authoring with
//! both Poseidon2 weld legs missing — a deployed, demonstrated forgery. The route now forbids that
//! divergence; the falsifier is `circuit/tests/predicate_arith_fact_weld_canary.rs`.
//!
//! The depth-general Merkle membership is built by [`membership_descriptor_of_depth`]
//! (Foundation 2), not parsed.

use std::collections::HashMap;
use std::sync::LazyLock;

use crate::descriptor_ir2::{EffectVmDescriptor2, parse_vm_descriptor2};

/// Parse-once cache for the byte-pinned static goldens. `descriptor_by_name` sits on the
/// per-verify path (`bridge/src/verifier.rs`), and `parse_vm_descriptor2` walks the JSON into
/// fresh `Vec`s at 15–57 µs/call — pure waste on an immutable constant. We parse each golden ONCE
/// here and clone from the cache on dispatch (clone ≪ parse), preserving the exact owned-return
/// signature (zero caller change) AND the legible byte-pin (the `*_JSON` strings remain the source
/// of truth — this only memoizes the deterministic decode). A golden that fails to decode is simply
/// absent from the map, so dispatch still falls through to the fail-closed `None`.
static GOLDEN_CACHE: LazyLock<HashMap<&'static str, EffectVmDescriptor2>> = LazyLock::new(|| {
    STATIC_GOLDENS
        .iter()
        .filter_map(|(name, json)| parse_vm_descriptor2(json).ok().map(|d| (*name, d)))
        .collect()
});

/// Parse the immutable Lean-emitted note-spend and delegate artifacts once, then clone on dispatch.
/// These helpers no longer lower constraints from the Rust DSL.
static NOTE_SPEND_CACHE: LazyLock<Option<EffectVmDescriptor2>> =
    LazyLock::new(|| note_spend_leaf_descriptor().ok());
static DELEGATE_CACHE: LazyLock<EffectVmDescriptor2> = LazyLock::new(delegate_binding_descriptor);

/// The (name → byte-pinned golden JSON) table — the single source of truth shared by the cache and
/// the table-DERIVED cover test [`tests::every_static_golden_decodes_and_dispatches`], so no name
/// can drift between dispatch and validation. That test walks THIS table (not a transcribed name
/// list), so a row that lands is checked the moment it lands.
const STATIC_GOLDENS: &[(&str, &str)] = &[
    ("dfa-routing-toggle-2state::poseidon2-v1", DFA_ROUTING_JSON),
    // The TABLE-AS-INPUT DFA-routing descriptor (`DfaRoutingTableEmit.lean`, routed through
    // `EmitByName.lean`). Deliberately dispatched by EXACT NAME only — it is NOT a member of
    // `PredicateKind::Dfa`'s family (that name list stays the deployed toggle descriptor), the same
    // additive shape `faithful-note-spend-v3` and the automatafl leaves use.
    //
    // Why it is worth serving beside the toggle descriptor: its Lean refinement
    // `tableRouting_refines_classify` is over the WHOLE emitted descriptor and GENERAL over the
    // transition table, the automaton and the descriptor name — `Satisfied2Public` of the emitted
    // bytes implies the exposed `pi[final_state]` IS `classifyFrom d pi[initial_state] word` for the
    // ℕ-word read off the symbol column. The toggle descriptor's refinement is per-automaton and
    // carries a terminal-step hypothesis plus a mod-`p` canonicality envelope; this one carries
    // NEITHER, because the transition tooth is one `exact_public_rows` lookup (row-uniform: lookups
    // have no last-row zerofier exemption) and table membership is an exact integer equality.
    //
    // Residual, named: the `exact_public_rows` LogUp receive is UNIT-CAPACITY, so a satisfying
    // witness must consume the declared row multiset EXACTLY — this restricts witness EXISTENCE for
    // words that re-use a transition, not soundness (the refinement consumes only the row
    // constraints + table faithfulness). The checked-in instance declares the single transition
    // `(0, 1, 1)`; a wider automaton needs its own emitted instance of the same Lean family.
    // Legacy shape: binds an edge multiset and endpoints, but not the ordered word.
    (
        "dregg-dfa-routing-table::exact-public-v1",
        DFA_ROUTING_TABLE_EXACT_PUBLIC_JSON,
    ),
    (
        "dregg-dfa-routing-table::route8-bound-v1",
        DFA_ROUTING_TABLE_ROUTE8_JSON,
    ),
    (
        "dregg-temporal-predicate-gte::dsl-v1",
        TEMPORAL_PREDICATE_JSON,
    ),
    (
        "merkle-membership-depth2-4ary::poseidon2-v1",
        MERKLE_MEMBERSHIP_DEPTH2_JSON,
    ),
    (
        "dregg-membership-adjacency-wide::node8-v1",
        ADJACENCY_MEMBERSHIP_WIDE_JSON,
    ),
    (
        "dregg-attested-fact-membership::v1",
        ATTESTED_FACT_MEMBERSHIP_JSON,
    ),
    (
        "quantified-absence-quotient-accumulator::babybear4-v1",
        QUANTIFIED_ABSENCE_JSON,
    ),
    ("dregg-turn-chain-binding-v2", TURN_CHAIN_BINDING_JSON),
    ("dregg-accumulator-nonrev-emit-v2", ACCUMULATOR_NONREV_JSON),
    (
        "dregg-predicate-arith-ge::threshold-v1",
        PREDICATE_ARITH_JSON,
    ),
    (
        "dregg-predicate-arith-le::threshold-v1",
        PREDICATE_ARITH_LE_JSON,
    ),
    (
        "dregg-predicate-arith-gt::threshold-v1",
        PREDICATE_ARITH_GT_JSON,
    ),
    (
        "dregg-predicate-arith-lt::threshold-v1",
        PREDICATE_ARITH_LT_JSON,
    ),
    (
        "dregg-predicate-arith-neq::threshold-v1",
        PREDICATE_ARITH_NEQ_JSON,
    ),
    (
        "dregg-predicate-arith-inrange::bounds-v1",
        PREDICATE_ARITH_INRANGE_JSON,
    ),
    (
        "dregg-presentation-freshness::summary-v1",
        PRESENTATION_FRESHNESS_JSON,
    ),
    (
        "faithful-note-spend-v2::exact-note16-root8-hiding",
        FAITHFUL_NOTE_SPEND_V2_JSON,
    ),
    (
        "faithful-note-spend-v3-plan::exact-aafi-fns3-rotated-wide-state",
        FAITHFUL_NOTE_SPEND_EXACT_V3_JSON,
    ),
    ("dregg-bound-presentation::v1", BOUND_PRESENTATION_JSON),
    ("dregg-blinded-membership::v1", BLINDED_MEMBERSHIP_JSON),
    ("dregg-derivation-v1", DERIVATION_JSON),
    (
        "dregg-effectvm-custom-v1",
        crate::effect_vm_descriptors::DREGG_EFFECTVM_CUSTOM_IR2_JSON,
    ),
    ("dregg-dyck-parse-v1", DYCK_PARSE_JSON),
    // The 8-felt WELDED attested-automaton descriptor (`AttestedAutomatonWeld8.lean` §3, GRADUATED
    // 2026-11-06 in §3.G: the two range teeth are lookups into `range_w15`/`range_w1`, so the
    // `ranges`/`hash_sites` carriers are empty and the v2 assembly admits it). Dispatched by exact
    // name only, like the table-routed DFA above. Its Lean denotation through all eight root lanes
    // is `AttestedAutomatonLanes8.Satisfied2Lanes8`; prove/verify and the forged-edge refusal are
    // `circuit/tests/weld8_served.rs`.
    (
        "dregg-attested-automaton::map-committed-weld8-v1",
        ATTESTED_AUTOMATON_WELD8_JSON,
    ),
    (
        "dregg-attested-automaton::map-committed-weld8-bound-v1",
        ATTESTED_AUTOMATON_WELD8_BOUND_JSON,
    ),
    // The automatafl board-transition automaton-step (D1) descriptors — the Lean-emitted
    // `automataflStepDescN {2,11}` (`AutomataflStepEmit.lean`), packed-felt board commitment,
    // ZERO lookups. These back the deployed automatafl proof-carrying leaderboard's per-turn D1
    // leaf (`dreggnet_game_board::AutomataflMatch`) — the object PROVEN in Lean becoming the object
    // DEPLOYED, replacing the hand-authored Rust AIR (`dregg-automatafl/src/air.rs`). Like
    // `faithful-note-spend-v3`, these are deliberately absent from every `PredicateKind` family:
    // they are re-provable recursion-leaf relations dispatched by exact name, not predicates.
    ("dregg-automatafl-step-d1-n2", AUTOMATAFL_STEP_N2_JSON),
    ("dregg-automatafl-step-d1-n11", AUTOMATAFL_STEP_N11_JSON),
    // The automatafl move-adjudication (RESOLVE, Leg R: `old → mid`) descriptors — the Lean-emitted
    // `automataflResolveDescN {2,11}` (`AutomataflResolveEmit.lean`), whose `cMidV4` IS
    // `AutomataflRules.roundStep`'s resolve board (`resolve_sat_imp_roundBoardN`). The golden
    // already exists on disk and is emitted by `EmitByName.lean`; this makes it dispatchable by
    // name for the two-leg fold's resolve leaf (`dregg-automatafl/src/resolve_witness.rs`).
    ("dregg-automatafl-resolve-n2", AUTOMATAFL_RESOLVE_N2_JSON),
    ("dregg-automatafl-resolve-n11", AUTOMATAFL_RESOLVE_N11_JSON),
    // The automatafl conflict-round (LEG C: `roundStep`'s `.again` branch) descriptors — the
    // Lean-emitted `automataflLegCDescN {5,11}` (`AutomataflLegCEmit.lean`), whose OUT window IS
    // `roundStep`'s `.again` RoundState up to `List.Perm` on marks (`legC_sat_imp_roundAgainN`, M2).
    // Byte-pinned in `AutomataflLegCGolden`; n=5 is the D4a/D4b audit-witness board, n=11 the
    // deployed stock game. These back the multi-round fold's per-conflict-round leaf
    // (`dregg-automatafl/src/legc_witness.rs`, M4); HASH-FREE, ZERO lookups.
    ("dregg-automatafl-legc-n5", AUTOMATAFL_LEGC_N5_JSON),
    ("dregg-automatafl-legc-n11", AUTOMATAFL_LEGC_N11_JSON),
    // The automatafl RESOLVE-MARKS (Leg R for a CLEAN ROUND of a multi-round turn) descriptors — the
    // Lean-emitted `automataflResolveMarksDescN {2,11}` (`AutomataflResolveMarksCapstone.lean`): the
    // resolve descriptor VERBATIM plus a marks tail (the accumulated `marksIn` commitment, the two
    // moves' destination one-hots, and the two marks-legality NOR pins). PROVEN: `cMidV4` IS
    // `roundStep`'s clean-round resolve board at ACCUMULATED marks (`resolve_sat_imp_roundBoardMarksN`,
    // `turn_sat_imp_roundStepMarks_pi`), the marks-legality re-check is a DESCRIPTOR THEOREM
    // (`resolveMarksMoveLegal`, not assumed), and the published `marksIn` window is the base-4-injective
    // pack of the decoded indicator (`resolveMarks_marksIn_pi_of_sat`) — the hash-free seam to Leg C's
    // `marksOut`. Byte-pinned in `AutomataflResolveMarksGolden`; this makes the marks-aware clean leaf
    // MINTABLE for the multi-round fold (`dregg-automatafl/src/resolve_marks_witness.rs`, M6->deploy).
    // HASH-FREE, ZERO lookups. n=2 is the minimal instance (460w/21pi/566c); n=11 the deployed stock
    // game (1453w/45pi/1817c).
    (
        "dregg-automatafl-resolve-marks-n2",
        AUTOMATAFL_RESOLVE_MARKS_N2_JSON,
    ),
    (
        "dregg-automatafl-resolve-marks-n11",
        AUTOMATAFL_RESOLVE_MARKS_N11_JSON,
    ),
    // The automatafl STEP-MARKS (Leg A for a CLEAN ROUND: the automaton step carrying a FROZEN marks
    // window) descriptors — the Lean-emitted `automataflStepMarksDescN {2,11}`
    // (`AutomataflStepMarksCapstone.lean`): the step descriptor `automataflStepDescN` VERBATIM plus one
    // marks window (the accumulated `marksIn` commitment `marksCommitFamilyAt` at fresh columns above
    // `A_WIDTH_N n`). This makes Leg A's OUT window 20-lane `[board(9) ‖ marks(9) ‖ auto(2)]` so the
    // clean sub-chain `RM(20) → A(20)` is UNIFORM-WIDTH. PROVEN: the emitted `new` board IS
    // `AutomataflRules.automatonStepCfg`'s cell at ANY marks (`astep_marks_sat_imp_automatonStepCfgN`,
    // marks-independent, reusing the step capstone via `stepMarks_restrict`); the published `marksIn`
    // window is the base-4-injective pack of the decoded indicator (`stepMarks_marksIn_pi_of_sat`); and
    // marks are FROZEN (`stepMarks_marksOut_eq_marksIn`: one published window, so `marksOut = marksIn`).
    // Byte-pinned in `AutomataflStepMarksGolden`; this makes the marks-carrying clean-round automaton-step
    // leaf MINTABLE (`dregg-automatafl/src/step_marks_witness.rs`, M6′->deploy). HASH-FREE, ZERO lookups.
    // n=2 is the minimal instance (261w/23pi/415c); n=11 the deployed stock game (810w/47pi/1213c).
    (
        "dregg-automatafl-step-marks-n2",
        AUTOMATAFL_STEP_MARKS_N2_JSON,
    ),
    (
        "dregg-automatafl-step-marks-n11",
        AUTOMATAFL_STEP_MARKS_N11_JSON,
    ),
    // The four peer-chain lightclient verification AIRs — dispatched by EXACT NAME (they are not a
    // `PredicateKind` family). Keys are the descriptors' self-declared `name` fields; the golden's
    // `name` must equal the key (checked by `every_static_golden_decodes_and_dispatches`). This is
    // what makes the STARK-ified lightclients PRODUCIBLE by a node (`descriptor_by_name` → prove).
    //
    // ⚑⚑ **AND PRODUCIBLE IS ALL IT IS. MEASURED 2026-08-05, SO NOBODY RE-DISCOVERS IT: NOT ONE OF
    // THESE FOUR HAS A NON-TEST RESOLVER.** Every const holding one of these names lives in
    // `circuit/tests/{eth,tendermint,solana,midnight}_lightclient_proves.rs`. The name-agnostic
    // production seams that COULD resolve them — `turn/src/conditional.rs:502/570`
    // (`ProofCondition::expected_air`), `bridge/src/verifier.rs:335`,
    // `circuit/src/presentation.rs:90`, `wasm/src/lib.rs:408` — are never handed one of these
    // strings anywhere in the repo. `turn/src/executor/` contains exactly ONE head verifier,
    // `mina_head_verifier.rs`. So the row above is a claim about DISPATCH, and the sentence a reader
    // should take away is *"a node CAN prove this"*, never *"a node checks this"*.
    //
    // ⚑ **THE JUDGEMENT, PER CHAIN — three GAPS and one PREMATURE, not four by-design.** The
    // missing consumer has the same shape in every case, and `mina_head_verifier.rs` is the worked
    // example: a `WitnessedPredicateVerifier` under a fixed `Custom { vk_hash }`, registered in
    // `turn/src/executor/membership_verifier.rs::registry_with_real_verifiers` beside the Mina row,
    // pinning PI slots to a CELL-PROGRAM trust root and to the slot the turn writes, then
    // `descriptor_by_name(…)` → `verify_vm_descriptor2`, fail-closed at every seam.
    //
    // * **`eth` — GAP.** `eth-lightclient/` is a real Altair sync-committee + finality client whose
    //   DECISIONS already come from the Lean archive (`verified_gate::decide` →
    //   `dregg_lean_ffi::verified_eth_lc_verify`). Its only production caller is the standalone CLI
    //   `eth-lightclient/src/bin/verify_holding.rs`; `node/`, `turn/` and `persist/` do not depend
    //   on that crate at all. So a verified ETH decision terminates in a Rust `Bool` on the
    //   operator's own machine and produces NO dregg state transition — verbatim the wound
    //   `mina_head_verifier.rs`'s header was written about, one chain over. Missing consumer:
    //   `turn/src/executor/eth_head_verifier.rs`.
    // * **`tm` — GAP, and colder.** `cosmos-lightclient::verify_cosmos_header` (→
    //   `verified_tm_lc_verify` / `verified_tm_skip_verify`) has NO production call site in the
    //   repo — only that crate's own tests and `dregg-interchain-gov`'s. Both legs, native and
    //   STARK, are unconsumed. Missing consumer: `turn/src/executor/tm_head_verifier.rs`.
    // * **`solana` — THE SHARPEST GAP, because here the native leg IS live and the proved one is
    //   not.** `bridge/src/solana_relayer.rs:836` and `:929` call
    //   `solana_trustless::verify_lock_proof_consensus{_anchored}` on the real finalized-RPC mint
    //   path, so Solana consensus verification already gates value movement — in hand-written Rust,
    //   outside any AIR. Meanwhile the node's own live Solana surface
    //   (`node/src/poa_holding_api.rs`) imports only `validate_rpc_snapshot`, the RPC-beta trust
    //   tier, NOT the consensus path; and `poa-solana-gate::verify_consensus_source`, the one
    //   function that can return a `ConsensusVerified` holding, has no non-test caller. Missing
    //   consumer: `turn/src/executor/solana_head_verifier.rs`, with
    //   [`SOLANA_STAKE_TABLE_FOLD_JSON`] as its SUB-PROOF — exactly the relationship
    //   `dregg-pasta-fq-chainlink::v1` has to the Mina head rung: verify the fold, then pin the
    //   light client's `PI_TOTAL_STK` slots 19..22 against the denominator it published.
    // * **`midnight` — NOT a gap; PREMATURE, and say so rather than implying a peer.** There is no
    //   Midnight light client in this tree. `bridge/src/midnight.rs` verifies an ed25519
    //   `FederationAttestation` — a 2/3 multisig over dregg's own federation — which is not a header
    //   verification, and `midnight_inclusion.rs`'s mirror tree is an explicit BLAKE3 PLACEHOLDER
    //   rather than Poseidon-over-BLS12-381, so it is not Compact-compatible. Nothing named
    //   `midnight` exists anywhere in `turn/`, `cell/`, `persist/` or `node/`. A consumer written
    //   today would refuse a turn on a proof about a chain state this tree cannot independently
    //   derive; the missing piece is upstream of the AIR, not downstream of it.
    //
    // ⚠ These four rows are deliberately KEPT despite having no resolver, and that is a different
    // call from the one made for `dregg-pasta-fq-wraplink::v1` below. The wraplink was STRICTLY
    // DOMINATED — a superseding sibling took over its role in the same seam, so two resolvable
    // names meant the next reader could pick the weaker object. These four are dominated by
    // nothing; the wound is the ABSENT consumer, and deleting the row would delete the thing that
    // consumer must dispatch. What is not kept is the implication: this comment is the second
    // source for "served, and by whom", and it says by nobody.
    (
        "dregg-eth-lightclient-verify::v1",
        ETH_LIGHTCLIENT_VERIFY_JSON,
    ),
    (
        "dregg-tm-lightclient-verify::v1",
        TM_LIGHTCLIENT_VERIFY_JSON,
    ),
    (
        "dregg-solana-lightclient-verify::v1",
        SOLANA_LIGHTCLIENT_VERIFY_JSON,
    ),
    (
        "dregg-midnight-lightclient-verify::v1",
        MIDNIGHT_LIGHTCLIENT_VERIFY_JSON,
    ),
    // ⚑ The Mina anchored-head verify AIR — the fifth, and the first of the five with a consumer
    // that REFUSES a dregg state transition on it (`dregg_turn::executor::mina_head_verifier`).
    (
        "dregg-mina-lightclient-verify::v1",
        MINA_LIGHTCLIENT_VERIFY_JSON,
    ),
    // ⚑ Its MULTI-ROW companion: one row per EXHIBITED Mina block. First compiler-authored
    // multi-row descriptor in the tree.
    (
        "dregg-mina-lightclient-link::v1",
        MINA_LIGHTCLIENT_LINK_JSON,
    ),
    // ⚑⚑ THE Fq-TRANSCRIPT SUB-PROOF the Mina verify rung recursion-binds to. Served here because
    // `mina_head_verifier::verify` VERIFIES a STARK over it before it accepts a head: a dispatch
    // miss is a REJECTION of the turn, so a node built without this row refuses Mina heads rather
    // than waving the carrier through.
    //
    // ⚑⚑ 2026-08-05 — THIS IS THE EIGHT-BLOCK CHAIN LINK, AND `dregg-pasta-fq-wraplink::v1` IS NO
    // LONGER SERVED AT ALL. The 46-link fold, the endo lift and the ξ chain were all PROVED against
    // the chainlink and none of them could reach it by name; the head verifier, meanwhile, bound the
    // seven-block wraplink beside it. Both halves of that are now one name. The wraplink descriptor
    // is still EMITTED and checked in (`EmitByName.lean` routes it; `pasta_fq_wrap_transcript_proves`
    // and `mina_xi_endo_weld` read its bytes with `include_str!`), but nothing dispatches it by name
    // any more, and a served descriptor no consumer resolves is the same wound in the other
    // direction. A pre-flag-day proof identity is answered `None` and REFUSED rather than
    // reinterpreted under a program that pins one fewer sponge lane.
    (
        "dregg-pasta-fq-chainlink::v1",
        MINA_CHAINLINK_TRANSCRIPT_JSON,
    ),
    // ⚑⚑ 2026-08-08 — THE FINALIZE-CONJUNCTION SUB-PROOF the head's third `proof_bind`
    // (`FINALIZE_XI_B_PROVED`, guard col 58) pins. Served because `mina_head_verifier::verify`
    // VERIFIES a STARK over it before accepting a head (REFUSAL 15): a dispatch miss is a
    // REJECTION of the turn, exactly as for the chainlink row above.
    //
    // ⚠ **FOUND ABSENT BY REFUSAL 15's OWN POSITIVE-POLARITY TEST, the day the refusal was
    // wired.** From 2026-08-06 to 2026-08-08 this descriptor was emitted, checked in, pinned by
    // the head's bind — and dispatched by NOTHING: `check_conjunction_binding` was dead code, so
    // no consumer ever asked for the name and the miss was invisible. Had the refusal been wired
    // without this row, every head would have been refused fail-closed — honest, but the honest
    // PATH would have been unreachable. The same wound the wraplink note above records, in the
    // other direction: a pinned descriptor no registry serves.
    (
        "dregg-mina-wrap-conjunction::v1",
        MINA_WRAP_CONJUNCTION_JSON,
    ),
    // ⚑⚑ 2026-08-05 — THE PHASE-1 (Fp) HALF OF THE SAME CHAIN, served so the weld is REACHABLE and
    // not merely proved. The phase-2 chain above absorbs `fq_digest` as tape element 0 and NOTHING
    // derived it; `MinaPhase1Chain` does, and its link 26's OUTGOING LANE 1 is that element. A
    // consumer that resolves both names can compare 32 felts — elementwise, full limb width, no
    // digest and therefore no birthday bound — and know WHOSE tape the phase-2 fold absorbed.
    // Same eight-block pin layout (`MinaPhase2Chain.chainPins`, 256 PIs), same 2 048-instruction
    // program at `pLimb` instead of `qLimb`.
    (
        "dregg-pasta-fp-chainlink::v1",
        MINA_FP_CHAINLINK_TRANSCRIPT_JSON,
    ),
    // ⚑⚑⚑ 2026-08-10 — THE STATE-HASH PREIMAGE PROGRAM, served so REFUSAL 17 can dispatch it.
    // `dregg-mina-lightclient-link::v1`'s state-hash seam has pinned this descriptor's fingerprint
    // since it was written, and NOTHING resolved the name: the seam declared a sub-program no
    // consumer could obtain, which is why its `state-hash-preimage` port had no cover. Emitted and
    // pinned but served by nothing is the same shape the conjunction descriptor sat in for two
    // days — see that row's note.
    ("dregg-pasta-fp-absorb::v1", MINA_FP_ABSORB_JSON),
    // ⚑ The Solana STAKE-TABLE FOLD: one row per stake-table entry. The eight-lane Poseidon2
    // commitment to the table and the u64 active-stake DENOMINATOR both come out of the SAME rows,
    // so a swapped validator set with an identical tally moves the root.
    (
        "dregg-solana-stake-table-fold::v1",
        SOLANA_STAKE_TABLE_FOLD_JSON,
    ),
];

pub use crate::blinded_membership_witness::{
    BLINDED_4ARY_NAME_PREFIX, blinded_membership_descriptor_of_depth_4ary,
};
pub use crate::delegate_descriptor::{DELEGATE_V2_NAME, delegate_binding_descriptor};
pub use crate::membership_descriptor_4ary::{
    MEMBERSHIP_4ARY_NAME_PREFIX, membership_descriptor_of_depth_4ary,
};
pub use crate::membership_descriptor_general::membership_descriptor_of_depth;
pub use crate::note_spend_witness::{NOTE_SPEND_LEAF_NAME, note_spend_leaf_descriptor};

// ---- The predicate-descriptor goldens: `include_str!` of the by-name files each Lean `#guard`
// ---- emits and `scripts/emit-descriptors.sh` re-derives (see the module header). ----
const DFA_ROUTING_JSON: &str = include_str!("../descriptors/by-name/dfa-routing.json");
const DFA_ROUTING_TABLE_ROUTE8_JSON: &str =
    include_str!("../descriptors/by-name/dfa-routing-table-route8-bound-v1.json");
const DFA_ROUTING_TABLE_EXACT_PUBLIC_JSON: &str =
    include_str!("../descriptors/by-name/dfa-routing-table-exact-public-v1.json");
const TEMPORAL_PREDICATE_JSON: &str =
    include_str!("../descriptors/by-name/temporal-predicate.json");
const MERKLE_MEMBERSHIP_DEPTH2_JSON: &str =
    include_str!("../descriptors/by-name/merkle-membership-depth2.json");
const ATTESTED_FACT_MEMBERSHIP_JSON: &str =
    include_str!("../descriptors/by-name/attested-fact-membership.json");
/// ⚑ node8 CUTOVER: the one-felt `adjacency-membership.json` (w18/5PI) is DELETED. This is the
/// WIDE twin (w88/26PI); the retired NAME is not routed, so a pre-cutover proof identity is
/// answered `None` and REFUSED rather than reinterpreted under different semantics.
const ADJACENCY_MEMBERSHIP_WIDE_JSON: &str =
    include_str!("../descriptors/by-name/adjacency-membership-wide.json");
const QUANTIFIED_ABSENCE_JSON: &str =
    include_str!("../descriptors/by-name/quantified-absence.json");
/// The **turn-chain binding** family (`dregg-turn-chain-binding-v2`), authored in
/// `metatheory/Dregg2/Circuit/Emit/EffectVmEmitTurnChainBinding.lean` (proved there, with refutation
/// teeth for forged continuity / idx-step / real_count). Byte source: `metatheory/EmitTurnChain.lean`.
/// This is the sole constraint authorship of the deployed whole-history chain proof
/// (`grain-verify/src/r3.rs`); Rust supplies only the witness and descriptor interpreter.
const TURN_CHAIN_BINDING_JSON: &str =
    include_str!("../descriptors/by-name/turn-chain-binding.json");
const ACCUMULATOR_NONREV_JSON: &str =
    include_str!("../descriptors/by-name/accumulator-nonrev.json");
const PREDICATE_ARITH_JSON: &str = include_str!("../descriptors/by-name/predicate-arith.json");
/// The arithmetic COMPARISON goldens (`≤`/`>`/`<`/`≠`/InRange), authored + byte-pinned in
/// `metatheory/Dregg2/Circuit/Emit/Predicates{Le,Gt,Lt,Neq,InRange}Emit.lean`.
///
/// **Every one of them carries the Poseidon2 value↔fact weld** (M14), like the `≥` sibling above:
/// the two chip lookups that force `fact_commitment = hash_2_to_1(hash_fact(pred, [value, ..]),
/// state_root)` INSIDE the circuit, so the comparison and the committed fact share the compared
/// column (`INPUT`, col 0).
///
/// Until M14 these were the leaner pre-weld shape — the C1/C2/C3/C5/C6 comparison teeth with
/// `fact_commitment` a pass-through public input. Their Lean authors genuinely emitted that shape (so
/// they were never re-authored mirrors like the `≥` file was), but it left the compared column and
/// the `fact_commitment` column in DISJOINT constraint sets — exactly what the `≥` forgery exploited:
/// a prover could satisfy `value ≤/>/</≠ threshold` on a value of its choosing while pinning an
/// unrelated, honest, verifier-expected `fact_commitment`. `prove_predicate_for_fact`
/// (`bridge/src/present.rs`) derived the commitment from the value out-of-circuit, which a caller
/// reaching the witness builders directly bypassed. That is now welded shut in-circuit, and the
/// builders make it unrepresentable at the API (the commitment is a computed OUTPUT).
///
/// The welded widths differ by layout: `≤`/`>`/`<` are 24 (geometry identical to `≥`), `≠` is 25 (it
/// carries `DIFF_INV`), InRange is 26 (it carries `LO`/`HI`/`DIFF_LO`/`DIFF_HI`). This claim is a
/// CHECK, not prose: `every_sibling_dispatches_with_both_weld_legs`
/// (`circuit-prove/tests/predicates_comparison_emit_gate.rs`) asserts both legs on the served bytes,
/// and `circuit/tests/predicate_comparison_fact_weld_canary.rs` drives the forgery per sibling.
/// Their Rust witness builders are in `crate::predicate_comparison_witness`.
const PREDICATE_ARITH_LE_JSON: &str =
    include_str!("../descriptors/by-name/predicate-arith-le.json");
const PREDICATE_ARITH_GT_JSON: &str =
    include_str!("../descriptors/by-name/predicate-arith-gt.json");
const PREDICATE_ARITH_LT_JSON: &str =
    include_str!("../descriptors/by-name/predicate-arith-lt.json");
const PREDICATE_ARITH_NEQ_JSON: &str =
    include_str!("../descriptors/by-name/predicate-arith-neq.json");
const PREDICATE_ARITH_INRANGE_JSON: &str =
    include_str!("../descriptors/by-name/predicate-arith-inrange.json");
/// The `presentation` family (token-presentation summary AIR + internalized FRESHNESS binding),
/// authored in `metatheory/Dregg2/Circuit/Emit/PresentationEmit.lean` (`presentationFreshnessDesc`)
/// and byte-pinned there by an `emitVmJson2` `#guard`. The blinded-presentation path reduces to
/// this descriptor for the summary + freshness tooth; the blinded issuer Merkle membership itself
/// rides as a NAMED STARK leaf (the `FITS_WITH_NAMED_GATE` verdict), so it is not internalized here.
///
/// ⚠ This doc named `sdk::verify_anonymous_presentation` as that path's consumer until
/// 2026-08-06. Measured that day: **`verify_anonymous_presentation` has zero call sites** — it is
/// a public SDK function nothing in the tree reaches. Citing an uncalled function as the consumer
/// that justifies a descriptor makes the descriptor look wired when it is not. The `bridge` issuer
/// path is the real one; the SDK entry point is a surface awaiting a consumer.
const PRESENTATION_FRESHNESS_JSON: &str =
    include_str!("../descriptors/by-name/presentation-freshness.json");
/// Exact shielded-owner opening, faithful note-tree membership, and nullifier relation authored
/// in `Dregg2/Circuit/Emit/FaithfulNoteSpendDescriptorPlan.lean`.
const FAITHFUL_NOTE_SPEND_V2_JSON: &str =
    include_str!("../descriptors/by-name/faithful-note-spend-v2.json");
/// The additive exact-nullifier FNSP-v3 descriptor. This is production-parsed and addressable by
/// its exact AIR name, but it is deliberately absent from every [`PredicateKind`] family and from
/// the live rotated registry/epoch selector. Its bytes are authored by
/// `ExactNullifierAafiRotatedStateWeld.lean` and re-derived by `EmitByName.lean`.
const FAITHFUL_NOTE_SPEND_EXACT_V3_JSON: &str =
    include_str!("../descriptors/by-name/faithful-note-spend-exact-v3.json");
/// The **bound-presentation** family (`dregg-bound-presentation::v1`), authored in
/// `metatheory/Dregg2/Circuit/Emit/BoundPresentationEmit.lean` (`boundPresentationDesc`) and
/// byte-pinned there by an `emitVmJson2` `#guard`. This is the Golden-Lift-stage-1 successor to the
/// freshness summary: the `presentation_tag` PI is CONSTRAINED in-circuit to its arity-4 Poseidon2
/// chip image (the tag-binding tooth `presentationFreshnessDesc` left to a named STARK leaf), so a
/// light client / the recursion fold re-verifies the tag binding from the descriptor alone. Its Rust
/// witness builder is [`crate::bound_presentation_witness::bound_presentation_witness`].
const BOUND_PRESENTATION_JSON: &str =
    include_str!("../descriptors/by-name/bound-presentation.json");
/// The **blinded ring-membership** family (`dregg-blinded-membership::v1`), authored in
/// `metatheory/Dregg2/Circuit/Emit/BlindedMembershipEmit.lean` (`blindedMembershipDesc`) and
/// byte-pinned there by an `emitVmJson2` `#guard`. The Golden-Lift-stage-3d successor to the
/// off-descriptor blinded-Merkle STARK (`poseidon2_air.rs:647`): both the unlinkability blinding
/// (`blinded_leaf = hash_2_to_1(leaf, blinding)`) and the 4-ary Merkle membership are CONSTRAINED
/// in-circuit (chip lookups), so a light client / the recursion fold re-verifies them from the
/// descriptor alone. Its Rust witness builder is
/// [`crate::blinded_membership_witness::blinded_membership_witness`].
const BLINDED_MEMBERSHIP_JSON: &str =
    include_str!("../descriptors/by-name/blinded-membership.json");
/// The **Datalog derivation** family (`dregg-derivation-v1`), authored in
/// `metatheory/Dregg2/Circuit/Emit/DerivationEmit.lean` (`derivationDesc`) and byte-pinned there by
/// an `emitVmJson2` `#guard`. This is the emit-from-Lean twin of the hand derivation AIR
/// (`circuit/src/dsl/derivation.rs::derivation_circuit_descriptor`): a Datalog rule FIRES — the head
/// fact is the genuine `hash_fact` of `(head_pred, head_terms)` (the C4 chip tooth), the body facts
/// are membership-authenticated against the committed `state_root` (pi[0]), the conclusion is bound
/// to pi[1], and the EIGHT exported body-fact hashes to pi[5..12] (C6b/C6c, the
/// body↔membership-leaf binding). Its Rust witness builder is
/// [`crate::derivation_witness::derivation_descriptor_witness`].
const DERIVATION_JSON: &str = include_str!("../descriptors/by-name/derivation.json");
/// The **Dyck pushdown parse** family (`dregg-dyck-parse-v1`), authored in
/// `metatheory/Dregg2/Circuit/Emit/DyckStackEmit.lean` (`dyckParseDesc`) and byte-pinned there by
/// an `emitVmJson2` `#guard`. The loader-flip retired the hand-authored IR-v1 Rust AIR: the
/// DEPLOYED dispatch serves the Lean-emitted
/// descriptor (38 wide: the 23 Rust `dyck_stack::col` base columns index for index, + the `ACC`
/// copy-forward accumulator + 2×7 chip lanes), so the deployed object IS the one the
/// `DyckStackRefine` theorems read. Its Rust witness lift is
/// [`crate::dsl::dyck_stack::lift_witness_to_v2`]; the prove-path teeth live in
/// `circuit-prove/tests/dyck_parse_tamper.rs`.
const DYCK_PARSE_JSON: &str = include_str!("../descriptors/by-name/dyck-parse.json");
/// The 8-felt welded attested-automaton descriptor
/// (`dregg-attested-automaton::map-committed-weld8-v1`), authored in `AttestedAutomatonWeld8.lean`
/// and re-derived onto `by-name/` by `EmitByName.lean`: one `map_op` read of the edge
/// `2·current + symbol ↦ next` against an 8-column root group pinned to PIs 2..9, plus the two
/// graduated range lookups.
const ATTESTED_AUTOMATON_WELD8_BOUND_JSON: &str =
    include_str!("../descriptors/by-name/attested-automaton-map-committed-weld8-bound-v1.json");
const ATTESTED_AUTOMATON_WELD8_JSON: &str =
    include_str!("../descriptors/by-name/attested-automaton-map-committed-weld8-v1.json");
/// The automatafl D1 automaton-step descriptors (Lean `automataflStepDescN {2,11}`), byte-pinned by
/// their `emitVmJson2` `#guard` and re-derived onto `by-name/` by `EmitByName.lean`. n=2 is the
/// minimal complete instance; n=11 is the deployed stock-game board size.
const AUTOMATAFL_STEP_N2_JSON: &str = include_str!("../descriptors/by-name/automatafl-step.json");
const AUTOMATAFL_STEP_N11_JSON: &str =
    include_str!("../descriptors/by-name/automatafl-step-n11.json");
/// The automatafl RESOLVE (Leg R) descriptors (Lean `automataflResolveDescN {2,11}`), byte-pinned by
/// their `emitVmJson2` `#guard` and re-derived onto `by-name/` by `EmitByName.lean`. n=2 is the
/// byte-golden minimal instance (441w/20pi); n=11 is the deployed stock-game board (1273w/36pi).
const AUTOMATAFL_RESOLVE_N2_JSON: &str =
    include_str!("../descriptors/by-name/automatafl-resolve.json");
const AUTOMATAFL_RESOLVE_N11_JSON: &str =
    include_str!("../descriptors/by-name/automatafl-resolve-n11.json");
/// The automatafl LEG C (conflict-round `.again`) descriptors (Lean `automataflLegCDescN {5,11}`),
/// byte-pinned by their `emitVmJson2` `#guard` in `AutomataflLegCGolden`. n=5 is the D4a/D4b
/// audit-witness board (536w/50pi/521c); n=11 is the deployed stock game (1208w/78pi/1425c).
const AUTOMATAFL_LEGC_N5_JSON: &str =
    include_str!("../descriptors/by-name/automatafl-legc-n5.json");
const AUTOMATAFL_LEGC_N11_JSON: &str =
    include_str!("../descriptors/by-name/automatafl-legc-n11.json");
/// The automatafl RESOLVE-MARKS (Leg R, clean round of a multi-round turn) descriptors (Lean
/// `automataflResolveMarksDescN {2,11}`), byte-pinned by their `emitVmJson2` `#guard` in
/// `AutomataflResolveMarksGolden` and re-derived onto `by-name/` by `EmitByName.lean`. The resolve
/// descriptor plus a marks tail; n=2 is the minimal instance (460w/21pi), n=11 the deployed stock
/// game (1453w/45pi).
const AUTOMATAFL_RESOLVE_MARKS_N2_JSON: &str =
    include_str!("../descriptors/by-name/automatafl-resolve-marks-n2.json");
const AUTOMATAFL_RESOLVE_MARKS_N11_JSON: &str =
    include_str!("../descriptors/by-name/automatafl-resolve-marks-n11.json");
/// The automatafl STEP-MARKS (Leg A, clean round: the automaton step carrying a FROZEN marks window)
/// descriptors (Lean `automataflStepMarksDescN {2,11}`), byte-pinned by their `emitVmJson2` `#guard` in
/// `AutomataflStepMarksGolden` and re-derived onto `by-name/` by `EmitByName.lean`. The step descriptor
/// plus one marks window; n=2 is the minimal instance (261w/23pi), n=11 the deployed stock game
/// (810w/47pi).
const AUTOMATAFL_STEP_MARKS_N2_JSON: &str =
    include_str!("../descriptors/by-name/automatafl-step-marks-n2.json");
const AUTOMATAFL_STEP_MARKS_N11_JSON: &str =
    include_str!("../descriptors/by-name/automatafl-step-marks-n11.json");

/// The four STARK-ified peer-chain lightclient VERIFICATION AIRs (bridge tree), each authored +
/// byte-pinned in `metatheory/Dregg2/Circuit/Emit/LightClient{Eth,Tendermint,Solana,Midnight}Air.lean`
/// (`ethLcVerifyDesc` / `tmLcVerifyDesc` / `solLcVerifyDesc` / `midLcVerifyDesc`) and re-derived onto
/// `by-name/` by `EmitByName.lean`. Dispatched here so a
/// dregg node can `descriptor_by_name(name)` → `prove_vm_descriptor2` the consensus-verification STARK
/// (the producibility prerequisite for the gnark peer-wrap → on-chain `DreggPeerRegistry` flow). Each
/// descriptor carries the chain's no-forgery obligation; soundness WHEN USED still rests on the
/// undischarged FRI/STARK floor and the chain's trusted-instance mirror.
///
/// ⚑ **FLAG DAY 2026-08-03, ETH ONLY.** `ethLcVerifyDesc` became COMPILER OUTPUT
/// (`EffectLower.lowerAir` of the `EffectAir` source `ethHeadAir`; no hand-written `VmConstraint2`
/// in its module) and gained a `PC_SLACK` leg forcing `PC ≤ BL` — closing the participation count
/// that was an unbounded witness and PROVED at `PC = 1023` against a 512-key committee
/// (`circuit/tests/eth_lightclient_proves.rs::an_over_committee_participation_count_proved_before_
/// the_bound_and_is_refused_after` runs both polarities). Trace width 20 → 21, constraints 20 → 22,
/// the eleven anchor columns shifted up by one. **The PI surface is UNCHANGED** — 11 slots, same
/// meanings, so the gnark peer-wrap's pack over `PI[1..9]` is untouched. What re-emits:
/// `descriptors/by-name/dregg-eth-lightclient-verify-v1.json` (done) and this descriptor's VK
/// (`scripts/emit-descriptors.sh` from a committed Lean closure). Nothing else
/// moves; no other descriptor changes shape and nothing re-genesises.
const ETH_LIGHTCLIENT_VERIFY_JSON: &str =
    include_str!("../descriptors/by-name/dregg-eth-lightclient-verify-v1.json");
const TM_LIGHTCLIENT_VERIFY_JSON: &str =
    include_str!("../descriptors/by-name/dregg-tm-lightclient-verify-v1.json");
/// ⚑⚑ `dregg-solana-lightclient-verify::v1` — **MULTI-ROW since 2026-08-04, one row per
/// stake-table entry**, and Lean-COMPILED (`LightClientSolanaAir.solLcVerifyDesc` =
/// `EffectLower.lowerAir` of the `EffectAir` source `solLcVerifyAir`; no hand-written
/// `VmConstraint2` in that module). Width 79, 22 PIs, 103 constraints, four declared range tables
/// (29 / 24 / 16 / 8).
///
/// Its columns 0..43 ARE `dregg-solana-stake-table-fold::v1`'s columns, from the SAME source leg
/// list (`foldLegs`), so the two rungs cannot drift about what a stake-table row is. The two numbers
/// the light client's trust story hangs from are DERIVED from those rows:
///
///  * `PI[0..7]` — the weak-subjectivity STAKE-TABLE ROOT, as the fold's eight `.last` output lanes.
///    It was ONE column carrying a 256-bit SHA-256 root (compared at 31 bits), then NINE `.first`
///    radix-2^31 limbs that bound the full width and were read by no constraint at all. Eight lanes
///    are `8 · 30.906891 = 247.26` bits of image ⇒ an equivocating prover needs a **2^123.63**
///    birthday collision — ⚠ not the 2^247.3 second-preimage figure for the same object.
///  * `PI[18..21]` — the ACTIVE-STAKE DENOMINATOR, `.last`-pinned from the fold's accumulator.
///
/// `STAKE_TABLE_OK` is GONE: it was a witnessed bit forced `= 1` asserting the sentence the fold now
/// computes.
///
/// ⚠ **CALLERS SUPPLY A POSEIDON2 ROOT.** `EpochStakeTable::root` (`STAKE_TABLE_ROOT_TAG`,
/// `bridge/src/solana_consensus.rs`) is a domain-separated SHA-256 and is NOT this value; it must be
/// re-anchored to `dregg-solana-stake-table-root:v2` and every `WeakSubjectivityAnchor
/// ::stake_table_root` re-derived. Until then a caller passing the SHA root is REFUSED at the
/// last-row pin — loudly, at verify, which is the intended behaviour of a shape change here.
///
/// ⚠ Still CARRIED, not constrained: `ED_OK` (no in-AIR ed25519), `ROOTED_STK` (a witnessed
/// projection — the fold binds who is in the table, not who voted), and the nine bank-root limbs
/// plus the slot, which no gate reads.
const SOLANA_LIGHTCLIENT_VERIFY_JSON: &str =
    include_str!("../descriptors/by-name/dregg-solana-lightclient-verify-v1.json");
const MIDNIGHT_LIGHTCLIENT_VERIFY_JSON: &str =
    include_str!("../descriptors/by-name/dregg-midnight-lightclient-verify-v1.json");

/// ⚑ THE FIFTH PEER-CHAIN LIGHTCLIENT VERIFY AIR, AND THE ONE THAT IS CONSUMED. Authored in
/// `metatheory/Dregg2/Circuit/Emit/LightClientMinaAir.lean` as COMPILER OUTPUT — `minaLcVerifyDesc`
/// is `EffectLower.lowerAir` of the `EffectAir` source `minaHeadAir`, with no hand-written
/// `VmConstraint2` in the module — and re-derived onto `by-name/` by `EmitByName.lean`.
///
/// Unlike its four siblings this descriptor has a CONSUMER that refuses on it:
/// `dregg_turn::executor::mina_head_verifier` dispatches it from a `StateConstraint::Witnessed`, so
/// a turn is REFUSED (`TurnError::ProgramViolation`) unless the proof verifies against the
/// cell-program-pinned Mina weak-subjectivity anchor and the head the turn actually records.
///
/// Its gates DERIVE the published `blockchain_length` (`BLOCK_LEN = ANCHOR_H + SEG_LEN`) and the
/// witnessed depth (`WIT_DEPTH + SUBMIT_H = BLOCK_LEN`) rather than witnessing them, so the one
/// field a truncated peer reply leaves standing is not settable.
///
/// ⚑⚑ **FLAG DAY 2026-08-05 — `PICKLES_OK` IS GONE.** Width 30 → 49, PIs 20 → 29, constraints
/// 50 → 69; re-emit this file and rotate its VK (`turn`'s `MINA_LC_PI_COUNT` moves with it, and a
/// pre-2026-08-05 `MinaHeadProofWire` no longer decodes). The old column split in two:
///
/// * `PICKLES_WITNESSED` — the residue, STILL A BIT, renamed so no reader takes it for a check;
///   ⚑ **and SPLIT AGAIN on 2026-08-06 — see the flag day below;**
/// * ⚑ `WRAP_FS_PROVED` — **not a bit.** Its `= 1` guards NINE `proof_bind` constraints pinning the
///   row's attested program, lane by lane, to the semantic fingerprint of
///   [`MINA_CHAINLINK_TRANSCRIPT_JSON`], and PI-binds that sub-proof's public-input commitment. The
///   consumer then VERIFIES a STARK over that descriptor, fail-closed, before accepting the head.
///   A single-felt program tie would be worth `2^31`; nine `Faithful9` lanes are 256 bits.
///
/// ⚑⚑ **FLAG DAY 2026-08-06 — `PICKLES_WITNESSED` IS GONE AS A NAME.** Width 58 → 77, PIs 30 → 39,
/// constraints 63 → 74, `proof_bind`s 2 → 3; re-emit this file and rotate its VK
/// (`turn`'s `MINA_LC_PI_COUNT` moves 30 → 39 with it). PI slots 30..38 are APPENDED — every slot
/// below 30 is unmoved, so no existing offset re-indexes. The old column split again:
///
/// * `PICKLES_OPENING_WITNESSED` — what is STILL A BIT, and it is now the residue of exactly three
///   things: the IPA opening (not in circuit, and `MinaWrapOpeningGate.opening_is_vacuous_when_sg_is_free`
///   is a THEOREM that its closing check accepts at EVERY value while `sg` is a free witness),
///   `cipCorrect`, and `plonkChecksPassed`.
/// * ⚑⚑ `FINALIZE_XI_B_PROVED` — **not a bit.** Its `= 1` guards a nine-lane `proof_bind` pinning
///   `dregg-mina-wrap-conjunction::v1` (`MinaWrapConjunctionAir.conjunctionDesc`), a Lean-authored
///   16-row threaded AIR that as of 2026-08-06 publishes ξ, ζ, ζω, the evalscale `r` and the claimed
///   `b0` as 160 public inputs. A verifying STARK over it forces **ONE of Pickles'
///   `finalize_other_proof` FOUR conjuncts** — `bCorrect` against `PastaIPA.bEval` itself — plus the
///   per-round challenge/inverse reciprocity weld and the opening residual's non-free coefficients,
///   each computed by a sound core, on Mina devnet block 539508's own opening argument. A SECOND
///   conjunct, `xiCorrect`, is CARRIED but not forced here: see the ⚠ below.
///
/// ⚠ **DO NOT READ THAT AS "finalize passed".** Upstream's conjunction is a FOUR-way AND with the
/// opening; `cipCorrect` and `plonkChecksPassed` are ABSENT BY CONSTRUCTION, because a gate
/// comparing `cip` against a ξ-fold with a FREE `ft_eval0` column forces nothing at all and that
/// ∃-image vacuity has shipped in this repo before.
///
/// ⚠ **And the sub-proof's ξ is free.** `MinaWrapConjunctionAir.no_arithmetic_call_names_an_xi_block`:
/// ξ enters no sound core, so `xiCorrect` alone forces only "two free columns agree". What welds it
/// to the block's own transcript is the recursion fold
/// `dregg_circuit_prove::mina_wrap_finalize_fold::fold_endo_into_finalize` — 32 in-circuit
/// `cb.connect`s to `dregg-mina-xi-endo-lift::v1`'s output — which is a CONSUMER's constraint, not
/// this descriptor's.
///
/// `LINK_OK` and `PICKLES_OPENING_WITNESSED` remain NAMED carriers on the undischarged IPA/FRI
/// floor; `CANON_OK` has been derived since 2026-08-03.
const MINA_LIGHTCLIENT_VERIFY_JSON: &str =
    include_str!("../descriptors/by-name/dregg-mina-lightclient-verify-v1.json");

/// The **MULTI-ROW** Mina exhibited-segment AIR (`dregg-mina-lightclient-link::v1`), authored in
/// Lean as COMPILER OUTPUT (`Dregg2.Circuit.Emit.LightClientMinaLinkAir.minaLinkDesc` =
/// `EffectLower.lowerAir` of the `EffectAir` source `minaLinkAir`; no hand-written `VmConstraint2`
/// exists for it). One row per exhibited block: nine `PARENT` lanes, nine `OWNHASH` lanes, the
/// height, and the `IS_REAL`/`REAL_COUNT` pair.
///
/// ⚑ What it DERIVES is the SHAPE half of `LINK_OK` — twelve `.transition` window gates force
/// `OWNHASH[i] = PARENT[i+1]` on all nine lanes, `HEIGHT[i+1] = HEIGHT[i] + 1`, and
/// `REAL_COUNT` accumulation, with the last row's `REAL_COUNT` PI-pinned as the segment length. So
/// a published depth is PAID FOR IN COMMITTED ROWS, unlike `dregg-mina-lightclient-verify::v1`
/// where `SEG_LEN` is a free witness column in a single row.
///
/// ⚠ What it does NOT derive: that each `OWNHASH` IS the Poseidon-over-Pasta hash of its block's
/// state row. That is `LightClientMinaLinkAir.LinkHashResidual`, it stays WITNESSED, and it is the
/// non-native Pasta multiply — ~5e5 BabyBear constraints per block hash at the schoolbook limb
/// construction. A prover free to choose `OWNHASH` can still fabricate a chain; what makes a row a
/// real block is the Pickles verdict, which after 2026-08-06 is `PICKLES_OPENING_WITNESSED` (the
/// opening, `cipCorrect` and `plonkChecksPassed` — still a witness, and now named for exactly what
/// it carries) plus `FINALIZE_XI_B_PROVED`, which is not a witness at all.
const MINA_LIGHTCLIENT_LINK_JSON: &str =
    include_str!("../descriptors/by-name/dregg-mina-lightclient-link-v1.json");

/// ⚑⚑ `dregg-pasta-fq-chainlink::v1` — **THE EIGHT-BLOCK LINK THE 46-LINK FOLD IS BUILT ON**, served
/// from 2026-08-05 and CONSUMED by `turn::executor::mina_head_verifier` from the same day.
/// Lean-authored (`Dregg2.Circuit.Emit.MinaPhase2Chain.chainDesc`).
///
/// The SAME 2 048-instruction `fq_kimchi` sponge program as `dregg-pasta-fq-wraplink::v1` (emitted,
/// checked in, and deliberately NOT served — see the dispatch-table note) —
/// `MinaPhase2Chain.the_chain_air_extends_the_program_air` states both airs as
/// `programAir qLimb absorbProg ++ <pins>` — differing ONLY in the boundary pin blocks:
///
/// | | pin blocks | PIs | outgoing lanes exposed |
/// |---|---|---|---|
/// | `dregg-pasta-fq-wraplink::v1` | 7 (`in(3) ++ absorbed(2) ++ out(2)`) | 224 | **TWO of three** |
/// | `dregg-pasta-fq-chainlink::v1` | 8 (`in(3) ++ out(3) ++ absorbed(2)`) | 256 | **THREE of three** |
///
/// ⚑ **THAT THIRD LANE IS THE WHOLE POINT.** A Poseidon state is three lanes and
/// `MinaPhase2Chain.the_outgoing_lanes_are_registers_4_5_0` names them; `linkPins` pins `last 4` and
/// `last 5` only. So a CHAIN welded on the wraplink would leave each successor's third incoming lane
/// a free prover scalar — `MinaPhase2Chain`'s own words, *"the chain would prove nothing about the
/// transcript."* `chainPins` adds `last 0`, which is why
/// `the_whole_phase2_transcript_folds_into_one_claim` can fold 46 of these over block 539508's real
/// 91-element phase-2 tape and mean something.
///
/// ⚑⚑ **AND SINCE 2026-08-05 IT IS CONSUMED, NOT MERELY SERVED.**
/// `turn::executor::mina_head_verifier::MINA_CHAINLINK_DESCRIPTOR` is THIS name:
/// `LightClientMinaAir.CHAINLINK_VK_LANES` pins this descriptor's fingerprint, so `WRAP_FS_PROVED`
/// attests a permutation of the chain the 46-leaf fold proves, and `check_chain_root_binding`'s weld
/// compares the fold root's whole 96-limb outgoing sponge state instead of 64 of it.
///
/// **The flag day that bought it:** `dregg-mina-lightclient-verify-v1.json` re-emitted (nine
/// `vk_pin` literals moved), and with it the head descriptor's VK — a pre-flag-day
/// `MinaHeadProofWire` no longer verifies, and its `transcript_public_inputs` arity moved 224 → 256.
/// The sub-proof PI-commitment context moved with it
/// (`dregg.mina-lightclient.wraplink-…` → `…chainlink-subproof-pi-commitment.v1`), so an old
/// commitment cannot be re-read under the new program. `mina_head_predicate_vk()` is UNCHANGED (it
/// is a function of the HEAD descriptor's NAME), so cell programs keep their pinned vk.
const MINA_CHAINLINK_TRANSCRIPT_JSON: &str =
    include_str!("../descriptors/by-name/pasta-fq-chainlink.json");

/// ⚑⚑ `dregg-mina-wrap-conjunction::v1` — **THE FINALIZE-CONJUNCTION SUB-PROOF**, served from
/// 2026-08-08 with REFUSAL 15's wiring. Lean-authored
/// (`Dregg2.Circuit.Emit.MinaWrapConjunctionAir.conjunctionDesc`), 2 536 columns, 160 public
/// inputs (ξ ‖ ζ ‖ ζω ‖ r ‖ b0, 32 limbs each), 4 317 constraints. The head's
/// `FINALIZE_XI_B_PROVED`-guarded bind pins this program's fingerprint lane by lane
/// (`LightClientMinaAir.CONJ_VK_LANES`), and `turn`'s verify dispatches this name fail-closed
/// before accepting a head. It was emitted and pinned but served by NOTHING for the two days the
/// refusal was dead code — see the table row's note.
const MINA_WRAP_CONJUNCTION_JSON: &str =
    include_str!("../descriptors/by-name/mina-wrap-conjunction.json");

/// ⚑⚑ `dregg-pasta-fp-chainlink::v1` — **THE PHASE-1 LINK THAT DERIVES `fq_digest`**, served from
/// 2026-08-05. Lean-authored (`Dregg2.Circuit.Emit.MinaPhase1Chain.chainDesc`).
///
/// The SAME machine as the phase-2 chain link above — same 469 columns, same 2 048-instruction
/// program, same eight-block pin layout (`MinaPhase2Chain.chainPins` ITSELF, not a copy:
/// `the_pin_layout_is_the_deployed_one`) — at **`pLimb` instead of `qLimb`** and the **`fp_kimchi`**
/// constants instead of `fq_kimchi`. `MinaWrapVerifierSpongeFp
/// .the_deployed_fq_programs_are_this_one_at_fqParams` proves by `rfl` that the two instruction
/// streams are ONE program at two parameter sets; `pasta_fp_sponge_proves.rs` §12 measures it on the
/// artifacts (2 048/2 048 instruction words identical in fields 0..23; exactly 660 immediates
/// differ).
///
/// ⚑⚑ **WHY IT IS SERVED.** The phase-2 chain's tape begins with `fq_digest`, and until this
/// descriptor **nothing derived it** — so the 46-link fold proved *a tape absorbs to block 539508's
/// published challenges* without proving whose tape. `fq_digest` is phase 1's OUTPUT, and it is
/// this descriptor's link 26 **outgoing lane 1**:
///
/// | | phase-1 (`fp`) link 26 | phase-2 (`fq`) link 0 |
/// |---|---|---|
/// | PI slice | `[4·SK, 5·SK)` — outgoing lane 1 | `[6·SK, 7·SK)` — `absorbed[0]` |
///
/// Those 32 felts are EQUAL, elementwise, at full limb width. ⚑ **No digest, so no birthday
/// bound** — a forger must match all 32 eight-bit limbs of a 254-bit element. A one-felt tie would
/// be `2^31`, below this repository's own ~124-bit bar.
///
/// ⚠ **WHAT IT DOES NOT ESTABLISH.** That the 53 absorbed coordinates are the commitments they
/// claim to be. They enter the transcript as `(x, y)` field elements and nothing here checks a point
/// is on the curve or that `public_comm` commits to the public input; that is the Wrap group check
/// and it bottoms out at the IPA `msm == 0` floor (P10). Nor that the verifier-index digest (tape
/// element 0) is the VK's. Deriving `fq_digest` removes a CARRIER; it does not verify Mina.
const MINA_FP_CHAINLINK_TRANSCRIPT_JSON: &str =
    include_str!("../descriptors/by-name/pasta-fp-chainlink.json");

/// ⚑⚑⚑ `dregg-pasta-fp-absorb::v1` — **THE MINA STATE-HASH STEP**, served from 2026-08-10.
///
/// Lean-authored. One `fp_kimchi` permutation over a PUBLIC incoming sponge state:
/// `perm(state + [x₀, x₁, 0])`, which is Mina's own
/// `state_hash = Poseidon_Fp(salt "MinaProtoState")[previous_state_hash ; state_body_hash]` — two
/// field elements at rate 2, one permutation (`Bridge/MinaStateHashDerive.lean:31`, the daemon's
/// `protocol_state.ml:45-55`). 192 public inputs: `in_state(96) ‖ absorbed(64) ‖ squeeze(32)`, in
/// the sound base-`2^8` limb encoding.
///
/// ⚑ **WHY IT IS SERVED, and it is the same defect the conjunction row records.**
/// `LightClientMinaLinkAir.stateHashBindLeg` has pinned this descriptor's semantic fingerprint
/// (`ABSORB_VK_LANES`) since it was written, and its 54-lane commitment IS this descriptor's
/// public-input vector re-encoded — but `descriptor_by_name` did not resolve the name, so **no
/// consumer could obtain the sub-program the seam names**, and the seam's `state-hash-preimage`
/// port therefore had no cover of any kind. `mina_head_verifier::check_state_hash_preimage_binding`
/// (REFUSAL 17) is the cover; this row is what lets it dispatch.
///
/// ⚠ **WHAT A VERIFYING PROOF OF IT ESTABLISHES, precisely.** That a CONSISTENT quadruple
/// `(state, x₀, x₁, out)` was exhibited — the genuine permutation of the first three lands on the
/// fourth. It does NOT say whose block: what ties the quadruple to a segment is the consumer
/// pinning the incoming state to the `MinaProtoState` salt and the other three blocks to the
/// link proof's own published lanes, which is exactly refusals 17b–17d and not an assumption
/// hidden here.
const MINA_FP_ABSORB_JSON: &str = include_str!("../descriptors/by-name/pasta-fp-absorb.json");

/// ⚑ `dregg-solana-stake-table-fold::v1` — the Solana stake table, FOLDED, one row per entry.
///
/// Lean-COMPILED (`Dregg2.Circuit.Emit.LightClientSolStakeFoldAir.solStakeFoldDesc` =
/// `EffectLower.lowerAir` of the `EffectAir` source `solStakeFoldAir`; no hand-written
/// `VmConstraint2` in that module). Width 44, 12 PIs, 58 constraints, three declared range tables
/// (ids 98 / 93 / 85, the first and third shared with descriptors that already declare them).
///
/// Each row absorbs TWO arity-16 Poseidon2 message blocks of the SAME `state8 ‖ block8` shape —
/// `ROOT_IN8 ‖ voter[0..8]` then `MID8 ‖ [voter8, stake0..3, 0, 0, 0]` — chains `ROOT_OUT` into the
/// next row's `ROOT_IN` through eight `.transition` window gates, and publishes the LAST row's
/// `ROOT_OUT` as the eight-lane table root. The SAME rows drive a four-limb u64 accumulator with
/// boolean carries whose LAST-row value is the published active-stake DENOMINATOR.
///
/// ⚑ THE TOOTH: `dregg-solana-lightclient-verify::v1` used to PIN the denominator and say so in its
/// own docblock — *"a swap to a different validator set with the SAME total active stake is NOT
/// refused by this"*. This descriptor refuses it: the tally pins still accept, and the root moves.
/// ⚑ **AND SINCE 2026-08-04 THE VERIFY RUNG ABSORBED THESE LEGS**, so the refusal is inside the
/// light client's own proof (`solana_lightclient_proves.rs::
/// a_same_tally_swap_is_refused_against_the_pinned_anchor_root`, paired with
/// `a_same_tally_swap_is_arithmetically_perfect` — bit-identical published denominator, moved root).
/// This rung remains served on its own for a consumer that wants only the table commitment.
///
/// ⚠ The commitment is NOT `EpochStakeTable::root`'s SHA-256. That root is dregg-authored
/// (`STAKE_TABLE_ROOT_TAG`) and its SHA-256 shape is 18,049,248 constraints / 12,831,336 columns at
/// 703 live vote accounts against a proved ceiling of 2,131 columns; re-anchoring it onto this
/// Poseidon2 frame is the flag day `LightClientSolStakeFoldAir`'s header names.
const SOLANA_STAKE_TABLE_FOLD_JSON: &str =
    include_str!("../descriptors/by-name/dregg-solana-stake-table-fold-v1.json");

/// The prefix of the depth-GENERAL Merkle-membership descriptor name
/// ([`membership_descriptor_of_depth`] pins `depth{N}` after it).
pub const MEMBERSHIP_GENERAL_NAME_PREFIX: &str =
    "merkle-membership::poseidon2-binary-general-depth";

/// The predicate KINDS the migration dispatches (the scout's map keys).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PredicateKind {
    /// DFA routing (finite-automaton transition predicate).
    Dfa,
    /// Temporal (`≥`/counter) predicate.
    Temporal,
    /// Poseidon2 Merkle set membership (fixed depth-2 4-ary + the depth-general builder).
    MerkleMembership,
    /// Set NON-membership (sorted-neighbor adjacency + quantified absence).
    NonMembership,
    /// Blinded-set / non-revocation membership (sorted tree + accumulator).
    BlindedSet,
    /// Bridge-action / arithmetic-threshold bridge predicate.
    BridgePredicate,
    /// Custom cell-program predicate (`customVmDescriptor2`).
    Custom,
    /// Pedersen-equality — off-STARK Schnorr; NO STARK descriptor.
    PedersenEquality,
}

/// The descriptor AIR-name(s) a predicate kind dispatches to (the scout map). `PedersenEquality`
/// returns `&[]` — it has no STARK descriptor (an off-STARK Schnorr equality). `MerkleMembership`
/// lists the fixed depth-2 name; the depth-general family is reached via
/// [`membership_descriptor_of_depth`] / the [`MEMBERSHIP_GENERAL_NAME_PREFIX`] name form.
pub fn descriptor_names_for_kind(kind: PredicateKind) -> &'static [&'static str] {
    match kind {
        PredicateKind::Dfa => &["dfa-routing-toggle-2state::poseidon2-v1"],
        PredicateKind::Temporal => &["dregg-temporal-predicate-gte::dsl-v1"],
        PredicateKind::MerkleMembership => &[
            "merkle-membership-depth2-4ary::poseidon2-v1",
            // The third-party rung of the predicate stack: binds a hidden `fact_hash` to the
            // presentation-attested `facts_root` and republishes it as the blinded
            // `fact_commitment` the predicate proof pins — the JOIN.
            "dregg-attested-fact-membership::v1",
        ],
        PredicateKind::NonMembership => &[
            "dregg-membership-adjacency-wide::node8-v1",
            "quantified-absence-quotient-accumulator::babybear4-v1",
        ],
        // (The 1-felt sorted-tree non-revocation descriptors are RETIRED — felt-width #11
        // fold-in. The polynomial-accumulator freshness leg remains.)
        PredicateKind::BlindedSet => &["dregg-accumulator-nonrev-emit-v2"],
        // ⚑ `bridge-action-leaf::bridge_action_air_v1` was the FIRST name here and is DELETED
        // (2026-08-07). It was a 28-slot binding-only leaf over a PROVER-CHOSEN tuple with no
        // enforcer anywhere in the tree, REFUSED as a bridge-mint backing by
        // `Dregg2.Circuit.BridgeBindingFromFold`. The sound backing is the re-proved note-spend
        // leaf connected to the leg's published PI-46 `mint_hash`.
        PredicateKind::BridgePredicate => &[
            "dregg-predicate-arith-ge::threshold-v1",
            "dregg-predicate-arith-le::threshold-v1",
            "dregg-predicate-arith-gt::threshold-v1",
            "dregg-predicate-arith-lt::threshold-v1",
            "dregg-predicate-arith-neq::threshold-v1",
            "dregg-predicate-arith-inrange::bounds-v1",
        ],
        PredicateKind::Custom => &["dregg-effectvm-custom-v1"],
        PredicateKind::PedersenEquality => &[],
    }
}

/// **`descriptor_by_name`** — map a predicate-descriptor AIR-name to its [`EffectVmDescriptor2`],
/// or [`None`] on an unrecognized name. The production analog of
/// [`crate::dsl::descriptors::circuit_for_air_name`], in the IR-v2 descriptor world.
///
/// A miss is `None` (fail-closed) — NEVER a stand-in descriptor. A known name whose byte-pinned
/// golden fails to decode is also `None` (fail-closed, not a silent accept); the table-derived
/// cover [`tests::every_static_golden_decodes_and_dispatches`] guarantees every known golden
/// decodes, so a `None` here always means an unknown predicate.
///
/// The depth-GENERAL Merkle-membership family is dispatched by the `merkle-membership::poseidon2-
/// binary-general-depth{N}` name form (parsed to a depth and built by
/// [`membership_descriptor_of_depth`]); every other name maps to a byte-pinned emitted golden.
pub fn descriptor_by_name(name: &str) -> Option<EffectVmDescriptor2> {
    // The depth-general BINARY membership family (built, not parsed).
    if let Some(depth_str) = name.strip_prefix(MEMBERSHIP_GENERAL_NAME_PREFIX) {
        return depth_str
            .parse::<usize>()
            .ok()
            .map(membership_descriptor_of_depth);
    }
    // The depth-general 4-ARY membership family (built, not parsed) — byte-faithful to the deployed
    // `hash_4_to_1`-chained root (`MEMBERSHIP_GENERAL_NAME_PREFIX` is `…-binary-…`, disjoint).
    if let Some(depth_str) = name.strip_prefix(MEMBERSHIP_4ARY_NAME_PREFIX) {
        return depth_str
            .parse::<usize>()
            .ok()
            .map(membership_descriptor_of_depth_4ary);
    }
    // The depth-general 4-ARY BLINDED ring-membership family (built, not parsed) — the depth-8,
    // general-position twin that carries production presentations; PIs `[blinded_leaf, root]`.
    if let Some(depth_str) = name.strip_prefix(BLINDED_4ARY_NAME_PREFIX) {
        return depth_str
            .parse::<usize>()
            .ok()
            .map(blinded_membership_descriptor_of_depth_4ary);
    }
    // The Lean-emitted delegation scope-binding descriptor (parsed once, then cloned).
    if name == DELEGATE_V2_NAME {
        return Some(DELEGATE_CACHE.clone());
    }
    // The fixed Lean-emitted note-spend recursion-leaf descriptor, parsed once and cloned.
    // Fail-closed on a parse/validation refusal (absent from the cache → `None`).
    if name == NOTE_SPEND_LEAF_NAME {
        return NOTE_SPEND_CACHE.clone();
    }

    // Static byte-pinned goldens: served from the parse-once cache (clone ≪ re-parse). A miss is
    // fail-closed `None`; a golden that failed to decode is absent from the cache → also `None`.
    GOLDEN_CACHE.get(name).cloned()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::descriptor_ir2::{
        CHIP_OUT_LANES, CHIP_RATE, CHIP_TUPLE_LEN, LookupSpec, MemBoundaryWitness, TID_P2,
        TID_P2_NARROW, VmConstraint2, check_descriptor2_wellformed, prove_vm_descriptor2,
        verify_vm_descriptor2,
    };
    use crate::field::BabyBear;
    use crate::lean_descriptor_air::{LeanExpr, VmConstraint, VmRow};
    use crate::poseidon2::{hash_2_to_1, hash_4_to_1};
    use std::panic::AssertUnwindSafe;

    /// Every predicate kind's every name.
    const ALL_KINDS: &[PredicateKind] = &[
        PredicateKind::Dfa,
        PredicateKind::Temporal,
        PredicateKind::MerkleMembership,
        PredicateKind::NonMembership,
        PredicateKind::BlindedSet,
        PredicateKind::BridgePredicate,
        PredicateKind::Custom,
        PredicateKind::PedersenEquality,
    ];

    /// DISPATCH SOUNDNESS: every AIR-name every kind lists resolves to a descriptor that decodes,
    /// carries that exact `name`, and passes the structural well-formedness gate
    /// (`check_descriptor2` — the same check prove/verify run first). A wrong/missing arm would
    /// fail HERE, not silently at verify time.
    #[test]
    fn dispatch_names_decode_and_check() {
        for &kind in ALL_KINDS {
            for &name in descriptor_names_for_kind(kind) {
                let desc = descriptor_by_name(name)
                    .unwrap_or_else(|| panic!("{kind:?} name {name:?} must dispatch to Some"));
                assert_eq!(
                    desc.name, name,
                    "{kind:?}: dispatched descriptor name must equal the dispatch key"
                );
                check_descriptor2_wellformed(&desc).unwrap_or_else(|e| {
                    panic!("{kind:?} descriptor {name:?} must be well-formed: {e}")
                });
            }
        }
    }

    /// **THE DISPATCH-SURFACE COVER — DERIVED FROM THE TABLE, NEVER TRANSCRIBED.**
    ///
    /// `dispatch_names_decode_and_check` above walks [`descriptor_names_for_kind`]: a HAND-KEPT
    /// name list that grows only when whoever lands a golden also remembers to extend it. It
    /// reaches 15 of `STATIC_GOLDENS`' rows. The rest — both `faithful-note-spend` planes, the ten
    /// DEPLOYED automatafl leaves, dyck-parse, derivation, bound-presentation, blinded-membership,
    /// presentation-freshness, turn-chain-binding — are deliberately absent from every
    /// `PredicateKind` family (they are re-provable recursion-leaf relations dispatched by exact
    /// name, not predicates), so nothing in this crate ever checked that they decode, self-name, or
    /// dispatch at all. `STATIC_GOLDENS`' own doc-comment named a "round-trip test" that did not
    /// exist: `STATIC_GOLDENS` had exactly ONE reader, the cache.
    ///
    /// That is load-bearing because [`GOLDEN_CACHE`] is built with `filter_map(… .ok())` — a golden
    /// whose bytes stop decoding is SILENTLY DROPPED from the map and `descriptor_by_name` answers
    /// `None` for it. Fail-closed on the wire, but the dispatch surface loses a member with nothing
    /// red; a mis-keyed row is worse still, since dispatch would then serve a DIFFERENT AIR than the
    /// caller named. This is the by-name route the module header already records losing once, when
    /// `predicate-arith` drifted to a 5-wide re-authoring with both Poseidon2 weld legs missing.
    ///
    /// The gate walks the TABLE, so it covers a row the moment that row lands — no list to keep in
    /// step. It also bites on a SHRUNK surface: leg 4 is a TWO-WAY cover between the by-name
    /// goldens this module EMBEDS and the rows the table WIRES, read out of this module's own
    /// source rather than copied, so deleting a row to quiet a red reds here instead.
    ///
    /// AT ITS OWN RESOLUTION: this is a cover of the DISPATCH SURFACE, not of the golden's CONTENT.
    /// A golden re-authored under its own name into a weaker-but-well-formed AIR still passes here
    /// (measured — a `constraints`-truncated `automatafl-legc-n5` is green). The content gate is the
    /// generate-fresh `scripts/check-descriptor-drift.sh` re-derivation from the Lean author plus
    /// the `PROVENANCE.json` stamp; this gate's job is that no member of the surface goes
    /// unexercised, mis-keyed, or silently un-dispatchable.
    /// ⚑ **NO REGISTERED DESCRIPTOR MAY BE A FREE SUBSTITUTION GADGET.**
    ///
    /// `descriptor_by_name` serves the WHOLE registry to an attacker-supplied `predicate` string
    /// (`bridge::present::verify_proof_complete`, reachable from the public `X-Dregg-Proof`
    /// header), and consumers then read FIXED PI INDICES out of the verified result. So a
    /// registered descriptor that (a) declares no tables, no hash sites and no ranges, (b) whose
    /// every constraint is an identity `PiBinding` or a column-constancy `WindowGate`, and (c) has
    /// enough PI slots to cover the read indices, is satisfiable **for any PI vector by a constant
    /// trace** — a forger names it, plants the verifier's own trusted values at exactly the
    /// indices that get read, and every downstream check passes. It is not a proof; it is a
    /// registry hit wearing one.
    ///
    /// `bridge-action-leaf::bridge_action_air_v1` was exactly that row (26 slots, `pi_binding` +
    /// `window_gate` only) and is DELETED (2026-08-07) with the AIR. The per-slot name pin
    /// (`bridge::present::WireSlot`, `sdk::verify::check_bundle_predicates`) is the closure at the
    /// call sites that exist today; THIS gate is the closure at the registry, so a NEW call site
    /// that reads fixed indices cannot re-open the hole by accident, and re-registering such a
    /// descriptor goes red HERE with the reason attached.
    ///
    /// The threshold is 9 PI slots: the presentation reads `FEDERATION_ROOT = 0`,
    /// `REQUEST_PREDICATE_BASE = 1 .. 1 + ACTION_BINDING_WIDTH = 9`, and `PI_ROOT_4ARY = 8`.
    /// ⚑ **THE SPECIMEN — the shape this gate exists to keep out, as a WIRE STRING.**
    ///
    /// A table-free, hash-free, range-free descriptor whose only constraints are identity
    /// `pi_binding`s and per-column `window_gate` constancy, wide enough to carry the fixed PI
    /// indices a presentation consumer reads. This is the shape
    /// `bridge-action-leaf::bridge_action_air_v1` had (at width 26) until it was DELETED 2026-08-07.
    ///
    /// ⚠ It is a JSON literal, PARSED — deliberately not a Rust-authored `VmConstraint2` tree. Law #1
    /// (`circuit-prove/tests/law1_enforcement_gate.rs`) counts hand-built constraint terms as
    /// Rust-authored AIR, and it is right to: a specimen of a bad AIR is still an AIR. The wire string
    /// is the same door every real descriptor comes through, and if the IR grammar moves, the parse
    /// below fails loudly rather than the control silently ceasing to be one.
    const FREE_SUBSTITUTION_SPECIMEN_JSON: &str = "{\"name\":\"deleted-gadget-specimen::free-substitution-shape\",\"ir\":2,\"trace_width\":10,\"public_input_count\":10,\"challenges\":0,\"tables\":[],\"constraints\":[{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":0,\"pi_index\":0},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":1,\"pi_index\":1},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":2,\"pi_index\":2},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":3,\"pi_index\":3},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":4,\"pi_index\":4},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":5,\"pi_index\":5},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":6,\"pi_index\":6},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":7,\"pi_index\":7},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":8,\"pi_index\":8},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":9,\"pi_index\":9},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":0},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":0}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":1}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":2}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":3},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":3}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":4},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":4}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":5},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":5}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":6},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":6}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":7},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":7}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":8},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":8}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":9},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":9}}}}],\"hash_sites\":[],\"ranges\":[]}";

    #[test]
    fn no_registered_descriptor_is_a_free_substitution_gadget() {
        /// The widest fixed PI index any registry consumer reads, exclusive.
        const READ_SURFACE: usize = 9;

        /// THE DETECTOR: is this descriptor satisfiable for an arbitrary PI vector by a constant
        /// trace, and wide enough to carry the read indices?
        fn is_free_substitution_gadget(d: &EffectVmDescriptor2) -> bool {
            d.public_input_count >= READ_SURFACE
                && d.tables.is_empty()
                && d.hash_sites.is_empty()
                && d.ranges.is_empty()
                && d.constraints.iter().all(|c| {
                    matches!(
                        c,
                        VmConstraint2::Base(VmConstraint::PiBinding { .. })
                            | VmConstraint2::WindowGate(_)
                    )
                })
        }

        // ⚠ ANTI-VACUITY (the positive control): the detector FIRES on the shape that was
        // registered until 2026-08-07 — `bridge-action-leaf::bridge_action_air_v1`. Without this,
        // a detector that had silently stopped detecting (a renamed variant, a widened
        // `READ_SURFACE`) would report the same green as a clean registry. The mutation is built
        // CONSTRUCTIVELY and asserted BEFORE the verdict below is read.
        let deleted_gadget = parse_vm_descriptor2(FREE_SUBSTITUTION_SPECIMEN_JSON)
            .expect("the specimen must still parse under the current IR-v2 grammar");
        assert!(
            is_free_substitution_gadget(&deleted_gadget),
            "the detector must fire on the shape this gate exists to keep out — it does not, so a \
             green verdict below means nothing"
        );
        assert!(
            descriptor_by_name("bridge-action-leaf::bridge_action_air_v1").is_none(),
            "the deleted gadget must not be back in the dispatch table"
        );
        assert!(
            descriptor_by_name(&deleted_gadget.name).is_none(),
            "the specimen itself must never be registered"
        );

        let mut offenders = Vec::new();
        for (key, json) in STATIC_GOLDENS {
            let Ok(d) = parse_vm_descriptor2(json) else {
                continue; // Leg 2 of the cover test above already fails on an undecodable row.
            };
            if is_free_substitution_gadget(&d) {
                offenders.push((*key, d.public_input_count));
            }
        }
        assert!(
            offenders.is_empty(),
            "these registered descriptors are FREE SUBSTITUTION GADGETS — table-free, hash-free, \
             range-free, every constraint an identity pin, and wide enough to carry the {READ_SURFACE} \
             fixed PI indices a presentation consumer reads. Any of them substitutes for any other \
             descriptor at a consumer that reads indices out of `descriptor_by_name`'s result: \
             {offenders:?}"
        );
    }

    #[test]
    fn every_static_golden_decodes_and_dispatches() {
        use std::collections::BTreeSet;

        // ---- Leg 1: the table is a FUNCTION — no key served by two different goldens. ----
        let keys: BTreeSet<&str> = STATIC_GOLDENS.iter().map(|(k, _)| *k).collect();
        assert_eq!(
            keys.len(),
            STATIC_GOLDENS.len(),
            "duplicate key in STATIC_GOLDENS — the name would resolve to whichever row the cache \
             happened to insert last"
        );

        // ---- Leg 2: EVERY row decodes, self-names, structurally checks, and is exactly what
        // ---- dispatch serves for that key.
        for (key, json) in STATIC_GOLDENS {
            let decoded = parse_vm_descriptor2(json).unwrap_or_else(|e| {
                panic!(
                    "golden {key}: the byte-pinned JSON must decode — the cache's \
                     `filter_map(… .ok())` would have dropped it silently and dispatch would \
                     answer None: {e}"
                )
            });
            assert_eq!(
                &decoded.name, key,
                "golden {key}: the emitted descriptor names itself {:?} — dispatch would serve a \
                 DIFFERENT AIR than the caller asked for",
                decoded.name
            );
            check_descriptor2_wellformed(&decoded).unwrap_or_else(|e| {
                panic!("golden {key} must pass the structural gate prove/verify run first: {e}")
            });
            let served = descriptor_by_name(key).unwrap_or_else(|| {
                panic!("golden {key} must dispatch to Some — a table row nothing serves")
            });
            assert_eq!(
                served, decoded,
                "golden {key}: dispatch serves something other than its own table row"
            );
        }

        // ---- Leg 3: the parse-once cache DROPS NOTHING. ----
        assert_eq!(
            GOLDEN_CACHE.len(),
            STATIC_GOLDENS.len(),
            "the golden cache is smaller than the table — `filter_map(… .ok())` swallowed a decode \
             failure, so that name now dispatches to None with nothing else red"
        );

        // ---- Leg 4: TWO-WAY COVER, embedded bytes ↔ wired rows. ----
        // Read out of this module's OWN source, so neither side is a second hand-maintained list.
        const SELF_SRC: &str = include_str!("descriptor_by_name.rs");

        /// The `*_JSON` identifiers a block of source REFERENCES, skipping comments and
        /// `::`-qualified paths (a row served from another module's const is not embedded here).
        fn bare_json_idents(block: &str) -> BTreeSet<&str> {
            let mut out = BTreeSet::new();
            for line in block.lines() {
                let code = match line.find("//") {
                    Some(i) => &line[..i],
                    None => line,
                };
                let b = code.as_bytes();
                let mut i = 0usize;
                while i < b.len() {
                    if b[i].is_ascii_alphabetic() || b[i] == b'_' {
                        let s = i;
                        while i < b.len() && (b[i].is_ascii_alphanumeric() || b[i] == b'_') {
                            i += 1;
                        }
                        let tok = &code[s..i];
                        if tok.ends_with("_JSON") && !code[..s].ends_with("::") {
                            out.insert(tok);
                        }
                    } else {
                        i += 1;
                    }
                }
            }
            out
        }

        let table_block = {
            let s = SELF_SRC
                .find("const STATIC_GOLDENS")
                .expect("this module defines STATIC_GOLDENS");
            let rest = &SELF_SRC[s..];
            let e = rest
                .find("\n];")
                .expect("the STATIC_GOLDENS array literal is terminated");
            &rest[..e]
        };
        let wired = bare_json_idents(table_block);

        // The by-name goldens this module EMBEDS. The needle is assembled at runtime so this scan
        // does not match its own source text.
        let needle = format!("include_str!(\"..{}descriptors/by-name/", '/');
        let mut embedded: BTreeSet<&str> = BTreeSet::new();
        let mut cursor = 0usize;
        while let Some(off) = SELF_SRC[cursor..].find(needle.as_str()) {
            let at = cursor + off;
            let head = &SELF_SRC[..at];
            let cs = head.rfind("\nconst ").unwrap_or_else(|| {
                panic!("an embedded by-name golden must bind to a module-level `const`")
            });
            let ident = SELF_SRC[cs + "\nconst ".len()..at]
                .split(':')
                .next()
                .expect("a const declaration names an identifier")
                .trim();
            embedded.insert(ident);
            cursor = at + needle.len();
        }

        // NON-VACUITY: either scan coming back empty (a spelling this leg keys on moved) would
        // make the cover trivially true. Fail loudly instead — re-point the scan, never delete it.
        assert!(
            !embedded.is_empty(),
            "the by-name `include_str!` scan found NOTHING — the spelling it keys on moved. \
             Re-point it; an empty scan makes this leg vacuous."
        );
        assert!(
            !wired.is_empty(),
            "the STATIC_GOLDENS `*_JSON` scan found NOTHING — the table literal's shape moved. \
             Re-point it; an empty scan makes this leg vacuous."
        );
        assert_eq!(
            embedded, wired,
            "the embedded by-name goldens and the STATIC_GOLDENS rows have diverged. A const in \
             `embedded` but not `wired` is a golden this crate ships bytes for and dispatch never \
             serves; one in `wired` but not `embedded` is a row pointing at bytes this module does \
             not embed. Wire it or drop it — do not leave the two lists to drift."
        );
    }

    #[test]
    fn faithful_note_spend_v2_dispatches_exact_hidden_shape() {
        use crate::descriptor_ir2::TID_P2_STATE16;

        const NAME: &str = "faithful-note-spend-v2::exact-note16-root8-hiding";
        let desc = descriptor_by_name(NAME).expect("faithful spend v2 must dispatch");
        assert_eq!(desc.name, NAME);
        assert_eq!(desc.trace_width, 1023);
        assert_eq!(desc.public_input_count, 44);
        check_descriptor2_wellformed(&desc).expect("faithful spend v2 descriptor must check");
        assert_eq!(
            desc.constraints
                .iter()
                .filter(|c| matches!(c, VmConstraint2::Lookup(l) if l.table == TID_P2_STATE16))
                .count(),
            50,
            "owner, commitment, nullifier, leaf, and node sponges must ride the state16 bus"
        );
    }

    #[test]
    fn faithful_note_spend_exact_v3_dispatches_rotated_weld_shape() {
        use crate::descriptor_ir2::TID_P2_STATE16;

        const NAME: &str = "faithful-note-spend-v3-plan::exact-aafi-fns3-rotated-wide-state";

        // ⚑ 2026-07-31, PART TWO. A byte-equality assertion between the registry copy and a
        // SECOND copy under `circuit/staged-descriptors/fnsp-v3/` used to stand here. It went red
        // in the nine-lane re-emit and it was RIGHT: the registry copy moved to `trace_width`
        // 3804 and the staged copy stayed at 3760, because the staged tree had its own emitter
        // (`metatheory/EmitExactNullifierAafiRotatedState.lean`) and its own staging script,
        // NEITHER of which was in `scripts/emit_descriptors.py`'s `EMITTERS`, so a geometry flag
        // day could not reach them. It was regenerated by hand — twice.
        //
        // The second copy is now DELETED, along with its emitter and its staging script. There is
        // one producer: `metatheory/EmitByName.lean`, which emits this exact Lean definition
        // (`ExactNullifierAafiRotatedStateWeld.exactNullifierAafiRotatedStateDescriptor`) into
        // `circuit/descriptors/by-name/faithful-note-spend-exact-v3.json`, is IN `EMITTERS`, and
        // is covered by `PROVENANCE.json` + `check-descriptor-drift.sh`. The assertion is gone
        // because comparing a file to itself is decoration, not because the claim was relaxed:
        // the byte pin now lives in `circuit/tests/exact_nullifier_aafi_staged_ingestion.rs`
        // against an independently reviewed SHA-256, which is a real second source.
        assert!(
            ALL_KINDS
                .iter()
                .all(|kind| !descriptor_names_for_kind(*kind).contains(&NAME)),
            "the additive by-name route must not silently join a live PredicateKind family"
        );

        let desc = descriptor_by_name(NAME).expect("exact FNSP-v3 must dispatch by exact name");
        assert_eq!(desc.name, NAME);
        // `ROTATED_TRACE_WIDTH = V3_TRACE_WIDTH(2442) + 2*(NUM_PRE_LIMBS + 1) + 2*8*WIDE_CARRIERS`
        // = 2442 + 2*188 + 2*504 = 3826 at the 2026-08-01 KEY NONET (`76c3f7b9b` took the region
        // 184 -> 187 and the carriers 62 -> 63; the delta is 2*3 pre-limbs + 2*8 carrier columns
        // = 22). It was 3804 at 184/62, and 3760 at 178/60.
        assert_eq!(desc.trace_width, 3826);
        assert_eq!(desc.public_input_count, 76);
        // 1274 + 3 boundary + 3 window_gate + 2 wide-chip lookups = 1282 — one boundary and one
        // window gate per NEW pre-limb (184/185/186), and one absorption lookup per BLOCK for the
        // new wide carrier. Decomposed at `exact_nullifier_aafi_rotated_trace.rs`'s twin.
        assert_eq!(desc.constraints.len(), 1282);
        assert_eq!(
            desc.tables.iter().map(|table| table.id).collect::<Vec<_>>(),
            vec![0, 9, 1, 84, 85]
        );
        check_descriptor2_wellformed(&desc).expect("exact FNSP-v3 descriptor must check");

        let lookup_counts = |table| {
            desc.constraints
                .iter()
                .filter(|constraint| {
                    matches!(constraint, VmConstraint2::Lookup(lookup) if lookup.table == table)
                })
                .count()
        };
        assert_eq!(lookup_counts(TID_P2_STATE16), 128);
        // 2 blocks x WIDE_NUM_CARRIERS: 2*60 -> 2*62 at the nine-lane epoch, and 2*62 -> 2*63
        // = 126 at the 2026-08-01 KEY NONET (`76c3f7b9b`: `wideNumCarriers` 62 -> 63, the extra
        // carrier absorbing pre-limbs 184..186). One absorption lookup per carrier per block.
        assert_eq!(lookup_counts(TID_P2), 126);
        assert_eq!(lookup_counts(84), 48, "15-bit range-table lookups");
        assert_eq!(lookup_counts(85), 132, "16-bit range-table lookups");
        assert_eq!(
            desc.constraints
                .iter()
                .filter(|constraint| matches!(
                    constraint,
                    VmConstraint2::Base(VmConstraint::PiBinding { .. })
                ))
                .count(),
            76,
            "every public input must have one emitted boundary pin"
        );
    }

    /// STRUCTURAL ANTI-FORK GATE for the WHOLE arithmetic-predicate family: every dispatched
    /// descriptor MUST carry the two Poseidon2 value↔fact weld legs and its Lean-emitted welded
    /// width. This encodes the module doc's claim as a CHECK on the served bytes, not prose — a prose
    /// claim is what let the deployed `≥` file drift to a 5-wide re-authoring with both legs missing
    /// (M13) while every by-name test stayed green, and prose is what carried the siblings' identical
    /// disjoint-set unsoundness as a "follow-up" (M14). If any dispatched predicate descriptor ever
    /// loses a leg, this fails.
    ///
    /// The widths differ by layout: `≥`/`≤`/`>`/`<` = 24, `≠` = 25 (`DIFF_INV`), InRange = 26
    /// (`LO`/`HI`/`DIFF_LO`/`DIFF_HI`).
    #[test]
    fn every_arith_predicate_descriptor_carries_both_poseidon2_weld_legs() {
        use crate::descriptor_ir2::{TID_P2, VmConstraint2};
        use crate::predicate_arith_witness::{PRED_WIDTH, PREDICATE_ARITH_NAME};
        use crate::predicate_comparison_witness::{
            IR_WIDTH, NEQ_WIDTH, OS_WIDTH, PREDICATE_ARITH_GT_NAME, PREDICATE_ARITH_INRANGE_NAME,
            PREDICATE_ARITH_LE_NAME, PREDICATE_ARITH_LT_NAME, PREDICATE_ARITH_NEQ_NAME,
        };
        for (name, width) in [
            (PREDICATE_ARITH_NAME, PRED_WIDTH),
            (PREDICATE_ARITH_LE_NAME, OS_WIDTH),
            (PREDICATE_ARITH_GT_NAME, OS_WIDTH),
            (PREDICATE_ARITH_LT_NAME, OS_WIDTH),
            (PREDICATE_ARITH_NEQ_NAME, NEQ_WIDTH),
            (PREDICATE_ARITH_INRANGE_NAME, IR_WIDTH),
        ] {
            let desc = descriptor_by_name(name).unwrap_or_else(|| panic!("{name} must dispatch"));
            let poseidon2_lookups = desc
                .constraints
                .iter()
                .filter(|c| matches!(c, VmConstraint2::Lookup(l) if l.table == TID_P2))
                .count();
            assert_eq!(
                poseidon2_lookups, 2,
                "the deployed `{name}` descriptor must carry BOTH weld legs (leg 1: hash_fact -> \
                 FACT_HASH, leg 2: hash_4_to_1([FACT_HASH, STATE_ROOT, BLINDING, 0]) -> \
                 FACT_COMMITMENT) — without them the predicate proof does not bind the compared \
                 value to the committed fact"
            );

            // **EVERY SIBLING IS BLINDED, NOT JUST `≥`.** Leg 2's arity tag (the chip tuple's first
            // element) must be 4 — the `hash_4_to_1([fact_hash, state_root, blinding, 0])` absorb —
            // on EVERY descriptor in the family. An arity-2 leg here would be a sibling that welds
            // the value to the fact but emits a DETERMINISTIC commitment: sound, but linkable, and
            // linkable on a surface whose peers are not. Privacy has to be uniform across the family
            // or the odd one out identifies its users.
            let leg2_arity = desc
                .constraints
                .iter()
                .filter_map(|c| match c {
                    VmConstraint2::Lookup(l) if l.table == TID_P2 => l.tuple.first(),
                    _ => None,
                })
                .last()
                .and_then(|e| match e {
                    crate::lean_descriptor_air::LeanExpr::Const(v) => Some(*v),
                    _ => None,
                });
            assert_eq!(
                leg2_arity,
                Some(4),
                "`{name}`'s weld leg 2 must be the ARITY-4 blinded absorb \
                 (hash_4_to_1([FACT_HASH, STATE_ROOT, BLINDING, 0])), not the arity-2 unblinded one \
                 — every sibling in the family must be unlinkable, not just `≥`"
            );
            assert_eq!(
                desc.trace_width, width,
                "the deployed `{name}` descriptor must be the Lean-emitted welded shape"
            );
        }
    }

    /// THE DYCK LOADER FLIP: `dregg-dyck-parse-v1` dispatches to the Lean-emitted, byte-pinned
    /// golden (`DyckStackEmit.dyckParseDesc`), decodes well-formed, and carries the emitted shape
    /// (24 wide after the E7 narrowing, 4 PIs, the two NARROW-bus Poseidon2 chip lookups — the
    /// arity-4 entry hash and the arity-2 running-hash step). A regression to the hand-authored
    /// Rust AIR (23 wide, zero lookups) fails HERE, not silently at verify time.
    #[test]
    fn dyck_parse_dispatches_to_the_lean_emitted_golden() {
        let desc = descriptor_by_name("dregg-dyck-parse-v1")
            .expect("the Dyck parse descriptor must dispatch");
        assert_eq!(desc.name, "dregg-dyck-parse-v1");
        assert_eq!(
            desc.trace_width, 24,
            "the Lean-emitted width (23 base + ACC); E7 narrowed both chip lookups, deleting the \
             two trailing 7-lane blocks [24, 38)"
        );
        assert_eq!(desc.public_input_count, 4);
        check_descriptor2_wellformed(&desc).expect("the emitted Dyck descriptor is well-formed");
        let arities: Vec<i64> = desc
            .constraints
            .iter()
            .filter_map(|c| match c {
                VmConstraint2::Lookup(l) if l.table == TID_P2_NARROW => match l.tuple.first() {
                    Some(LeanExpr::Const(v)) => Some(*v),
                    _ => None,
                },
                _ => None,
            })
            .collect();
        assert_eq!(
            arities,
            vec![4, 2],
            "the entry-hash (arity 4) and running-hash (arity 2) chip lookups, in emit order"
        );
        assert!(
            !desc
                .constraints
                .iter()
                .any(|c| matches!(c, VmConstraint2::Lookup(l) if l.table == TID_P2)),
            "no WIDE-bus chip lookup may survive the E7 narrowing"
        );
    }

    /// PedersenEquality has NO descriptor (off-STARK) — its name list is empty and no
    /// pedersen-shaped name silently resolves.
    #[test]
    fn pedersen_equality_has_no_descriptor() {
        assert!(descriptor_names_for_kind(PredicateKind::PedersenEquality).is_empty());
        assert!(descriptor_by_name("pedersen-equality").is_none());
        assert!(descriptor_by_name("schnorr-equality").is_none());
    }

    /// A MISS is `None` — never a stand-in, never a silent accept.
    #[test]
    fn unknown_name_is_none() {
        assert!(descriptor_by_name("no-such-air").is_none());
        assert!(descriptor_by_name("").is_none());
        assert!(descriptor_by_name("merkle-membership").is_none()); // prefix-only, no depth
        // a wrong depth suffix on the general family is a miss, not a panic.
        assert!(
            descriptor_by_name("merkle-membership::poseidon2-binary-general-depthNaN").is_none()
        );
    }

    /// The depth-GENERAL name form dispatches to exactly [`membership_descriptor_of_depth`].
    #[test]
    fn depth_general_membership_dispatches() {
        for depth in [2usize, 4, 8] {
            let name = format!("{MEMBERSHIP_GENERAL_NAME_PREFIX}{depth}");
            let via_dispatch = descriptor_by_name(&name).expect("general membership dispatches");
            assert_eq!(via_dispatch, membership_descriptor_of_depth(depth));
            assert_eq!(via_dispatch.name, name);
        }
    }

    // ---- The depth-2 4-ary Merkle-membership golden witness (mirrors merkle_membership_emit_gate). ----
    const LEAF: usize = 0;
    const SIB0A: usize = 1;
    const SIB0B: usize = 2;
    const SIB0C: usize = 3;
    const PARENT0: usize = 4;
    const CUR1: usize = 5;
    const SIB1A: usize = 6;
    const SIB1B: usize = 7;
    const SIB1C: usize = 8;
    const PARENT1: usize = 9;
    /// 10 after the E7 narrowing (the 2 x 7 chip-lane columns are gone).
    const MEMBERSHIP_WIDTH: usize = 10;

    fn honest_merkle_row(
        leaf: BabyBear,
        s0: [BabyBear; 3],
        s1: [BabyBear; 3],
    ) -> (Vec<BabyBear>, BabyBear) {
        let parent0 = hash_4_to_1(&[leaf, s0[0], s0[1], s0[2]]);
        let root = hash_4_to_1(&[parent0, s1[0], s1[1], s1[2]]);
        let mut row = vec![BabyBear::ZERO; MEMBERSHIP_WIDTH];
        row[LEAF] = leaf;
        row[SIB0A] = s0[0];
        row[SIB0B] = s0[1];
        row[SIB0C] = s0[2];
        row[PARENT0] = parent0;
        row[CUR1] = parent0;
        row[SIB1A] = s1[0];
        row[SIB1B] = s1[1];
        row[SIB1C] = s1[2];
        row[PARENT1] = root;
        (row, root)
    }

    fn rejects(desc: &EffectVmDescriptor2, trace: &[Vec<BabyBear>], pis: &[BabyBear]) -> bool {
        let r = std::panic::catch_unwind(AssertUnwindSafe(|| {
            let proof =
                prove_vm_descriptor2(desc, trace, pis, &MemBoundaryWitness::default(), &[])?;
            verify_vm_descriptor2(desc, &proof, pis)
        }));
        matches!(r, Err(_) | Ok(Err(_)))
    }

    /// REAL PROVE → VERIFY through the dispatched depth-2 Merkle-membership descriptor
    /// (honest accept), plus a forged-root REJECT (non-vacuous: the honest witness is accepted).
    #[test]
    fn merkle_membership_dispatch_proves_and_verifies() {
        let name = "merkle-membership-depth2-4ary::poseidon2-v1";
        let desc = descriptor_by_name(name).expect("dispatch");
        let leaf = BabyBear::new(1001);
        let s0 = [
            BabyBear::new(2002),
            BabyBear::new(3003),
            BabyBear::new(4004),
        ];
        let s1 = [
            BabyBear::new(5005),
            BabyBear::new(6006),
            BabyBear::new(7007),
        ];
        let (row, root) = honest_merkle_row(leaf, s0, s1);
        let trace = vec![row.clone(), row.clone(), row.clone(), row];

        let proof =
            prove_vm_descriptor2(&desc, &trace, &[root], &MemBoundaryWitness::default(), &[])
                .expect("honest membership must prove through the dispatched descriptor");
        verify_vm_descriptor2(&desc, &proof, &[root]).expect("honest proof must verify");

        // forged root → the root pin is UNSAT.
        assert!(
            rejects(&desc, &trace, &[root + BabyBear::ONE]),
            "a forged claimed root must be REJECTED"
        );
    }

    /// CROSS-DESCRIPTOR REJECT: a proof minted for the depth-2 Merkle golden does NOT verify
    /// against a DIFFERENT dispatched descriptor (the DFA one) — a wrong dispatch arm cannot
    /// launder a proof.
    #[test]
    fn proof_does_not_verify_against_wrong_descriptor() {
        let merkle = descriptor_by_name("merkle-membership-depth2-4ary::poseidon2-v1").unwrap();
        let dfa = descriptor_by_name("dfa-routing-toggle-2state::poseidon2-v1").unwrap();
        let leaf = BabyBear::new(1001);
        let s0 = [
            BabyBear::new(2002),
            BabyBear::new(3003),
            BabyBear::new(4004),
        ];
        let s1 = [
            BabyBear::new(5005),
            BabyBear::new(6006),
            BabyBear::new(7007),
        ];
        let (row, root) = honest_merkle_row(leaf, s0, s1);
        let trace = vec![row.clone(), row.clone(), row.clone(), row];
        let proof = prove_vm_descriptor2(
            &merkle,
            &trace,
            &[root],
            &MemBoundaryWitness::default(),
            &[],
        )
        .expect("prove");
        // Verifying the merkle proof under the DFA descriptor must fail (different AIR set / PIs).
        assert!(
            verify_vm_descriptor2(&dfa, &proof, &[root]).is_err(),
            "a merkle proof must NOT verify against the DFA descriptor"
        );
    }

    /// TAMPERED GOLDEN: a byte-mutated descriptor JSON either fails to decode OR decodes to a
    /// descriptor that rejects the honest proof — a drifted golden never silently accepts.
    #[test]
    fn tampered_golden_does_not_silently_accept() {
        // Mutate the merkle golden's root-pin `pi_index` (0 → 9, out of range) — decode-or-check fails.
        let bad = MERKLE_MEMBERSHIP_DEPTH2_JSON.replace(
            "\"pi_binding\",\"row\":\"first\",\"col\":9,\"pi_index\":0",
            "\"pi_binding\",\"row\":\"first\",\"col\":9,\"pi_index\":9",
        );
        assert_ne!(
            bad, MERKLE_MEMBERSHIP_DEPTH2_JSON,
            "the mutation must change the golden"
        );
        let decoded = parse_vm_descriptor2(&bad);
        if let Ok(d) = decoded {
            // decoded — but pi_index 9 exceeds public_input_count 1, so well-formedness fails.
            assert!(
                check_descriptor2_wellformed(&d).is_err(),
                "a golden with an out-of-range pi_index must fail the well-formedness gate"
            );
        }
    }

    /// Keep the hand-built shape aligned with the golden decode: the chip4 tuple helper the emit
    /// gate uses produces the exact chip tuple shape (a guard against a silent chip-arity drift in
    /// the dispatched membership descriptor).
    ///
    /// The INTENT — "this golden really does perform two arity-4 child→parent chip lookups" — is
    /// unchanged; the BUS moved. The E7 by-name narrowing (`9648759c79`) re-emitted
    /// `merkle-membership-depth2` onto the NARROW chip bus (`poseidon2narrow`, wire 8 =
    /// `TID_P2_NARROW`): the same two lookups, tail-truncated of their 7 trailing output lanes
    /// (`trace_width 24 → 10`), served by the SAME chip rows. So the tooth counts the lookups on
    /// the bus the descriptor NOW uses AND pins the bus identity both ways — a re-widening back to
    /// `TID_P2`, or a third bus, fails here instead of silently passing with a count of zero.
    #[test]
    fn merkle_golden_has_two_arity4_chip_lookups() {
        use crate::descriptor_ir2::TID_P2_NARROW;
        let d = descriptor_by_name("merkle-membership-depth2-4ary::poseidon2-v1").unwrap();
        let chip: Vec<&LookupSpec> = d
            .constraints
            .iter()
            .filter_map(|c| match c {
                VmConstraint2::Lookup(l) if l.table == TID_P2_NARROW => Some(l),
                _ => None,
            })
            .collect();
        assert_eq!(
            chip.len(),
            2,
            "depth-2 = two child→parent chip lookups, on the E7 NARROW chip bus"
        );
        // BUS IDENTITY: the narrowing is a cutover, not an addition — NO lookup rides the wide
        // 25-tuple `TID_P2` bus any more. Together with the count above this pins exactly two chip
        // lookups in total, and pins which bus carries them.
        assert_eq!(
            d.constraints
                .iter()
                .filter(|c| matches!(c, VmConstraint2::Lookup(l) if l.table == TID_P2))
                .count(),
            0,
            "the E7-narrowed golden carries NO wide-bus chip lookup"
        );
        for l in chip {
            assert_eq!(l.tuple[0], LeanExpr::Const(4), "arity-4 tag");
            // The narrow tuple is `[arity, ins, out0]`: the input block is still CHIP_RATE wide,
            // and exactly the 7 trailing output lanes of the wide CHIP_TUPLE_LEN shape are gone
            // (a pure tail truncation — no input column was renumbered).
            assert_eq!(l.tuple.len(), 1 + CHIP_RATE + 1);
            assert_eq!(
                l.tuple.len(),
                CHIP_TUPLE_LEN - (CHIP_OUT_LANES - 1),
                "the narrow bus drops exactly the wide tuple's trailing output lanes"
            );
        }
        // the single root pin.
        let pins = d
            .constraints
            .iter()
            .filter(|c| {
                matches!(
                    c,
                    VmConstraint2::Base(VmConstraint::PiBinding {
                        row: VmRow::First,
                        ..
                    })
                )
            })
            .count();
        assert_eq!(pins, 1);
    }

    // ---- A second, NON-membership predicate kind proven end-to-end through the dispatch: the
    //      toggle-DFA routing golden (mirrors dfa_routing_emit_gate's honest witness). ----
    const DFA_CURRENT: usize = 0;
    const DFA_SYMBOL: usize = 1;
    const DFA_NEXT: usize = 2;
    const DFA_ENTRY_HASH: usize = 3;
    const DFA_RUNNING_HASH: usize = 4;
    const DFA_IS_FIRST: usize = 5;
    const DFA_ACC: usize = 7;
    /// E7 narrowed both chip lookups onto the NARROW bus (`DfaRoutingEmit.lean`), deleting the two
    /// trailing 7-lane blocks `[8, 22)`. Pure tail truncation — no semantic column moved.
    const DFA_WIDTH: usize = 8;

    /// Build the honest 4-row toggle-DFA routing witness (`step(s,y) = s XOR y`): start state, a
    /// symbol at row 0, self-loops after, with the genuine `hash_4_to_1` entry hashes and the
    /// `hash_2_to_1` running-hash chain. Returns `(trace, pis = [initial, final, seed, route])`.
    fn dfa_honest(start: u32, sym0: u32, seed: BabyBear) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
        let symbols = [sym0, 0, 0, 0];
        let mut cur = start;
        let mut running = seed;
        let mut rows: Vec<Vec<BabyBear>> = Vec::with_capacity(4);
        for (i, &sym) in symbols.iter().enumerate() {
            let nxt = cur ^ sym;
            let entry = hash_4_to_1(&[
                BabyBear::new(cur),
                BabyBear::new(sym),
                BabyBear::new(nxt),
                BabyBear::ZERO,
            ]);
            let acc = running;
            running = hash_2_to_1(acc, entry);
            let mut row = vec![BabyBear::ZERO; DFA_WIDTH];
            row[DFA_CURRENT] = BabyBear::new(cur);
            row[DFA_SYMBOL] = BabyBear::new(sym);
            row[DFA_NEXT] = BabyBear::new(nxt);
            row[DFA_ENTRY_HASH] = entry;
            row[DFA_RUNNING_HASH] = running;
            row[DFA_IS_FIRST] = if i == 0 {
                BabyBear::ONE
            } else {
                BabyBear::ZERO
            };
            row[DFA_ACC] = acc;
            rows.push(row);
            cur = nxt;
        }
        let pis = vec![
            BabyBear::new(start),
            BabyBear::new(cur),
            seed,
            rows[3][DFA_RUNNING_HASH],
        ];
        (rows, pis)
    }

    /// REAL PROVE → VERIFY through the dispatched DFA-routing descriptor (a DISTINCT, non-membership
    /// predicate kind). Honest accept + a FORBIDDEN-edge reject (`0 --sym1--> 0`, violating
    /// `step(0,1)=1`) — non-vacuous: the honest route is accepted.
    #[test]
    fn dfa_routing_dispatch_proves_and_verifies() {
        let desc = descriptor_by_name("dfa-routing-toggle-2state::poseidon2-v1").expect("dispatch");
        let (trace, pis) = dfa_honest(0, 1, BabyBear::new(0x51D5));
        let proof = prove_vm_descriptor2(&desc, &trace, &pis, &MemBoundaryWitness::default(), &[])
            .expect("honest DFA route must prove through the dispatched descriptor");
        verify_vm_descriptor2(&desc, &proof, &pis).expect("honest DFA proof must verify");

        // Forbidden edge: force NEXT = 0 at row 0 where step(0,1) = 1 → the transition Gate is UNSAT.
        let (mut bad, bad_pis) = dfa_honest(0, 1, BabyBear::new(0x51D5));
        bad[0][DFA_NEXT] = BabyBear::ZERO;
        assert!(
            rejects(&desc, &bad, &bad_pis),
            "a forbidden DFA edge (step(0,1)=1 routed to 0) must be REJECTED"
        );
    }
}
