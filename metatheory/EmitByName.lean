/-
# EmitByName — the byte source for the WHOLE `circuit/descriptors/by-name/` surface.

Prints one `<filename>\t<emitVmJson2 descriptor>` line per checked-in by-name descriptor, so
`scripts/emit_descriptors.py` can regenerate every one of them FROM THE VERIFIED LEAN EMISSION —
the same snapshot→emit→diff treatment the main `circuit/descriptors/*.json` set already gets.

    lake env lean --run EmitByName.lean

## Why this file exists

`by-name/` is the set `circuit/src/descriptor_by_name.rs::descriptor_by_name()` — the production
predicate-dispatch registry — serves to `bridge/` and `wire/` at verify time. Until this emitter,
NOTHING regenerated it: `emit_descriptors.py`'s coverage check walked `DESC.iterdir()` filtered on
`p.is_file()`, and `by-name/` is a DIRECTORY, so the entire deployed dispatch surface was silently
exempt from the drift gate. The gate's snapshot→emit→diff therefore left `by-name/` byte-identical
on both sides — an unconditional PASS for any content whatsoever. The real chain had an UNGATED
hand-transcription hop in it:

    Lean descriptor ==(#guard)== Lean golden ==(HAND TRANSCRIPTION, ungated)== disk bytes

That hop is where `predicate-arith.json` drifted from its 24-wide welded Lean author down to a
5-wide re-authoring with the two Poseidon2 value↔fact weld legs missing — a CRITICAL, deployed,
demonstrated forgery (the compared value and the committed fact had disjoint constraint sets, so a
prover could satisfy `value ≥ threshold` on a value of its choosing while presenting the honest
verifier-expected `fact_commitment` for an unrelated value). This emitter deletes the hop.

Law #1: the constraints are AUTHORED in the `Dregg2/Circuit/Emit/*` modules (proved there, with
their `emitVmJson2` `#guard`s); this file only SERIALIZES them. Rust interprets; Rust authors
nothing. A descriptor reachable from here can never again disagree with its Lean author, because
the artifact IS the Lean author's output.
-/
import Dregg2.Circuit.Emit.MinaPhase1Chain
import Dregg2.Circuit.Emit.AccumulatorNonRevocationEmit
import Dregg2.Circuit.Emit.AdjacencyMembershipEmit
import Dregg2.Circuit.Emit.AdjacencyMembershipWideEmit
import Dregg2.Circuit.Emit.AttestedFactMembershipEmit
import Dregg2.Circuit.Emit.AttestedAutomatonWeld8
import Dregg2.Circuit.Emit.AutomataflResolveEmit
import Dregg2.Circuit.Emit.AutomataflStepEmit
import Dregg2.Circuit.Emit.AutomataflNGenGolden
import Dregg2.Circuit.Emit.AutomataflLegCEmit
import Dregg2.Circuit.Emit.AutomataflResolveMarksCapstone
import Dregg2.Circuit.Emit.AutomataflStepMarksGolden
import Dregg2.Circuit.Emit.BlindedMembershipEmit
import Dregg2.Circuit.Emit.BlindedMembershipWideEmit
import Dregg2.Circuit.Emit.BoundPresentationEmit
import Dregg2.Circuit.Emit.DerivationEmit
import Dregg2.Circuit.Emit.DfaRoutingEmit
import Dregg2.Circuit.Emit.DfaRoutingGeneralEmit
import Dregg2.Circuit.Emit.SolvencyLeafEmit
import Dregg2.Circuit.Emit.DecoLeafEmit
import Dregg2.Circuit.Emit.CaveatAdmissionEmit
import Dregg2.Circuit.Emit.DfaRoutingTableRoute8
import Dregg2.Circuit.Emit.AttestedAutomatonRoute8
import Dregg2.Circuit.Emit.TupleBindingEmit
import Dregg2.Circuit.Emit.DfaRoutingTableEmit
import Dregg2.Circuit.Emit.DyckStackEmit
import Dregg2.Circuit.Emit.GuardedHidingSpanWideBlindEmit
import Dregg2.Circuit.Emit.EffectVmEmitTurnChainBinding
import Dregg2.Circuit.Emit.ExactNullifierAafiRotatedStateWeld
import Dregg2.Circuit.Emit.FaithfulNoteSpendDescriptorPlan
import Dregg2.Circuit.Emit.FieldDeltaRangeEmit
import Dregg2.Circuit.Emit.MerkleMembership4aryEmit
import Dregg2.Circuit.Emit.MerkleMembership4aryWideEmit
import Dregg2.Circuit.Emit.MerkleMembershipEmit
import Dregg2.Circuit.Emit.MinaFixtureEmit
import Dregg2.Circuit.Emit.LightClientMinaAir
import Dregg2.Circuit.Emit.LightClientMinaLinkAir
import Dregg2.Circuit.Emit.MinaBodyPreimageBitsAir
import Dregg2.Circuit.Emit.MinaBodyHashRelimbAir
import Dregg2.Circuit.Emit.MinaPreambleLegsAir
import Dregg2.Circuit.Emit.LightClientSolStakeFoldAir
import Dregg2.Circuit.Emit.NoteSpendingLeafEmit
import Dregg2.Circuit.Emit.Poseidon2HashEmit
import Dregg2.Circuit.Emit.PastaMsmWindowed
import Dregg2.Circuit.Emit.PastaMsmSliced
import Dregg2.Circuit.Emit.PastaFieldSound
import Dregg2.Circuit.Emit.PastaAddSubSound
import Dregg2.Circuit.Emit.PastaCurveSound
import Dregg2.Circuit.Emit.PastaLadderThread
import Dregg2.Circuit.Emit.MinaAccumulatorAir
import Dregg2.Circuit.Emit.MinaAccumulatorSrsDemo
-- ⚑ ROUTED as of 2026-08-05 (it spent one commit imported-but-withheld while its row-local layout
-- was threaded). Two rows: the threaded conjunction and its unthreaded twin.
import Dregg2.Circuit.Emit.MinaWrapConjunctionAir
import Dregg2.Circuit.Emit.MinaWrapVerifierAir
import Dregg2.Circuit.Emit.MinaWrapVerifierProgram
import Dregg2.Circuit.Emit.MinaPhase2Chain
-- ⚑ 2026-08-05 — THE ELEVEN HAND-DRIVEN ROWS, ROUTED. Every descriptor below was checked into
-- `by-name/` by a one-off `lake env lean --run` driver (`EmitPastaAlu.lean fqround|fqabsorb|fqlink`,
-- `EmitLcTmp.lean`, and per-lane redirects) while `EmitByName.lean` itself could not run — its
-- length pin said 92 against 91 rows, so `lake env lean --run EmitByName.lean` died on `rfl` and
-- the WHOLE by-name surface was unemittable by anybody. Each lane then hand-transcribed its own
-- file, which is precisely how a served descriptor stops being the Lean object (measured today:
-- `dark-bazaar-private-poa-settlement` served 1330 constraints where Lean authors 984).
-- Routing them here makes their bytes re-derivable from the ONE emit that produces every other
-- by-name artifact.
import Dregg2.Circuit.Emit.MinaWrapVerifierSponge
import Dregg2.Circuit.Emit.MinaBlockFqTranscript
import Dregg2.Circuit.Emit.MinaWrapCommitStages
import Dregg2.Circuit.Emit.MinaWrapXiEndoLift
import Dregg2.Circuit.Emit.MinaWrapXiAggregateMsm
import Dregg2.Circuit.Emit.PredicatesArithmeticEmit
import Dregg2.Circuit.Emit.PredicatesGtEmit
import Dregg2.Circuit.Emit.PredicatesInRangeEmit
import Dregg2.Circuit.Emit.PredicatesLeEmit
import Dregg2.Circuit.Emit.PredicatesLtEmit
import Dregg2.Circuit.Emit.PredicatesNeqEmit
import Dregg2.Circuit.Emit.PresentationEmit
import Dregg2.Circuit.Emit.QuantifiedAbsenceEmit
import Dregg2.Circuit.Emit.TemporalPredicateEmit
-- The four STARK-ified peer-chain lightclient verification AIRs (bridge tree). Each emits its
-- consensus-verification as an `EffectVmDescriptor2` carrying the chain's no-forgery obligation
-- (`eth_no_forgery` / `tmNoForgery` / `sol_no_forgery` / `mid_no_forgery`); routing them here puts
-- their byte-pinned descriptors under the same Lean-authored drift gate as every other by-name
-- artifact, so a dregg node emits + proves them from the VERIFIED Lean emission (the prerequisite
-- for the gnark peer-wrap → on-chain DreggPeerRegistry flow).
import Dregg2.Circuit.Emit.LightClientEthAir
import Dregg2.Circuit.Emit.LightClientTendermintAir
import Dregg2.Circuit.Emit.LightClientSolanaAir
import Dregg2.Circuit.Emit.LightClientMidnightAir
import Dregg2.Crypto.PrivateGraphRewriteDescriptor
import Dregg2.Games.PrivateQuestGraphDescriptor
import Dregg2.Crypto.PrivateGraphRewriteCellDescriptor
import Dregg2.Games.PrivatePreferenceDescriptor
import Dregg2.Games.PrivatePreferenceCellDescriptor
import Dregg2.Games.DescentCensusDescriptor
import Dregg2.Circuit.Emit.ShieldedWholeNoteSwapSubstrateDescriptor
import Dregg2.Circuit.Emit.ShieldedSpendDescriptor
import Dregg2.Circuit.Emit.ShieldedWideValueLinkDescriptor
import Dregg2.Circuit.ShieldedValueRangeDischarge
import Dregg2.Games.PrivateRaidAssignmentDescriptor
import Dregg2.Games.PrivateShuffleDescriptor
import Dregg2.Games.PrivateShuffleFairDescriptor
import Market.DarkBazaarPrivateDescriptor
import Market.DarkBazaarPrivatePoaSettlementDescriptor
-- The fixed q0/N8 exact-public BFV NTT butterfly stage descriptors (`stage{0,1,2}Descriptor`, the
-- three four-row per-stage LogUp relations). Emitted here so `by-name/*bfv*butterfly*stage*-exact-
-- public.json` are drift-checked from their Lean author, not left as un-reproduced checked-in bytes.
import Market.PrivateBookBfvExactPublicConsumer
import Market.DarkAmmPrivateDescriptor
import Market.PrivateBookBfvSliceDescriptor
import Market.PrivateBookBfvButterflyAir
-- ⚑ 2026-08-06 — THE NINE TEST-ONLY DESCRIPTORS, ROUTED. Seven modules below author nine
-- `EffectVmDescriptor2`s that had NO checked-in artifact at all, so fifteen sites under
-- `circuit-prove/tests/` carried the emitted JSON as a HAND-COPIED `const … &str = r#"…"#`
-- literal instead of `include_str!` of a file. That is the same ungated hand-transcription hop
-- this emitter's header disowns, one medium over: the Lean `#guard` pins the bytes, the Rust
-- literal pins the bytes, and NOTHING re-derives one from the other — so a Lean change moves the
-- guard and the fifteen Rust copies stay green against their own stale transcription. Six of the
-- fifteen are `_emit_gate`/`_audit` DUPLICATE pairs of each other, which is the transcription
-- hazard doubled: two copies of one descriptor that can drift apart with nothing red.
-- Routing them here mints the artifact, and the goldens become `include_str!` of it.
import Dregg2.Circuit.Emit.PredicatesRelationalCompoundEmit
import Dregg2.Circuit.Emit.EffectVmEmitIvcStateTransition
import Dregg2.Circuit.Emit.EffectActionBindingEmit
import Dregg2.Circuit.Emit.GarbledEvalEmit
import Dregg2.Circuit.Emit.FoldEmit
import Dregg2.Circuit.Emit.MultiStepChainEmit
import Dregg2.Circuit.Emit.CommittedThresholdEmit

open Dregg2.Circuit.DescriptorIR2 (EffectVmDescriptor2 emitVmJson2)

/-- The by-name routing table: `(checked-in filename, the Lean descriptor that authors it)`.

Each entry is the SOLE authorship of its artifact. Adding a by-name descriptor without adding it
here is a routing gap `emit_descriptors.py` REFUSES (its coverage check recurses into `by-name/`
and fails on any checked-in file no emitter reproduces) — so this table cannot silently fall
behind the directory.

Three notes the mechanical reader needs:
* `blindedMembership4aryDesc` is depth-PARAMETERIZED in Lean; the two checked-in artifacts are its
  `depth := 2` and `depth := 8` instances. (The constraint block is depth-uniform — only the `name`
  field differs — but both are checked in, so both are emitted.)
* `NoteSpendingLeafEmit.noteSpendLeafDescFixed` is served: six last-row boundaries repair
  the earlier 27-constraint artifact. Width149 and the seven PIs stay unchanged, but the
  canonical descriptor bytes (and derived verification key) change. The original descriptor
  remains a theorem-level counterexample; matching its name alone would miss the repair.
* `mina-fixture.json` is EMITTED but not DISPATCHED, and never will be: it is not a predicate
  descriptor. `circuit/src/bin/mina_stark_fixture.rs` `include_str!`s it directly to mint the
  fixture proof `bridge/mina-zkapp` verifies. It is routed here for the same reason everything
  else is — so the artifact is RE-DERIVED from `MinaFixtureEmit.lean` on every drift run rather
  than transcribed once. (It replaced a hand-written Rust AIR; see HORIZONLOG E4.)
* `dyck-parse.json` is EMITTED but not yet DISPATCHED: `descriptor_by_name.rs` has no arm for it,
  because `circuit/src/dsl/dyck_stack.rs` still hand-builds the IR-v1 `CircuitDescriptor` the Dyck
  prover/tamper suite drives. It is registered here anyway — routing it through this table is what
  makes the byte-pin RE-DERIVABLE and puts the Dyck circuit under the drift gate (law #1's spine);
  the loader flip is the follow-up. The routing table is a superset of the dispatch table by
  design: the coverage check fails on a checked-in file NO emitter reproduces, never on an emitted
  descriptor Rust does not yet serve. -/
def byNameDescriptors : List (String × EffectVmDescriptor2) :=
  [ ("accumulator-nonrev.json",
      Dregg2.Circuit.Emit.AccumulatorNonRevocationEmit.accumulatorNonRevDesc)
  -- ⚑ node8 CUTOVER: `adjacency-membership.json` (`adjacencyDesc`) is RETIRED — its per-level
  -- node was `chipLookupTupleNarrow [left, right] par`, the arity-2 NARROW bus binding `out0`
  -- alone, so every interior node, both leaf PIs and the root PI committed at ~31 bits and were
  -- collidable at 2^15.45 (`circuit/tests/adjacency_forge_tooth.rs` exhibits the forge: a MEMBER
  -- of the committed set passes the sorted-set NON-membership gate). The narrow `def` survives in
  -- `AdjacencyMembershipEmit` ONLY as the object the wide module's anti-masquerade tooth
  -- quantifies over (`narrowNode2Lane0`, `interior_forge_narrow_admits_wide_refuses`) and as the
  -- subject of the `AdjacencyMembershipRefine`/`Rung2` refinement rungs — you cannot state "the
  -- old fold admits this" without the old fold. It is emitted nowhere.
  , ("adjacency-membership-wide.json",
      Dregg2.Circuit.Emit.AdjacencyMembershipWideEmit.adjacencyWideDesc)
  , ("attested-fact-membership.json",
      Dregg2.Circuit.Emit.AttestedFactMembershipEmit.attestedFactMembershipDesc)
  -- The 8-felt WELDED attested-automaton descriptor (`AttestedAutomatonWeld8.lean` §3): the
  -- `.read` map op's root group is eight distinct columns (3..10), each pinned to a public input on
  -- row 0 and threaded by a constancy window. The deployed map-ops table forces all eight lanes
  -- through its arity-16 `node8` chain; the Lean `MapOp.holdsAt` denotation still reads lane 0
  -- only (that file's §3a), so this route ships the wire, not yet the Lean refinement.
  , ("attested-automaton-map-committed-weld8-v1.json",
      Dregg2.Circuit.Emit.AttestedAutomatonWeld8.weldInstance)
  , ("automatafl-resolve.json",
      Dregg2.Circuit.Emit.AutomataflResolveEmit.automataflResolveDesc)
  , ("automatafl-step.json",
      Dregg2.Circuit.Emit.AutomataflStepEmit.automataflStepDesc)
  , ("automatafl-step-n11.json",
      Dregg2.Circuit.Emit.AutomataflNGenGolden.automataflStepDescN11)
  , ("automatafl-resolve-n11.json",
      Dregg2.Circuit.Emit.AutomataflNGenGolden.automataflResolveDescN11)
  , ("automatafl-legc-n5.json",
      Dregg2.Circuit.Emit.AutomataflLegCEmit.automataflLegCDescN 5)
  , ("automatafl-legc-n11.json",
      Dregg2.Circuit.Emit.AutomataflLegCEmit.automataflLegCDescN 11)
  , ("automatafl-resolve-marks-n2.json",
      Dregg2.Circuit.Emit.AutomataflResolveMarksCapstone.automataflResolveMarksDescN 2)
  , ("automatafl-resolve-marks-n11.json",
      Dregg2.Circuit.Emit.AutomataflResolveMarksCapstone.automataflResolveMarksDescN 11)
  , ("automatafl-step-marks-n2.json",
      Dregg2.Circuit.Emit.AutomataflStepMarksCapstone.automataflStepMarksDescN 2)
  , ("automatafl-step-marks-n11.json",
      Dregg2.Circuit.Emit.AutomataflStepMarksCapstone.automataflStepMarksDescN 11)
  -- ⚑ node8 CUTOVER: the depth-keyed ONE-FELT blinded 4-ary pair
  -- (`blinded-membership-4ary-depth{2,8}.json`, `blindedMembership4aryDesc`) is RETIRED. Its
  -- node fold chained lane 0 only, so every interior node, the root PI and the published
  -- blinded leaf were ~31-bit. The wide twin is depth-uniform (the depth rides the trace
  -- height), so one row replaces two.
  , ("blinded-membership-4ary-wide.json",
      Dregg2.Circuit.Emit.BlindedMembershipWideEmit.blindedMembershipWideDesc)
  , ("blinded-membership.json",
      Dregg2.Circuit.Emit.BlindedMembershipEmit.blindedMembershipDesc)
  , ("bound-presentation.json",
      Dregg2.Circuit.Emit.BoundPresentationEmit.boundPresentationDesc)
  -- ⚑ DELETED 2026-08-07: `bridge-action.json` / `bridge-action-leaf::bridge_action_air_v1`.
  -- The 28-slot binding-only leaf bound a PROVER-CHOSEN tuple, had no enforcer anywhere in the
  -- tree (`verify_bridge_action` never existed), and `Dregg2.Circuit.BridgeBindingFromFold`
  -- REFUSES it as a bridge-mint backing. The sound deployed backing is the re-proved note-spend
  -- leaf connected to the leg's published PI-46 `mint_hash`
  -- (`circuit-prove/src/note_spend_leaf_adapter.rs`). Nothing serves this name any more.
  , ("derivation.json",
      Dregg2.Circuit.Emit.DerivationEmit.derivationDesc)
  , ("dfa-routing.json",
      Dregg2.Circuit.Emit.DfaRoutingEmit.dfaRoutingDesc)
  -- The TABLE-AS-INPUT DFA-routing instance (`DfaRoutingTableEmit.lean`). Its refinement
  -- `tableRouting_refines_classify` is over the WHOLE emitted descriptor and GENERAL over the
  -- transition table `tbl`, the automaton `d` and the descriptor `name` — strictly
  -- better-conditioned than `dfa-routing.json`'s per-automaton refinement, which carries a
  -- terminal-step hypothesis (`hterm`: the transition-zerofier leaves the last row unasserted) and
  -- a mod-`p` canonicality envelope. Here the transition tooth is ONE `exactPublicRows` lookup
  -- (row-uniform: no last-row exemption) and table membership is an exact ℤ equality, so neither
  -- residual exists. Routed here so the served bytes are RE-DERIVED from that Lean author.
  , ("dfa-routing-table-exact-public-v1.json",
      Dregg2.Circuit.Emit.DfaRoutingTableEmit.demoRoutingDesc)
  , ("dyck-parse.json",
      Dregg2.Circuit.Emit.DyckStackEmit.dyckParseDesc)
  , ("field-delta-result-range.json",
      Dregg2.Circuit.Emit.FieldDeltaRangeEmit.fieldDeltaRangeDescriptor)
  , ("faithful-note-spend-v2.json",
      Dregg2.Circuit.Emit.FaithfulNoteSpendDescriptorPlan.faithfulNoteSpendDescriptor)
  , ("faithful-note-spend-exact-v3.json",
      Dregg2.Circuit.Emit.ExactNullifierAafiRotatedStateWeld.exactNullifierAafiRotatedStateDescriptor)
  -- ⚑ node8 CUTOVER: `merkle-membership-4ary-general.json` (`membership4aryDesc`) is RETIRED —
  -- its per-level node was `chip_absorb_all_lanes(4, children)[0]`, ONE BabyBear felt, so the
  -- whole tree committed at ~31 bits and was collidable at 2^15.5
  -- (`circuit/tests/membership_forge_tooth.rs` exhibits the forge). The narrow `def` survives in
  -- `MerkleMembership4aryEmit` ONLY as the object the wide module's anti-masquerade tooth
  -- quantifies over (`narrowFold4Lane0`, `interior_forge_narrow_admits_wide_refuses`) — you
  -- cannot state "the old fold admits this" without the old fold. It is emitted nowhere.
  , ("merkle-membership-4ary-wide-general.json",
      Dregg2.Circuit.Emit.MerkleMembership4aryWideEmit.merkleMembership4aryWideDesc)
  , ("merkle-membership-depth2.json",
      Dregg2.Circuit.Emit.MerkleMembershipEmit.merkleMembershipDesc)
  , ("mina-fixture.json",
      Dregg2.Circuit.Emit.MinaFixtureEmit.minaFixtureDesc)
  , ("note-spend-leaf.json",
      Dregg2.Circuit.Emit.NoteSpendingLeafEmit.noteSpendLeafDescFixed)
  , ("poseidon2-hash-arity2.json",
      Dregg2.Circuit.Emit.Poseidon2HashEmit.poseidon2HashDesc)
  -- The two Pasta ALU descriptors are the shared fp/fq modular-arithmetic
  -- rows used by the Mina wrap verifier. They were checked in and served but
  -- omitted from this source-of-truth routing table, which made the canonical
  -- emitter refuse the whole by-name surface as a routing gap.
  , ("pasta-alu-sound.json",
      Dregg2.Circuit.Emit.MinaWrapVerifierAir.fpAluDesc)
  , ("pasta-sbox-prog.json",
      Dregg2.Circuit.Emit.MinaWrapVerifierProgram.sboxDesc)
  , ("pasta-sbox-prog-1k.json",
      Dregg2.Circuit.Emit.MinaWrapVerifierProgram.longDesc)
  , ("pasta-alu-fq-sound.json",
      Dregg2.Circuit.Emit.MinaWrapVerifierAir.fqAluDesc)
    -- ⚑ 2026-08-09 — THE SAME ALU ROW WITH THE CHEAP MULTIPLY. `pastaAluSzAir` is `pastaAluAir`
    -- leg for leg with the 63 selector-gated coefficient gates replaced by TWO selector-gated
    -- `PastaSzMul.szBodyAt` challenge gates: 171 → 110 legs, 386 → 325 emitted constraints,
    -- 2 269 → 444 multiplication nodes per row in the multiply block. ⚠ IDENTICAL LAYOUT — 226
    -- declared columns, 794 committed, the same seven `limbs` legs, the same 32 `.transition`
    -- chain legs, and the SAME honest fixture rows (`aluMulRow`/`aluAddRow`/`aluSubRow`), so the
    -- artifact pair is a controlled before/after on one trace. At §5's census that is
    -- `588 732 · 1 764 = 1.04 × 10⁹` multiplication nodes removed and **zero** committed cells:
    -- `WRAP_CELLS` and `WRAP_ROWS_SOUND` do not move by one.
  , ("pasta-alu-sz.json",
      Dregg2.Circuit.Emit.MinaWrapVerifierAir.fpAluSzDesc)
  , ("pasta-alu-fq-sz.json",
      Dregg2.Circuit.Emit.MinaWrapVerifierAir.fqAluSzDesc)
  -- ⚑ 2026-08-05 — THE EIGHT-BLOCK PHASE-2 CHAIN LINK, routed so its bytes are re-derivable from
  -- Lean on a flag day. `MinaPhase2Chain.the_chain_air_extends_the_program_air`: this and
  -- `dregg-pasta-fq-wraplink::v1` are the SAME `programAir qLimb absorbProg` (2048-instruction
  -- `fq_kimchi` ROM); only the boundary pin blocks differ — `chainPins` pins EIGHT
  -- (`in(3) ++ out(3) ++ absorbed(2)`, 256 PIs) where `linkPins` pins SEVEN (224 PIs) and exposes
  -- only TWO of a Poseidon state's THREE outgoing lanes. That missing third lane is why a chain
  -- welded on the wraplink hands a third of its state on as a free prover scalar.
  , ("pasta-fq-chainlink.json",
      Dregg2.Circuit.Emit.MinaPhase2Chain.chainDesc)
    -- ⚑ THE WRAP-VERIFIER SPONGE PAIR AND THE WRAP LINK. Same `programAir qLimb` register file as
    -- the chain link above; `roundDesc`/`absorbDesc` differ only in which ROM they run, and
    -- `linkDesc` pins SEVEN boundary blocks (224 PIs) where `chainDesc` pins eight (256).
  , ("pasta-fq-round.json",
      Dregg2.Circuit.Emit.MinaWrapVerifierSponge.roundDesc)
  , ("pasta-fq-absorb.json",
      Dregg2.Circuit.Emit.MinaWrapVerifierSponge.absorbDesc)
  , ("pasta-fq-wraplink.json",
      Dregg2.Circuit.Emit.MinaBlockFqTranscript.linkDesc)
    -- ⚑ 2026-08-05 — THE PHASE-1 (Fp) LEG. The SAME `programAir` at `pLimb` instead of `qLimb` and
    -- the `fp_kimchi` constants instead of `fq_kimchi`; `MinaWrapVerifierSpongeFp
    -- .the_deployed_fq_programs_are_this_one_at_fqParams` proves the two instruction streams are
    -- one program at two parameter sets. `pasta-fp-chainlink` carries the SAME eight-block pin
    -- layout (`MinaPhase2Chain.chainPins`, 256 PIs) and its link 26's OUTGOING LANE 1 is the
    -- `fq_digest` phase 2's tape starts with — the weld that says WHOSE tape phase 2 absorbs.
  , ("pasta-fp-round.json",
      Dregg2.Circuit.Emit.MinaWrapVerifierSpongeFp.fpRoundDesc)
  , ("pasta-fp-absorb.json",
      Dregg2.Circuit.Emit.MinaWrapVerifierSpongeFp.fpAbsorbDesc)
  , ("pasta-fp-chainlink.json",
      Dregg2.Circuit.Emit.MinaPhase1Chain.chainDesc)
    -- ⚑ THE SIX WRAP COMMITMENT-COMBINATION STAGES + THE ENDO LIFT + THE BUCKETED MSM.
    -- `mina-commit-xi` is `::v2` — the ξ scalar vector's published surface went 64 → 256 PIs, and
    -- because a NAME IS A KEY the descriptor's name moved with it rather than two shapes sharing
    -- one key. `mina-xi-aggregate-msm` is the bucketed Pallas MSM at 219 PIs (`PI_COUNT + NC`),
    -- the ξ-aggregate's in-circuit scalar multiplication.
  , ("mina-commit-pub.json",
      Dregg2.Circuit.Emit.MinaWrapCommitStages.publicCommDesc)
  , ("mina-commit-f.json",
      Dregg2.Circuit.Emit.MinaWrapCommitStages.fCommDesc)
  , ("mina-commit-ft.json",
      Dregg2.Circuit.Emit.MinaWrapCommitStages.ftCommDesc)
  , ("mina-commit-agg.json",
      Dregg2.Circuit.Emit.MinaWrapCommitStages.xiAggDesc)
  , ("mina-commit-ladder.json",
      Dregg2.Circuit.Emit.MinaWrapCommitStages.ladderDesc)
  , ("mina-commit-xi.json",
      Dregg2.Circuit.Emit.MinaWrapCommitStages.xiDesc)
  , ("mina-xi-endo-lift.json",
      Dregg2.Circuit.Emit.MinaWrapXiEndoLift.endoDesc)
  , ("mina-xi-aggregate-msm.json",
      Dregg2.Circuit.Emit.MinaWrapXiAggregateMsm.xiAggMsmDesc)
  , ("predicate-arith-gt.json",
      Dregg2.Circuit.Emit.PredicatesGtEmit.predicateGtDesc)
  , ("predicate-arith-inrange.json",
      Dregg2.Circuit.Emit.PredicatesInRangeEmit.predicateInRangeDesc)
  , ("predicate-arith-le.json",
      Dregg2.Circuit.Emit.PredicatesLeEmit.predicateLeDesc)
  , ("predicate-arith-lt.json",
      Dregg2.Circuit.Emit.PredicatesLtEmit.predicateLtDesc)
  , ("predicate-arith-neq.json",
      Dregg2.Circuit.Emit.PredicatesNeqEmit.predicateNeqDesc)
  , ("predicate-arith.json",
      Dregg2.Circuit.Emit.PredicatesArithmeticEmit.predicateGeDesc)
  , ("presentation-freshness.json",
      Dregg2.Circuit.Emit.PresentationEmit.presentationFreshnessDesc)
  , ("quantified-absence.json",
      Dregg2.Circuit.Emit.QuantifiedAbsenceEmit.quantifiedAbsenceDesc)
  , ("temporal-predicate.json",
      Dregg2.Circuit.Emit.TemporalPredicateEmit.temporalPredicateDesc)
  , ("turn-chain-binding.json",
      Dregg2.Circuit.Emit.EffectVmEmitTurnChainBinding.turnChainBindingDescriptor)
  , ("dark-bazaar-private-n4k4.json",
      Market.DarkBazaarPrivateDescriptor.darkBazaarPrivateN4K4Descriptor)
  , ("dark-bazaar-private-poa-settlement-n4k4-v4.json",
      Market.DarkBazaarPrivatePoaSettlementDescriptor.darkBazaarPrivatePoaSettlementN4K4Descriptor)
  , ("private-book-bfv-slice-o0-c0-q0-k0.json",
      Market.PrivateBookBfvSliceDescriptor.privateBookBfvSliceDescriptor)
  , ("private-book-bfv-odd-ntt-butterfly-q0-n8.json",
      Market.PrivateBookBfvButterflyAir.butterflyDescriptor)
  , ("private-book-bfv-odd-ntt-butterfly-q0-n4096.json",
      Market.PrivateBookBfvButterflyAir.productionQ0N4096Descriptor)
  , ("private-book-bfv-odd-intt-butterfly-q0-n4096.json",
      Market.PrivateBookBfvButterflyAir.productionQ0N4096InverseDescriptor)
  , ("private-book-bfv-threshold-terminal-q0-b80.json",
      Market.PrivateBookBfvButterflyAir.thresholdTerminalQ0Descriptor)
  , ("dark-amm-private-v1.json",
      Market.DarkAmmPrivateDescriptor.darkAmmPrivateDescriptor)
  , ("private-preference-n4k4.json",
      Dregg2.Games.PrivatePreferenceDescriptor.privatePreferenceN4K4Descriptor)
  , ("private-preference-cell-n4k4.json",
      Dregg2.Games.PrivatePreferenceCellDescriptor.privatePreferenceCellN4K4Descriptor)
  , ("private-shuffle-n8.json",
      Dregg2.Games.PrivateShuffleDescriptor.privateShuffleN8Descriptor)
  , ("private-shuffle-fair-n8.json",
      Dregg2.Games.PrivateShuffleFairDescriptor.privateShuffleFairN8Descriptor)
  , ("private-raid-assignment-n4.json",
      Dregg2.Games.PrivateRaidAssignmentDescriptor.privateRaidAssignmentN4Descriptor)
  , ("private-graph-rewrite-4x2.json",
      Dregg2.Crypto.PrivateGraphRewriteDescriptor.privateGraphRewriteDescriptor)
  , ("private-graph-rewrite-cell-4x2.json",
      Dregg2.Crypto.PrivateGraphRewriteCellDescriptor.privateGraphRewriteCellDescriptor)
  , ("private-quest-graph-4x2.json",
      Dregg2.Games.PrivateQuestGraphDescriptor.privateQuestGraphDescriptor)
  , ("descent-custody-census-fixed8-v1.json",
      Dregg2.Games.DescentCensusDescriptor.descentCensusDescriptor)
  , ("shielded-whole-note-swap-substrate-v1.json",
      Dregg2.Circuit.Emit.ShieldedWholeNoteSwapSubstrateDescriptor.shieldedWholeNoteSwapSubstrateDescriptor)
  -- ⚑ L3 (shielded apex redesign): the three already-PROVEN, previously-unrouted shielded
  -- descriptors land as emitted authority. Each is byte-pinned by a machine-checked
  -- `#guard emitVmJson2 <desc> == <GOLDEN>` in its authoring module — this table makes those
  -- bytes the SOLE checked-in artifact (house-law #1 for the shielded family). #15 spend-root
  -- pin, #17 ranged value-link + wraparound-refusal, #17 wide 8-lane value binding. Soundness
  -- WHEN USED still rests on L0's committed accumulator + the L4 route (not yet live).
  , ("dregg-shielded-spend-pinned-root-v1.json",
      Dregg2.Circuit.Emit.ShieldedSpendDescriptor.shieldedSpendDesc)
  , ("dregg-shielded-value-link-conserve-ranged-v1.json",
      Dregg2.Circuit.ShieldedValueRangeDischarge.shieldedValueLinkRangedDesc)
  , ("dregg-shielded-wide-value-link-conserve-v1.json",
      Dregg2.Circuit.Emit.ShieldedWideValueLinkDescriptor.shieldedWideValueLinkDesc)
  , ("private-book-bfv-odd-ntt-butterfly-q0-n8-stage0-exact-public.json",
      Market.PrivateBookBfvExactPublicConsumer.stage0Descriptor)
  , ("private-book-bfv-odd-ntt-butterfly-q0-n8-stage1-exact-public.json",
      Market.PrivateBookBfvExactPublicConsumer.stage1Descriptor)
  , ("private-book-bfv-odd-ntt-butterfly-q0-n8-stage2-exact-public.json",
      Market.PrivateBookBfvExactPublicConsumer.stage2Descriptor)
  -- THE hidden-span commitment descriptor: the WIDE-BLIND (5-blinding-lane, |R| = p⁵ ≈ 2^154.5)
  -- form. The narrow single-blinding-felt `guardedHidingSpanDesc` (~31-bit blinding space) was
  -- DELETED in the felt-width cutover of 2026-07-23 — it must never re-enter this table.
  , ("guarded-hiding-span-m0-wide-blinded-commit-blind5-v1.json",
      Dregg2.Circuit.Emit.GuardedHidingSpanWideBlindEmit.guardedHidingSpanWideBlindDesc)
  -- ⚑ The four peer-chain lightclient verification AIRs. Each is byte-pinned in its authoring
  -- module (`LightClient*Air.lean`); this table makes those bytes the SOLE checked-in artifact and
  -- RE-DERIVABLE from the Lean author (house-law #1). The descriptors carry the chain's consensus
  -- no-forgery obligation, so a dregg node can now emit + prove the STARK from `descriptor_by_name`
  -- — the producibility prerequisite for the gnark peer-wrap → on-chain `DreggPeerRegistry`
  -- true-peers flow. Soundness WHEN USED still rests on the undischarged FRI/STARK floor and each
  -- chain's trusted-instance mirror.
  --
  -- ⚑ FLAG DAY 2026-08-03, ETH ONLY: `ethLcVerifyDesc` is now COMPILER OUTPUT
  -- (`EffectLower.lowerAir` of the `EffectAir` source `ethHeadAir`, no hand-written `VmConstraint2`
  -- in its module) AND carries a new `PC_SLACK` leg that forces `PC ≤ BL` — the unbounded
  -- participation count that PROVED at `PC = 1023` against a 512-key committee. Trace width 20 → 21,
  -- constraints 20 → 22, all eleven anchor columns shifted up by one; the PI surface is UNCHANGED
  -- (11 slots, same meanings). `dregg-eth-lightclient-verify-v1.json` RE-EMITS and its VK must be
  -- re-minted; no other descriptor moves, nothing re-genesises. Its module's byte-golden `#guard` is
  -- retired in favour of `rfl` pins on the compiler's own emission.
  , ("dregg-eth-lightclient-verify-v1.json",
      Dregg2.Circuit.Emit.LightClientEthAir.ethLcVerifyDesc)
  , ("dregg-tm-lightclient-verify-v1.json",
      Dregg2.Circuit.Emit.LightClientTendermintAir.tmLcVerifyDesc)
    -- ⚑⚑ FLAG DAY 2026-08-04, SOLANA: `solLcVerifyDesc` is now COMPILER OUTPUT
    -- (`EffectLower.lowerAir` of the `EffectAir` source `solLcVerifyAir`, no hand-written
    -- `VmConstraint2` in its module; `solLcVerifyAir_mainRailOk = true` by `rfl`) and it is
    -- **MULTI-ROW**: it ABSORBS `dregg-solana-stake-table-fold::v1`'s 44 columns from the SAME
    -- source leg list (`foldLegs`, `sol_fold_block_is_the_shared_source`), one row per stake-table
    -- entry. Trace width 49 → 79, PIs 23 → 22, constraints 63 → 103, declared tables 2 → 4.
    -- `ANCHOR_ROOT` moved from NINE `.first` radix-2^31 limbs that no constraint read to the fold's
    -- EIGHT `.last` output lanes, so the light client's trust anchor is the IMAGE of the rows
    -- (2^123.63 birthday, over 8 · 30.906891 = 247.26 bits — NOT the 2^247.3 second-preimage
    -- figure); the DENOMINATOR moved from four dedicated `.first` columns to the fold's accumulator
    -- on the last row; and `STAKE_TABLE_OK` was DELETED because the fold computes what it asserted
    -- (`LightClientSolStakeFoldAir.solLcAir_table_carrier_from_the_fold` discharges the bridge's
    -- `stakeTableOk` from the emitted pin). ⚠ `dregg-solana-lightclient-verify-v1.json` RE-EMITS and
    -- its VK ROTATES; both the width and the PI count move, so a stale row or PI vector REFUSES TO
    -- LOAD. ⚠ Callers must now supply a POSEIDON2 root in PI[0..7]: `EpochStakeTable::root` is a
    -- domain-separated SHA-256 and must be re-anchored to `dregg-solana-stake-table-root:v2` with
    -- every `WeakSubjectivityAnchor.stake_table_root` re-derived. Until then a caller passing the
    -- SHA root is refused at the pin. The FOLD rung's own bytes are UNCHANGED.
  , ("dregg-solana-lightclient-verify-v1.json",
      Dregg2.Circuit.Emit.LightClientSolanaAir.solLcVerifyDesc)
  , ("dregg-midnight-lightclient-verify-v1.json",
      Dregg2.Circuit.Emit.LightClientMidnightAir.midLcVerifyDesc)
    -- ⚑ THE FIFTH, AND THE ONE THAT LANDS. Mina was the one peer chain with a PROVEN, `@[export]`ed
    -- verify decision (`dregg_mina_lc_verify`) and NO emitted AIR, so a verified Mina block produced
    -- no dregg state transition at all. `minaLcVerifyDesc` is COMPILER OUTPUT — `EffectLower.lowerAir`
    -- of the `EffectAir` source `minaHeadAir`, no hand-written `VmConstraint2` anywhere in its module
    -- (`minaHeadAir_mainRailOk = true` by `rfl` records that the compiler's vocabulary was ADEQUATE).
    -- Unlike its four siblings this one is CONSUMED: `turn/src/executor/mina_head_verifier.rs`
    -- dispatches it from a `StateConstraint::Witnessed` and a turn is REFUSED
    -- (`TurnError::ProgramViolation`) unless the proof verifies against the CELL-PROGRAM-PINNED Mina
    -- weak-subjectivity anchor and the head the turn actually records.
  , ("dregg-mina-lightclient-verify-v1.json",
      Dregg2.Circuit.Emit.LightClientMinaAir.minaLcVerifyDesc)
    -- ⚑ The MULTI-ROW companion (2026-08-03): `dregg-mina-lightclient-link::v1`, one row per
    -- EXHIBITED Mina block. `minaLinkDesc` is COMPILER OUTPUT — `EffectLower.lowerAir` of the
    -- `EffectAir` source `minaLinkAir`, no hand-written `VmConstraint2` in its module. It is the
    -- first COMPILER-AUTHORED MULTI-ROW descriptor in the tree (twelve `.transition` window legs;
    -- `minaLinkAir_mainRailOk = true` by `rfl` records that the vocabulary was adequate). It
    -- derives the SHAPE half of `LINK_OK` — nine-lane parent linkage, height contiguity, and the
    -- segment length as a counted row total — and NOT the Poseidon-over-Pasta half, which stays
    -- witnessed (`LinkHashResidual`).
  , ("dregg-mina-lightclient-link-v1.json",
      Dregg2.Circuit.Emit.LightClientMinaLinkAir.minaLinkDesc)
    -- ⚑ THE BODY-PREIMAGE CHUNK GATES (2026-08-08): `dregg-mina-body-preimage-bits::v1`, ONE ROW,
    -- 2 381 booleanity gates over the packed half of `Body.to_input` and 302 limb gates composing
    -- the eleven packed field elements the body-hash chain absorbs. `bodyBitsDesc` is COMPILER
    -- OUTPUT — `EffectLower.lowerTiedAir` of the `EffectAir` source `bodyBitsAir`, no hand-written
    -- `VmConstraint2` in its module. It discharges the range hypothesis of
    -- `Bridge.MinaPackInjective.packing_is_injective`, without which two different bodies pack to
    -- the same 49 field elements and the whole 25-link chain attests the wrong thing with every
    -- link honest. ⚑ NO TABLE AND NO LOOKUP: committed width = declared width.
  , ("dregg-mina-body-preimage-bits-v1.json",
      Dregg2.Circuit.Emit.MinaBodyPreimageBitsAir.bodyBitsDesc)
    -- ⚑⚑ THE BODY-HASH RE-LIMBING (2026-08-10): `dregg-mina-bodyhash-relimb::v1`, ONE ROW,
    -- 254 booleanity gates over one bit block plus 32 byte-composition gates (coefficients top
    -- out at 2^7) and 9 lane-composition gates (2^28) — the two spellings the body-hash tie has
    -- to relate. `relimbDesc` is COMPILER OUTPUT — `EffectLower.lowerTiedAir` of the `EffectAir`
    -- source `relimbAir`, no hand-written `VmConstraint2` in its module. It removes a MEASURED
    -- blocker: a direct 32-limb ↔ 9-lane identity carries coefficients to 2^248 against BabyBear's
    -- 2^31 and is not a linear gate, so tie 2 could not be a `SeamSpec` at all; read off ONE bit
    -- block both spellings are in-field and the identity is a REGROUPING theorem
    -- (`the_two_spellings_denote_one_value`), not a gate. ⚑ NO TABLE AND NO LOOKUP: committed
    -- width = declared width, 295 → 295, 1.00×.
  , ("dregg-mina-bodyhash-relimb-v1.json",
      Dregg2.Circuit.Emit.MinaBodyHashRelimbAir.relimbDesc)
    -- ⚑ THE PREAMBLE LEGS (2026-08-08): `dregg-mina-preamble-legs::v1`, ONE ROW, 30 columns,
    -- 38 constraints — five `verify_block` preamble legs (B1 non-chunking + non-empty walk,
    -- B3 step-domain ≤ 16, C3's packing length, D1a/D1b's two count equalities) rendered as
    -- emitted polynomials instead of the compiled decision the observer calls. `preambleDesc`
    -- is COMPILER OUTPUT — `EffectLower.lowerTiedAir` of the `EffectAir` source `preambleAir`,
    -- no hand-written `VmConstraint2` in its module. D1b is the marquee: the equality
    -- `verifier.rs:816-820` checks, which `shapeOkRec`'s `decide (0 < publicLen)` never was —
    -- the 41-word index the old gate admitted has NO accepted row
    -- (`the_41_word_index_has_no_accepted_row`). ⚑ NO TABLE AND NO LOOKUP: committed = declared.
  , ("dregg-mina-preamble-legs-v1.json",
      Dregg2.Circuit.Emit.MinaPreambleLegsAir.preambleDesc)
    -- ⚑ THE SOLANA STAKE-TABLE FOLD (2026-08-04): `dregg-solana-stake-table-fold::v1`, ONE ROW PER
    -- STAKE-TABLE ENTRY. `solStakeFoldDesc` is COMPILER OUTPUT — `EffectLower.lowerAir` of the
    -- `EffectAir` source `solStakeFoldAir`, no hand-written `VmConstraint2` in its module
    -- (`solStakeFoldAir_mainRailOk = true` by `rfl`). It DERIVES both of the numbers the Solana
    -- light client's trust story hangs from, from the SAME exhibited rows: the eight-lane Poseidon2
    -- commitment to the stake table (LAST-row PI pins) and the u64 active-stake DENOMINATOR (the
    -- LAST-row value of a limb accumulator with boolean carries). That pair is the point — a swapped
    -- validator set with an IDENTICAL tally clears every denominator pin `solLcVerifyDesc` has and
    -- moves the root (`FoldScheme.same_tally_moves_the_root`, and the deployed-prover half in
    -- `circuit/tests/solana_stake_table_fold.rs`). ⚑ THE HASH WAS CHOSEN BY MEASUREMENT: the
    -- SHA-256 shape of the same fact is 18,049,248 constraints / 12,831,336 columns at 703 live vote
    -- accounts (`LightClientSolanaAir` §6c) against a proved ceiling of 2,131 columns; this is 44
    -- columns and 58 constraints at ANY validator count, because the validators are ROWS and a
    -- Poseidon2 absorb here is ONE chip lookup. ⚠ FLAG DAY: emit
    -- `circuit/descriptors/by-name/dregg-solana-stake-table-fold-v1.json` and MINT a VK. The
    -- commitment is NOT `EpochStakeTable::root`'s SHA-256 — a consumer that wants them to agree must
    -- re-anchor that dregg-authored root onto this Poseidon2 frame and re-derive every
    -- `WeakSubjectivityAnchor.stake_table_root`. ⚑ SUPERSEDED SAME DAY: that sentence continued
    -- "`solLcVerifyDesc` is untouched, no VK rotates" — it is no longer true and was never a reason.
    -- The verify rung ABSORBED this fold's legs (see its routing note above); the two now share ONE
    -- source list and this rung's own emitted bytes did not move.
  , ("dregg-solana-stake-table-fold-v1.json",
      Dregg2.Circuit.Emit.LightClientSolStakeFoldAir.solStakeFoldDesc)
    -- ⚑ THE LEAN-AUTHORED PASTA AIRs. `pasta-rcb-windowed.json` was checked in UNROUTED — its
    -- bytes were not re-derivable from Lean, which is precisely the ungated hand-transcription hop
    -- this file exists to delete, on the descriptor the whole Mina opening-check arc rests on.
  , ("pasta-rcb-windowed.json",
      Dregg2.Circuit.Emit.PastaMsmWindowed.windowedRowDesc)
    -- The FOUR-WAY CUT, at the REAL parameters: 8,192 generators per slice. The offset is a
    -- LITERAL in each emitted gate, so these are four distinct objects and routing them
    -- separately is the point, not duplication.
  , ("pasta-rcb-sg-slice-0-of-4.json",
      Dregg2.Circuit.Emit.PastaMsmSliced.slicedRowDesc 4 0 8192)
  , ("pasta-rcb-sg-slice-1-of-4.json",
      Dregg2.Circuit.Emit.PastaMsmSliced.slicedRowDesc 4 1 8192)
  , ("pasta-rcb-sg-slice-2-of-4.json",
      Dregg2.Circuit.Emit.PastaMsmSliced.slicedRowDesc 4 2 8192)
  , ("pasta-rcb-sg-slice-3-of-4.json",
      Dregg2.Circuit.Emit.PastaMsmSliced.slicedRowDesc 4 3 8192)
    -- …and at the width that PROVES on a box (`circuit/tests/pasta_sliced_sg_prove.rs`). Same
    -- `def`, different width literal; `slices_compose` is width-independent, the measurement is not.
  , ("pasta-rcb-sg-slice-0-of-4-w8.json",
      Dregg2.Circuit.Emit.PastaMsmSliced.slicedRowDesc 4 0 8)
  , ("pasta-rcb-sg-slice-1-of-4-w8.json",
      Dregg2.Circuit.Emit.PastaMsmSliced.slicedRowDesc 4 1 8)
  , ("pasta-rcb-sg-slice-2-of-4-w8.json",
      Dregg2.Circuit.Emit.PastaMsmSliced.slicedRowDesc 4 2 8)
  , ("pasta-rcb-sg-slice-3-of-4-w8.json",
      Dregg2.Circuit.Emit.PastaMsmSliced.slicedRowDesc 4 3 8)
    -- ⚑ THE FELT-SOUND REPLACEMENTS for the six Pasta field ops. The nine `pasta-rcb-*` entries
    -- above are read over ℤ and the deployed prover reads them mod BabyBear; both halves of that
    -- gap are now exhibited as PROVING falsifiers against the very first entry
    -- (`circuit/tests/pasta_{field,addsub}_felt_soundness.rs`). These six are the encodings whose
    -- every gate body FITS a felt, so the two readings coincide — `8×32` limbs, range-checked
    -- carries, and a forcing theorem whose HYPOTHESIS is the mod-`P` reading
    -- (`PastaFieldSound.felt_gates_force_congruence`, `PastaAddSubSound.addsub_gates_force_congruence`).
    --
    -- ⚑ They landed here UNROUTED on 2026-08-03 (`3dcefe00a`, the multiply pair) — checked into
    -- `by-name/` with no entry in this table, which is exactly the ungated hand-transcription hop
    -- the comment above records, and `--verify-by-name-routing` named both by hand. Routed now,
    -- with the add/sub four.
  , ("pasta-fpmul-sound.json",
      Dregg2.Circuit.Emit.PastaFieldSound.fpMulSoundDesc)
  , ("pasta-fqmul-sound.json",
      Dregg2.Circuit.Emit.PastaFieldSound.fqMulSoundDesc)
  , ("pasta-fpadd-sound.json",
      Dregg2.Circuit.Emit.PastaAddSubSound.fpAddSoundDesc)
  , ("pasta-fpsub-sound.json",
      Dregg2.Circuit.Emit.PastaAddSubSound.fpSubSoundDesc)
  , ("pasta-fqadd-sound.json",
      Dregg2.Circuit.Emit.PastaAddSubSound.fqAddSoundDesc)
  , ("pasta-fqsub-sound.json",
      Dregg2.Circuit.Emit.PastaAddSubSound.fqSubSoundDesc)
    -- ⚑ 2026-08-05 — THE SOUND CURVE ROW, on both curves. `PastaCurveSound` composes the six
    -- descriptors above into one RCB complete addition through the `SoundCore` bridge, so a
    -- curve-op row is emitted by the compiler rather than by a `VmConstraint2` list. Routed on
    -- arrival, not after: the six above spent two days unrouted and were named by hand.
  , ("pasta-pallas-complete-add-sound.json",
      Dregg2.Circuit.Emit.PastaCurveSound.pallasCompleteAddSoundDesc)
  , ("pasta-vesta-complete-add-sound.json",
      Dregg2.Circuit.Emit.PastaCurveSound.vestaCompleteAddSoundDesc)
    -- ⚑ 2026-08-09 — THE CHEAP MULTIPLY, ROUTED. The SAME RCB complete addition with each of the
    -- twelve multiplies' 63 coefficient gates replaced by TWO relocated `PastaSzMul.szBodyAt`
    -- challenge gates at `permutation_randomness()[0]` and `[1]`: 4 476 → 3 744 constraints, and
    -- 12·2 206 → 12·442 multiplication nodes in the emitted bodies. ⚠ THE WIDTH DOES NOT MOVE —
    -- 3 048 declared before and after, same range lookups, same honest witness
    -- (`PastaCurveSound.szRcbWidthIsUnchanged`, `szMulCore_width_unchanged`), so the SAME emitted
    -- trace fixture proves against both artifacts. That is the whole point of the pair: it is a
    -- controlled before/after on one witness. ⚠ The sz row's soundness carries a LEDGER the
    -- schoolbook row does not — it forces the congruence at `1 − 2^−197.0` over the draw
    -- (`sz_two_point_clears_the_bar`), and the one-gate form would be `2^−98.5`, BELOW the bar
    -- (`sz_single_challenge_is_below_the_bar`), which is why there are two draws and never one.
    -- These are the first `chalGate`-carrying artifacts in `by-name/`: they declare
    -- `"challenges":2`, they REFUSE the uni-stark route by construction (`Ir2UniAir::new`), and
    -- `prove_vm_descriptor2` is the only prover that can carry them.
  , ("pasta-pallas-complete-add-sz.json",
      Dregg2.Circuit.Emit.PastaCurveSound.pallasCompleteAddSzDesc)
  , ("pasta-vesta-complete-add-sz.json",
      Dregg2.Circuit.Emit.PastaCurveSound.vestaCompleteAddSzDesc)
    -- ⚑ 2026-08-05 — THE THREADED SOUND ROW. The same RCB complete addition with the accumulator
    -- carried to the NEXT row by 96 `.transition` window legs, so a ladder's depth is ROWS and the
    -- width is a constant 3 048 at every depth. `PastaCurveSound.sound_ladder_does_not_fit_a_row`
    -- priced the row-local layout at 731 136 columns in ONE row at GLV depth; this is the layout
    -- that answers it, and the layout `minaOpeningCheckDesc` was refused by the prover for lacking.
  , ("pasta-pallas-rcb-thread.json",
      Dregg2.Circuit.Emit.PastaLadderThread.pallasThreadDesc)
  , ("pasta-vesta-rcb-thread.json",
      Dregg2.Circuit.Emit.PastaLadderThread.vestaThreadDesc)
    -- ⚑ 2026-08-06 — THE DEFERRED IPA ACCUMULATOR CHECK, IN A CIRCUIT. The threaded sound VESTA
    -- row with its two endpoints published (`in ‖ out`, 96 limbs each, contiguous so a fold node
    -- connects them with `cb.connect`), and — in the `-final` artifact — the 64 `.last`-row window
    -- gates that force the terminal accumulator to be the point at infinity. That last block IS
    -- `pasta_msm::is_identity` as a constraint, i.e. the leg `Ipa.Step.accumulator_check` performs
    -- and `bridge/src/mina_accumulator_discharge.rs` performs NATIVELY. The pair is the
    -- OLD-ADMITS/NEW-REJECTS exhibit: a chain that does not vanish proves under `-seg` and is
    -- refused under `-final`. `MinaAccumulatorAir.accumulator_discharge_forced` is what the
    -- emitted constraints force.
    -- ⚑ 2026-08-06 — AND THE ADDEND ROUTING IS NO LONGER A RESIDUAL. `-routed` is `-final` plus a
    -- threaded row-index column and ONE exact-public lookup per row, tuple `(index + 1) ‖ the 96
    -- addend limbs` = 97 wide. That needed `MAX_EXACT_PUBLIC_ARITY` raised `64 → 97`, which cost a
    -- JSON re-emit and a re-pin and NO resource: §4's price was retracted at source and the cap
    -- turned out to be the member count of `dregg-ir2-exact-public-v1.json`. The new pair: a chain
    -- of honest Vesta points that are NOT this block's addends proves under `-final` and is
    -- REFUSED under `-routed`, by the balance of `mina_accumulator_addends`.
    -- `MinaAccumulatorAir.accumulator_discharge_forced_on_declared_addends` concludes over a fold
    -- in which the trace's addend columns do not occur.
  , ("mina-accumulator-seg.json",
      Dregg2.Circuit.Emit.MinaAccumulatorAir.accSegDesc)
  , ("mina-accumulator-final.json",
      Dregg2.Circuit.Emit.MinaAccumulatorAir.accFinalDesc)
  , ("mina-accumulator-routed.json",
      Dregg2.Circuit.Emit.MinaAccumulatorAir.accRoutedDemoDesc)
    -- ⚑ 2026-08-07 — THE SCALING RUNG. `-routed`'s manifest is a FREE PARAMETER: `accRoutedDesc`
    -- emits any 97-wide table it is handed, so the routing bought "a prover cannot choose the
    -- addends" and not "the addends are `−s_r·G_r`". `-srs`'s manifest is not a parameter at all —
    -- it is `MinaAccumulatorAir.srsScaledAddends`' IMAGE at the pinned SRS and the challenges, so
    -- the object anyone must certify went from `n` arbitrary Vesta points to `|u⃗|` field elements
    -- and a byte-pinned blob. Same algebra as `-routed` (4 831 constraints, 3 049 columns) — only
    -- the manifest and the name differ, which is what makes the pair an exhibit: the routed rung's
    -- own honest chain PROVES under `-routed` and is REFUSED under `-srs`
    -- (`ir2_exact_public_a97`), because it discharges and is not the scalar multiples.
  , ("mina-accumulator-srs.json",
      Dregg2.Circuit.Emit.MinaAccumulatorSrsDemo.accSrsDemoDesc)
    -- ⚑ 2026-08-07 — THE HEAD RUNG, and it closes the accumulator's SECOND trusted item.
    -- `-srs` publishes the claim at `PI[0..95]` and NO gate relates it to a head: the comparison
    -- was `bridge/src/mina_accumulator_discharge.rs::root_entry_binds_claim`, whose own docblock
    -- says *"a REFUSAL made by the consumer, not a gate"* — so a node that forgets to call it
    -- accepts any discharging claim. `-head` is `-srs`'s algebra plus TWELVE constraints: a guard
    -- forced on at `.first` and off on every successor, nine PI pins publishing the head, and ONE
    -- `proof_bind` whose 105 `commit` lanes (head ‖ claim) are `bound` to the descriptor's declared
    -- pair and whose nine `vk` lanes are pinned to `dregg-mina-lightclient-verify::v1`'s semantic
    -- fingerprint. The pair: the honest head chain PROVES under `-head`, and the SAME chain with
    -- the devnet GENESIS anchor substituted for the block-539508 tip — a claim that still
    -- discharges, still routes, still publishes PI[0..191] byte-identically — is REFUSED by the
    -- `proof_bind` and by nothing else, while proving under `-srs` narrowed to 3 049 columns.
    -- ⚠ FLAG DAY: re-emitting `dregg-mina-lightclient-verify-v1.json` MOVES `MINA_HEAD_VK_LANES`
    -- and re-VKs THIS descriptor. Nothing below `-head` moves; PI 192..200 are APPENDED.
  , ("mina-accumulator-head.json",
      Dregg2.Circuit.Emit.MinaAccumulatorSrsDemo.accHeadDemoDesc)
    -- ⚑ …and its NEGATIVE CONTROL, emitted for the same reason `mina-wrap-conjunction-unthreaded`
    -- is: the isolation claim *"refused by the `proof_bind` and by nothing else"* has to be
    -- MEASURED, and measuring it by editing a parsed descriptor's `bound` lanes in Rust would be
    -- Rust authoring AIR. Same algebra, same manifest, same claim, the devnet GENESIS head
    -- declared instead of the block-539508 tip: the two artifacts differ in EXACTLY ONE constraint
    -- and within it in EXACTLY the nine head lanes, and each accepts the chain the other refuses.
  , ("mina-accumulator-head-genesis.json",
      Dregg2.Circuit.Emit.MinaAccumulatorSrsDemo.accHeadGenesisDesc)
    -- ⚑ 2026-08-05 — THE CONJUNCTION, THREADED, AND ITS UNTHREADED TWIN. The row withheld below
    -- lands here: the b-polynomial's 15 rounds are 15 ROWS carried by 448 `.transition` legs, so
    -- the width is 2 536 at every round count and the artifact is 4 157 constraints instead of
    -- 30 607. The `-unthreaded` twin is the SAME Lean AIR minus the thread — the negative control
    -- `without_the_thread_the_forged_trace_proves` needs, emitted rather than assembled in Rust by
    -- filtering constraints out of a parsed descriptor (which would be Rust authoring AIR).
  , ("mina-wrap-conjunction.json",
      Dregg2.Circuit.Emit.MinaWrapConjunctionAir.conjunctionDesc)
  , ("mina-wrap-conjunction-unthreaded.json",
      Dregg2.Circuit.Emit.MinaWrapConjunctionAir.conjunctionUnthreadedDesc)
    -- ⚑ 2026-08-06 — THE NINE THAT EXISTED ONLY AS RUST STRING LITERALS. Each of the nine rows
    -- below had a Lean author with an `emitVmJson2` `#guard` and NO artifact, so its bytes reached
    -- the test suite by hand-copy. `descriptor_by_name.rs` dispatches none of them — same standing
    -- as `dyck-parse.json` and `mina-fixture.json` above: the routing table is a SUPERSET of the
    -- dispatch table by design, and routing is what makes a byte-pin re-derivable.
  , ("deco-commitment-leaf.json",
      Dregg2.Circuit.Emit.DecoLeafEmit.decoDescriptor)
  , ("caveat-admission-leaf.json",
      Dregg2.Circuit.Emit.CaveatAdmissionEmit.descriptor)
  , ("dfa-routing-table-route8-bound-v1.json",
      Dregg2.Circuit.Emit.DfaRoutingTableRoute8.demoBoundDesc)
  , ("attested-automaton-map-committed-weld8-bound-v1.json",
      Dregg2.Circuit.Emit.AttestedAutomatonRoute8.weldBoundInstance)
  , ("solvency-leaf-v2.json",
      Dregg2.Circuit.Emit.SolvencyLeafEmit.solvencyDescriptor)
  , ("dfa-routing-injection.json",
      Dregg2.Circuit.Emit.DfaRoutingGeneralEmit.injectionRoutingDesc)
  , ("factory-backing-leaf.json",
      Dregg2.Circuit.Emit.TupleBindingEmit.factoryDesc)
  , ("hatchery-attestation-leaf.json",
      Dregg2.Circuit.Emit.TupleBindingEmit.hatcheryDesc)
  , ("sovereign-authority-leaf.json",
      Dregg2.Circuit.Emit.TupleBindingEmit.sovereignDesc)
  , ("membership-leaf.json",
      Dregg2.Circuit.Emit.TupleBindingEmit.membershipDesc)
  , ("delegate-binding-v2.json",
      Dregg2.Circuit.Emit.TupleBindingEmit.delegateDesc)
  , ("compound-predicate.json",
      Dregg2.Circuit.Emit.PredicatesRelationalCompoundEmit.compoundPredicateDesc)
  , ("relational-predicate.json",
      Dregg2.Circuit.Emit.PredicatesRelationalCompoundEmit.relationalPredicateDesc)
  , ("ivc-state-transition.json",
      Dregg2.Circuit.Emit.EffectVmEmitIvcStateTransition.ivcStateTransitionDescriptor)
    -- `effectActionDesc` is name/arity-PARAMETERIZED; these are its two deployed instances, and
    -- they are the pair `effect_action_emit_gate.rs` carried as two literals in ONE file.
  , ("effect-revoke-capability.json",
      Dregg2.Circuit.Emit.EffectActionBindingEmit.revokeCapabilityDesc)
  , ("effect-burn.json",
      Dregg2.Circuit.Emit.EffectActionBindingEmit.burnDesc)
  , ("garbled-eval.json",
      Dregg2.Circuit.Emit.GarbledEvalEmit.garbledEvalDesc)
  , ("fold-step.json",
      Dregg2.Circuit.Emit.FoldEmit.foldDesc)
  , ("multi-step-chain.json",
      Dregg2.Circuit.Emit.MultiStepChainEmit.multiStepChainDesc)
  , ("committed-threshold.json",
      Dregg2.Circuit.Emit.CommittedThresholdEmit.committedThresholdDesc)
  ]

/- The routing table covers the checked-in directory exactly. A bare count is a
weak guard, but it is the one this file can state without IO — and note what it does NOT say:
a table entry whose artifact was never committed still COUNTS, so this guard passes on a ghost.

Both directions are gated outside Lean:
* file → table: `emit_descriptors.py`'s recursive coverage check fails on any by-name file this
  table does not reproduce. Needs a full emit to say anything.
* table → file: `scripts/emit_descriptors.py --verify-by-name-routing` (CI job
  `descriptor-by-name-routing`, and a preflight in `check-descriptor-drift.sh`) reconciles this
  table against the tracked `by-name/` set AND the PROVENANCE stamp. It parses the name literals
  STATICALLY, so it keeps reporting while the emit is blocked. Adding an entry here without
  committing its artifact reds that gate by name. -/
-- ⚠ 89, not 87. This pin was STALE at 86 against 88 entries when this lane arrived: two sibling
-- lanes (`pasta-alu-sound` / `pasta-alu-fq-sound` / `dark-bazaar-private-poa-settlement-n4k4-v3`)
-- added routing rows in the shared tree and left the pin behind, so the file was already red for
-- everyone. 89 = those + `dregg-solana-stake-table-fold-v1.json`. A single shared line cannot be
-- bumped by only one lane's worth; whoever reads the blame should read it as three lanes' rows.
-- ⚠ 91, not 89: this lane added `pasta-sbox-prog` + `pasta-sbox-prog-1k` (the register-file /
-- instruction-ROM machine and its 2^10 instance). Same shared-line hazard as the note above — if
-- the blame on this line is one lane's, the count is probably still short.
-- ⚑ 2026-08-05 — 102, and the two numbers before it were BOTH wrong in the way this note warned
-- about. The pin arrived at 92 against 91 ROWS: a lane bumped the count and its row did not
-- survive the shared tree, so `rfl` failed and `lake env lean --run EmitByName.lean` — the ONLY
-- route to `by-name/` — was dead for every lane at once. That is why eleven descriptors reached
-- `by-name/` through one-off drivers instead of this table. 102 = 91 real rows + those eleven,
-- and it is now the DIRECTORY's count, not an increment: `--verify-by-name-routing` reconciles
-- both directions, so the next drift is a named red rather than eleven private emitters.
-- ⚑ 2026-08-05 — 107 = 104 + the phase-1 (Fp) sponge trio: `pasta-fp-round`, `pasta-fp-absorb`
-- and `pasta-fp-chainlink`. Same shared-line hazard as every note above: if the blame on this
-- line is one lane's, the count is probably already short again.
-- ⚑ 2026-08-05 — 109 = 107 + the threaded sound row on both curves (`pasta-{pallas,vesta}-rcb-
-- thread`). At that count `MinaWrapConjunctionAir.conjunctionDesc` was deliberately NOT routed: its
-- emitted instance was ROW-LOCAL (22 184 columns, 30 607 constraints, a 24 MB artifact — 10x the
-- largest descriptor in the tree and 40% of the directory), which is the very layout
-- `PastaLadderThread` exists to replace, and routing it would have checked in the shape that same
-- commit measured as wrong.
-- ⚑ 2026-08-05 — 111, AND THE WITHHELD ROW IS ONE OF THE TWO. The conjunction's b-polynomial is
-- threaded: 15 rounds are 15 ROWS carried by 448 `.transition` legs, the width is 2 536 at EVERY
-- round count (`threaded_conj_width_is_flat`) and the descriptor is 4 157 constraints. The second
-- row is its unthreaded TWIN, the negative control that makes the falsifier's refusal attributable
-- to the thread rather than to the fixture — the same Lean AIR minus the 448 window legs, so it is
-- an emission and not a Rust-side edit of a parsed descriptor.
-- Same shared-line hazard as every note above: if the blame on this line is one lane's, the count
-- is probably already short again.
-- ⚑ 2026-08-06 — 122 = 113 + the nine descriptors that had a Lean author and no artifact (their
-- bytes lived in fifteen hand-copied `const … &str = r#"…"#` literals under `circuit-prove/
-- tests/`). ⚠ THIS PIN IS BUMPED IN THE SAME EDIT AS THE ROWS, DELIBERATELY. Every note above
-- records the same accident from the other side: a lane adds rows and leaves the pin, or bumps
-- the pin and its row does not survive the shared tree — and either way `rfl` fails, `lake env
-- lean --run EmitByName.lean` dies, and the WHOLE by-name surface is unemittable for every lane
-- at once. That outage is what produced the eleven private one-off emitters this file spent
-- 2026-08-05 absorbing. Rows and pin are one atom.
-- ⚑ 2026-08-08: the 126th row (`dregg-mina-body-preimage-bits-v1.json`) pushed the `rfl` over the
-- default recursion depth — the list is longer, not the descriptor heavier. Raised, not weakened.
-- ⚑ 2026-08-08: 127 = 126 + `dregg-mina-preamble-legs-v1.json` (the five `verify_block` preamble
-- legs as emitted polynomials). Rows and pin are one atom — bumped in the same edit as the row.
-- ⚑ 2026-08-09 → repaired 2026-08-10: 131 = 127 + the four Schwartz-Zippel rows `001e4732a` added
-- (`pasta-alu-sz`, `pasta-alu-fq-sz`, `pasta-{pallas,vesta}-complete-add-sz`). THE ACCIDENT EVERY
-- NOTE ABOVE PREDICTS HAPPENED AGAIN, for the sixth time: rows landed, the pin did not move, `rfl`
-- was `131 = 127`, and the whole by-name emit surface was dead for every lane for ~19 hours. It
-- also took a gate with it that no one would look for here — `emit_descriptors.py`'s STATIC parse
-- refuses when its count disagrees with this pin ("refusing to report on a table it may be reading
-- wrong"), so `--verify-provenance` / `--verify-by-name-routing` exited before checking anything,
-- and the `provenance` local-gates row reported NOTHING rather than a pass or a fail. The pin is
-- not a cap on the table; it is the parser's independent ground truth. 131 is the measured count:
-- 131 rows, 131 tracked `circuit/descriptors/by-name/*.json`, no duplicates.
-- ⚑ 2026-08-10: 132 = 131 + `dregg-mina-bodyhash-relimb-v1.json` (the bit-level re-limbing that
-- makes tie 2 expressible as two descriptor-ended seams). Rows and pin are one atom — bumped in
-- the same edit as the row, which is the discipline the six notes above were each paid for.
-- ⚑ 133 = 132 + `attested-automaton-map-committed-weld8-v1.json`. Rows and pin are one atom.
set_option maxRecDepth 8000 in
theorem byNameDescriptors_length : byNameDescriptors.length = 144 := rfl

def main : IO Unit := do
  for (file, d) in byNameDescriptors do
    IO.println s!"{file}\t{emitVmJson2 d}"
