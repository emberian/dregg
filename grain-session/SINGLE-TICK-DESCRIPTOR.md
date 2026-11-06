# Single-nonce-tick multi-field grain rotated descriptor

Branch `i10-single-tick-grain-descriptor` (ember-gated: not merged, nothing deployed or emitted).
Helper lane for initiative 10. The gap it closes is named in `grain-turn/src/finalize.rs`
(`finalize_session`, "RESIDUAL GAP").

## 1. The gap, restated with a measurement

A grain turn (`grain-turn/src/lib.rs` `ToolGatewayMinter::mint_turn`) is one executor turn whose
agent is the grain worker cell `w`. `turn/src/executor/execute.rs` PHASE 1 does two things to `w`
once per turn: `debit_balance(turn.fee)` and `increment_nonce()`. The body then applies five
`SetField`s to `w`, in this order: slot 4 `calls_made` (gateway-prepended), 3 `history_root`,
5 `consumed`, 6 `heap_root`, 7 `action`. The SDK stamps `fee: 5_000` on every
`ToolGateway::invoke` turn (`sdk/src/runtime.rs` `execute_method`).

The R3 adapter turns this into about five rotated legs, one `setFieldVmDescriptor2-{slot}R24` per
slot. Each of those ticks the nonce once and freezes the balance. So the folded head differs from
the ledger head in two coordinates, not one:

| coordinate | ledger head after T turns | EffectVM-model head (today) |
|---|---|---|
| nonce | `pre + T` | `pre + 5T` |
| balance | `pre − T·fee` | `pre` (every SetField member freezes `bal_lo`) |
| slot fields | the written values | the same values |

`finalize_session_threaded` and `grain-session/src/lib.rs` describe the nonce difference only. The
balance difference follows from the code read above.
`grain-turn/tests/ledger_head_delta.rs` (on this branch) is the falsifier for this table. On the real
executor it asserts, per turn: nonce `+1`; balance `−5000`; exactly five SetFields on `w` in the
order above; slots 0..2 untouched; and turn `i+1`'s pre-cell equal to turn `i`'s post-cell.
**It has not been run yet** (§7). Until it is, the balance row is a code reading.

## 2. Descriptor semantics

**One executor grain turn is one active EffectVM row.** The leg is that row followed by NoOp pads.

Selector `s_g` = column `SEL_GRAIN_TURN = 6`, a retired index (decision D1).

| column | active row (`s_g = 1`) | any other row (`s_g = 0`) |
|---|---|---|
| `fields[j]`, j ∈ {3,4,5,6,7} | `after = param(j−3)` (lane 0 of the written 32-byte value) | frozen |
| `fields[0..2]` | frozen | frozen |
| `bal_lo` | `after = before − param5` (`turn.fee`) | frozen |
| `nonce` | `after = before + 1` | frozen |
| `bal_hi`, `cap_root`, `reserved` | frozen | frozen |

Gate forms (`metatheory/Dregg2/Circuit/Emit/EffectVmEmitGrainTurn.lean`):
- `gGrainWrite j = (a_j − b_j) − s_g·(param − b_j)` is two-sided. It writes on the active row and freezes on every other row.
- `gNonceG = (a_n − b_n) − s_g`. The tick is the selector itself, so no row other than the grain row can move the nonce. This is a design change from `gNonce` (`… − (1 − s_noop)`), which ticks on every non-NoOp row.
- `gBalLoFeeG = (a_lo − b_lo) + s_g·fee`.
- `gSelBool` makes `s_g` boolean.
- `grainFirstRowPin` (`.boundary .first (s_g − 1)`) makes row 0 the grain row.
- `transitionAll` (the transfer face's whole-block continuity) chains each row's after-block to the next row's before-block.
- The IR-v2 window gate `grainNoSecondActiveRow` (`nxt s_g = 0` on every transition) makes every later row inactive.

**Relation to Phase 1.** The row is `commitPrologue` (fee debit + ONE nonce tick on the agent)
composed with the five-write body, applied to the one cell the grain turn touches. The agent and the
written cell coincide (`w`), so one row carries both phases. Phase 3 (`distributeFee`) credits the
proposer and treasury cells, never `w`. The descriptor does not model it, and the theorem uses the
`distributeFee_frame` hypothesis `w ∉ {proposer, treasury}`.

**Rotated member** (`EffectVmEmitGrainTurnRotated.lean`, `grainTurnVmDescriptor2R24`). The steps follow the deployed setField members, generalised from one slot to five:
1. `rotateV3`.
2. `frozenAuthorityColEqs`.
3. The fields completion freezes for slots 0..2 only. That is 24 freezes, where a per-slot member has 56.
4. `graduateV1`.
5. `withSelectorGate 6`.
6. The window gate.
7. `withSetFieldCompletionPins j` for each `j ∈ {3..7}`. This adds 40 tail PIs publishing the high lanes of the five 32-byte values. A per-slot member adds 8.

The trace width equals `setFieldV3 3`'s (`#guard`). The registry wraps (`withDfaRcPins`, `wideAppend`) are not applied, because the member is in no registry.

## 3. Lean statements (elaborated, no `sorry`, `#assert_axioms` clean)

Elaborated with `lake env lean` against the main tree's built oleans (the worktree has no `.lake`;
nothing was built in it). The rotated file was checked against an overlay that adds the core
module's olean. Both are in `metatheory/Dregg2/Circuit/Emit/`.

The agreement with the executor's per-turn transition, over the real defs (`Admission.runTurn`,
`Admission.commitPrologue`, `Admission.distributeFee`, `TurnExecutorFull.execFullTurnA`,
`EffectVmEmitSetField.slotName`):

```lean
def grainBody (w : CellId) (v : Fin 8 → Int) : List FullActionA :=
  ([4, 3, 5, 6, 7] : List (Fin 8)).map (fun j => .setFieldA w w (slotName j) (v j))

def grainTurnExec (ctx : AdmCtx) (h : TurnHdr) (v : Fin 8 → Int) (s : RecChainedState) :
    Option RecChainedState :=
  runTurn ctx h s (fun s₁ =>
    (execFullTurnA s₁ (grainBody h.agent v)).map (fun s₂ => distributeFee ctx s₂ h.fee))

theorem grainTurn_row_agrees_executor
    (ctx : AdmCtx) (h : TurnHdr) (v : Fin 8 → Int) (s s₂ : RecChainedState) (p t : CellId)
    (hp : ctx.proposer = some p) (ht : ctx.treasury = some t)
    (hwp : h.agent ≠ p) (hwt : h.agent ≠ t)
    (hadm : admissible ctx h s = true)
    (hbody : execFullTurnA (commitPrologue s h.agent h.fee) (grainBody h.agent v) = some s₂)
    (env : VmRowEnv) (post : CellState)
    (hrow : IsGrainTurnRow env) (hcanon : GrainRowCanon env)
    (henc : RowEncodesGrain env (grainProj s.kernel h.agent) post)
    (hval : ∀ j : Fin 8, IsGrainSlot j = true → env.loc (prmCol (grainParam j)) = v j)
    (hfee : env.loc (prmCol FEE_PARAM) = h.fee)
    (hsat : ∀ c ∈ grainTurnRowGates, c.holdsVm env false false) :
    grainTurnExec ctx h v s = some (distributeFee ctx s₂ h.fee)
    ∧ post.balLo = balOf ((distributeFee ctx s₂ h.fee).kernel.cell h.agent)
    ∧ post.nonce = nonceOf ((distributeFee ctx s₂ h.fee).kernel.cell h.agent)
    ∧ ∀ j : Fin 8,
        post.fields j = fieldOf (slotName j) ((distributeFee ctx s₂ h.fee).kernel.cell h.agent)
```

Supporting theorems, all proved:
- `grainTurnVm_faithful`: on the active row, the gates hold iff `GrainTurnRowIntent`. The reverse direction is the completeness half, so an honest row is not refused.
- `grainTurn_inactive_row_frozen`: a row with `s_g = 0` moves no nonce, balance or slot.
- `grainTurn_rejects_double_tick_row`: on the active row, a nonce delta of 2 is UNSAT.
- `grainTurn_trace_ticks_once`: every row `k ≥ 1` starts at `pre + 1`. The trace has ≥ 2 rows; the gates hold on the non-last rows; the first-row pin, window gate and nonce continuity hold. The continuity (`nonce_transition_mem`) and the pin (`firstRowPin_mem`) are proved to be constraints of the face.
- `grainTurn_refuses_two_ticks`: no such trace has its last row's before-nonce at `pre + 2`.

**Open obligations (named, not proved here):**
- **O1 (rotated lift).** A `Satisfied2` witness of `grainTurnVmDescriptor2R24` yields the face's hypotheses on every row. The ingredients are the setField ones (`rotV3FrozenSetField_sound_v1`, `satisfied2_of_withSetFieldCompletionPins`, selector-gate peel), plus one peel for the appended window gate. I did not write these lifts.
- **O2 (the wrap row).** `grainTurn_trace_ticks_once` stops at the last row's BEFORE block. The rotated `NEW_COMMIT` pin (`rotPins`) reads the last row's AFTER block. Every `.gate`, including the welds, binds only off the last row (`holdsVm`, `when_transition`). Equating the two blocks on the final pad is the same question for every rotated member. I did not establish how the deployed AIR closes it.
- **O3 (value8).** The five completion-lane groups are published as PIs (as for setField VALUE8), not tied to the executor's 32-byte values. Same status as the deployed setField members.

## 4. What changes, what rotates, who is affected

Built on this branch:
- `metatheory/Dregg2/Circuit/Emit/EffectVmEmitGrainTurn.lean` (new): the face, the proofs, and the executor link.
- `metatheory/Dregg2/Circuit/Emit/EffectVmEmitGrainTurnRotated.lean` (new): the R24 member.
- `grain-turn/tests/ledger_head_delta.rs` (new): the measurement.
- This note.

Not added to `Dregg2.lean` / any import root, so the main tree build is untouched.

Designed, not built. Deploying takes these steps, in order:
1. **Selector (VERB-LOCKSTEP).**
   - Rust: `circuit/src/effect_vm/columns.rs` gets `sel::GRAIN_TURN = 6`, and 6 is removed from `RETIRED_SELECTORS`.
   - Lean: `EffectVmEmit.sel` gets the twin.
   - `circuit/tests/unforced_pi_pin_census.rs::retired_selector_columns_are_referenced_by_nothing` goes red by design, and its list is updated.
2. **VM effect.**
   - `circuit/src/effect_vm/effect.rs` gets `Effect::GrainTurn { values: [BabyBear; 5], fee }` (lane 0), plus the five value8 completion vectors.
   - `trace.rs` gets `effect_selector` and the row writer (params 0..5, a single tick, the fee debit).
   - `trace_rotated.rs` gets `rotated_descriptor_name(6) = "grainTurnVmDescriptor2R24"`, and the wide producer fills five slots' completion lanes.
   - Every exhaustive `match` on `Effect` changes.
3. **Marshalling stays where it is honest.** `AgentCipherclerk::convert_effects_to_vm` is NOT changed: it must keep projecting the executor's effect list one-to-one. The coalescing lives in `grain-turn/src/finalize.rs`. A `grain_turn_vm_effect(record)` builds the one `GrainTurn` from the five SetFields and `turn.fee`, and fails closed on any other shape (attestation slot 8, a missing slot, a non-worker cell). `finalize_grain_turn_from` then mints ONE leg, and `apply_run`'s per-effect tick goes away. `split_into_cohort_runs` (`sdk/src/full_turn_proof.rs`) needs no change: a single-effect run is one run.
4. **Registries (the VK epoch).** All of these move:
   - Lean `v3RegistryBare` (and its `#guard v3Registry.length == 36`).
   - `v3RegistryWideBB` / `v3RegistryWide` (`#guard … == 36`, and the `decide` in `CapOpenEmit.lean:1822`).
   - The emit drivers `metatheory/EmitWideRegistryProbe.lean` and `EmitWideUMemWeldRegistryProbe.lean`.
   - The TSVs `circuit/descriptors/rotation-v3-staged-registry.tsv` and `rotation-wide-registry-staged.tsv`.
   - Their pins `V3_STAGED_REGISTRY_FP` and `WIDE_REGISTRY_STAGED_FP` (`circuit/src/effect_vm_descriptors.rs`), and `WIDE_MEMBER_GEOMETRY`.
   - `CUTOVER_READY_SELECTORS` (`circuit/src/proof_forest.rs`). `joint_turn_aggregation::rotated_descriptor_selector` then resolves the leg's display name from the wide TSV.
   - The coverage gates `producer_descriptor_coverage_gate.rs`, `keystone_descriptor_deployment_gate.rs` and `effect_enum_descriptor_residual_gate.rs`.
   - The `CircuitSoundnessAssembled.lean` selector→member map.

   The change is ADDITIVE: no existing member's bytes change. But both registry digests rotate, and every light client that iterates the wide registry admits one more member.
5. **R3 consumers.**
   - `grain-verify` (`r3_verify`) and `grain-session` fold one leg per turn.
   - The recursion VK fingerprint is a function of `(num_turns, leaf trace heights)`, so every recorded grain aggregate VK changes: `num_turns` goes from about 5T to T.
   - `finalize_session_threaded` becomes unnecessary: the naive `finalize_session` already closes, because the leg head is the ledger head.
   - The `r3_threaded_session.rs` and `r3_grain_adapter.rs` expectations change.

## 5. Falsifiers

- **F1, the multi-turn fold closes at the LEDGER head.** Drive T ≥ 3 grain turns with `ToolGatewayMinter`, finalize with the single-leg recipe (no state threading), and fold. The test asserts:
  - zero seam breaks;
  - the aggregate's `final_root8` equals the wide commitment of the LAST record's real `after_cell`, computed by `produce(after_cell, …)`, the same block derivation the genesis uses;
  - its `genesis_root8` equals that of record 0's real `before_cell`.

  Today this fails on both nonce and balance. With the member it must pass.
- **F2, a two-tick forgery is refused.** Over the member's real `prove_vm_descriptor2` / `verify_vm_descriptor2`, take the honest one-turn trace and set the active row's `nonce_after` to `pre + 2` (re-deriving the after-block commit). It must be UNSAT. Second variant: keep row 0 honest and make a pad row carry `s_g = 1` with a second tick. The window gate must refuse it. Lean already proves both at the row and trace level (`grainTurn_rejects_double_tick_row`, `grainTurn_refuses_two_ticks`). F2 is the Rust-side twin.
- **F3, fee binding.** A trace that debits `fee − 1` while the published balance claims the ledger's `pre − fee` is refused.
- **F0, the spec stays true** (built): `ledger_head_delta.rs`.

## 6. Cost

- **Proving.** A grain turn goes from about 5 leg proves to 1, and the fold has T leaves instead of about 5T. The leg is the same width as a setField leg, with 32 more PIs (40 completion pins instead of 8). Expect roughly a 5× cut in R3 producer time for a session. This is not measured: no prover was run.
- **Engineering, remaining.**
  - Lean: O1 lifts, emitting, registry insertion and `#guard` updates. About 1 day.
  - Rust: selector, Effect variant, trace row, wide producer lanes, finalize recipe, F1–F3. About 3–4 days.
  - The registry regen and pin updates are mechanical once ember opens the epoch.

## 7. Measurement result

NOT RUN. `cargo test -p grain-turn --no-default-features --test ledger_head_delta` compiles. On the Mac
worktree it fails before reaching any assertion, with `mandate refused tool call: … the verified
admission oracle (dregg_deleg_admit) reached NO VERDICT: Lean static lib not linked`.
`ToolGatewayMinter` needs the Lean FFI archive, and this worktree has no built metatheory. It is
deliberately not pointed at the main tree's `.lake` (`DREGG_METATHEORY_DIR`), because that would write
into another tree. Run it where `dregg-lean-ffi` links (hbox, `swarm-build`). Its result decides D3:
if the balance delta is 0, the fee leg can be dropped.

## 8. Decisions only ember can make

- **D1, the selector index.** The options:
  - Repurpose retired 6 (no relayout; follows the `MINT = 14` precedent).
  - Add a fresh column (relayout of every member).
  - Reuse `SET_FIELD = 2`. Rejected: same selector, different param meaning, so an effects-hash aliasing risk against `SetField`.
- **D2, open the VK epoch.** Adding the member rotates both registry digests and the light client's accepted set.
- **D3, bind the fee or not.** If the fee is not bound, the folded head still differs from the ledger head in balance. If it is, decide whether `turn.fee` is also published as a PI (the `transferFeeV3` / `ROT_FEE_PI` precedent) so a stranger reads it, instead of only through the commitments.
- **D4, how general.** The options are a grain-specific member (fixed mask {3..7}, this design) or a mask-parameterised family. Attested grain turns (slot 8, outside the 8-field block) remain unfoldable either way.
- **D5, whether R3 should bind the ledger head at all.** The alternative is to keep and document the EffectVM-model head. That is cheaper and needs no epoch, but it leaves the balance as well as the nonce unfaithful.
