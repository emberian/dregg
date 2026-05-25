# DSL-to-Effect-VM feasibility study

> Can the `EffectVmAir` in `circuit/src/effect_vm.rs` (8,339 lines, hand-written) be
> regenerated from an enhanced `pyana-dsl` IR, such that all 7 backends
> (`gen_air`, `gen_kimchi`, `gen_plonky3`, `gen_sp1`, `gen_midnight`, `gen_datalog`,
> `gen_rust`) can produce the AIR + executor projection from a single declarative
> source?

**Verdict: FOOL'S ERRAND, in the strict form.** The Effect VM is not a row-shaped
constraint at all; it is a 46-instruction VM whose state, aux, PI, witness, and
boundary layouts encode the entire abstract machine, with hand-tuned aux-column
sharing and Lagrange tricks for degree control. Pyana-dsl is a row-shaped
constraint DSL with no aux-column abstraction, no inter-row constraint kind, no
boundary kind, and stubs for the hash/Merkle primitives the VM is *built out of*.

The honest second answer: **PARTIAL is feasible and useful**, but only for the
per-variant inner constraint shape (one variant at a time, as a degree-9
polynomial in 14 state cols + 8 param cols), not the whole machine. The
scaffold — selector exclusivity, multi-row continuity, aux-column allocation,
boundary pinning, custom-effect count sum-check, PI variable-length appendix —
stays hand-written. That cut is honest, useful, and *much* smaller than
"DSL-author the whole VM."

Below: the gap, the lift, the cut, and the recommended Plan B (Custom dispatch
wiring + cross-backend differential testing).

---

## 1. The expressiveness gap, enumerated concretely

Each row is "DSL feature → can current IR (see `pyana-dsl/src/ir.rs`) express it?"

### 1.1 Selector exclusivity: `Σ s_i = 1` and `s_i ∈ {0,1}` for 46 selectors

`EffectVmAir::eval_constraints` lines 1495–1510. Two-phase: (a) every selector
times `(s − 1)` is asserted zero; (b) the *sum* of all 46 selectors minus one is
asserted zero.

- The boolean part fits `RequirementKind::Equal` if we permit
  `s * (s - 1) == 0` as a richer left-hand side. **Current IR cannot:**
  `RequirementKind::Equal { left: Expr, right: Expr }` parses `require!(a == b)`
  where `a` and `b` come from `expr_to_ident_string` (parse.rs:341), which
  collapses to `Ident` or `Lit`. Polynomial expressions in selectors are not
  representable.
- The 46-ary sum has no IR. `Statement::Match` is the closest construct, but
  match arms don't share an exclusivity constraint at IR level — `gen_air.rs`
  emits *one selector column per match construct* (line 208), and
  `gen_plonky3.rs` (lines 257–284) hand-codes a `sel * (sel - 1) == 0` only for
  binary matches.

**Verdict: not expressible.** Would need either (a) `RequirementKind::OneHot {
columns: Vec<String> }` or (b) a richer expression AST that admits products of
column references.

### 1.2 14-column state with named offsets

The Effect VM uses `state::{BALANCE_LO, BALANCE_HI, NONCE, FIELD_BASE+0..7,
CAP_ROOT, STATE_COMMIT, RESERVED}` — a named record (`pub mod state`). The IR
has `Param { name, ty: ParamType, mutable }`. `ParamType::ByteArray32` (8
limbs) is the closest analog of multi-column, but the IR cannot express *named
sub-fields* of a parameter, and it cannot bind multiple semantically-distinct
columns to a single conceptual "state."

**Verdict: not expressible.** Would need a `ParamType::Record { fields: Vec<(name, ParamType)> }`
or a dedicated `StateBlock` IR construct.

### 1.3 8 param columns reused with variant-specific meanings

`pub mod param` (effect_vm.rs:388–517) overloads the same 8 columns:
`AMOUNT = 0 = FIELD_INDEX = 0 = CAP_ENTRY = 0 = NULLIFIER = 0 = NOTE_COMMITMENT = 0`.
The same column `PARAM_BASE+0` is read as `amount` by Transfer, as
`field_index` by SetField, as `cap_entry` by GrantCap, etc. — gated by
selector. This is "union" or "variant" semantics at the column level.

`ParamType` is a closed enum (U64, ByteArray32, ByteMatrix32(u32), Set,
UserDefined). It does not admit per-arm-rebinding of parameter slots.
`Statement::Match` arms don't expose param-column slots — each arm body is a
list of statements, but those statements refer back to the *function's*
parameters by name.

**Verdict: not expressible.** Would need an `enum-discriminant-overlay`
construct: `Statement::Match` arms become tagged unions over a shared "param
slot table," each arm binding its own names to slots.

### 1.4 23 aux columns with cross-row continuity

Aux semantics from `aux_off`:

- `STATE_INTER1..3` — local hashing witnesses (per-row).
- `CUSTOM_COUNT_ACC` — *running sum* across rows. Constraint Group 7
  (effect_vm.rs:3308–3337) enforces `next_acc = this_acc + this.s_custom`.
- `RESERVED_BIT_0..7`, `RESERVED_MODE` — bit decomposition of `old_reserved`,
  per row, but referenced from multiple Effect variants (SetField, Seal,
  Unseal, MakeSovereign).
- `SEAL_POW2_IDX` — Lagrange witness; same column referenced by Seal *and*
  Unseal arithmetic.
- `RESIZE_DELTA_SIGN`, `RESIZE_DELTA_MAG` — ResizeQueue-specific.

The current IR has no aux concept at all. `emit_stark_impl.rs` *internally*
tracks aux columns (lines 84–139) as a by-product of compiling Requirement
shapes — but those aux columns are owned by individual requirements, never
exposed in the IR, never named, never shared, never multi-row.

**Verdict: not expressible.** Aux-column sharing across selector arms is
fundamental to the Effect VM's degree budget. Without it, the same trick
(e.g. one Lagrange witness column reused by Seal and Unseal) is impossible.

### 1.5 Multi-row continuity

```
next[STATE_BEFORE_BASE + i] - local[STATE_AFTER_BASE + i] == 0
```

This is the `next` argument to `eval_constraints` (line 1484). It compares row
*i*'s `state_after` to row *i+1*'s `state_before`, for all 14 state columns.

The IR has no `next` analog. `gen_plonky3.rs:120` reads `main.current_slice()` —
not `next_slice`. `emit_stark_impl.rs` never references a successor row.

**Verdict: not expressible.** This is the cleanest, biggest gap. A row-oriented
constraint DSL where every constraint is single-row simply cannot describe an
execution trace.

### 1.6 Per-variant constraint sets that share aux indices

E.g. `SEAL_POW2_IDX = aux[7]` is shared by Seal and Unseal: both write the same
column (`local[AUX_BASE + aux_off::SEAL_POW2_IDX]`), and both gate their
"`aux_pow2 == 2^field_idx`" Lagrange check by their own selector. If both
selectors are zero (other variant active), the constraint vanishes.

`Statement::Match` arms in the IR are independent constraint scopes. There is
no way to say "arm A and arm B both write column X with the same Lagrange
formula, but gated separately."

**Verdict: not expressible.** Would need a cross-arm aux declaration plus a
selector-gated equality.

### 1.7 Boundary constraints

The Effect VM's `boundary_constraints` method (effect_vm.rs:3342–3509) pins
specific (row, col) cells to specific PI values: row 0 state_commit ==
PI[OLD_COMMIT], last_row state_commit == PI[NEW_COMMIT], row 0 balance_lo ==
PI[INIT_BAL_LO], etc.

The IR has no boundary statement kind. `BoundaryConstraint` exists in the
runtime (`pyana_circuit::stark::BoundaryConstraint`) but is not surfaced in the
IR.

**Verdict: not expressible.**

### 1.8 Poseidon2 hash chains

`Constraint Group 4` (effect_vm.rs:3190–3252) builds a 4-arity tree:
`inter1 = hash_4_to_1(bal_lo, bal_hi, nonce, field[0])`, then
`state_commit = hash_4_to_1(inter1, inter2, inter3, ZERO)`. The arity-4
hash is *evaluated concretely* against trace values during constraint
evaluation (the comment at line 1466 explains "Hash constraints are evaluated
concretely on trace values at FRI evaluation points — they do NOT contribute
polynomial degree").

The IR has `RequirementKind::Poseidon2Hash { inputs, output }`. The arity is
inputs.len(). Hash *trees* would require nesting — `Poseidon2Hash` as an
inline expression — which is currently flat. And critically, the gen_air,
gen_plonky3, gen_kimchi, gen_sp1 backends all emit **stubs** for this kind
(see `gen_air.rs:147–154`, `gen_plonky3.rs:378–382`, etc.).

**Verdict: stubbed.** The DSL has the *syntax* but no backend produces a real
constraint. Trying to author the state commitment tree in DSL today would
silently emit `assert_zero(ZERO)` placeholders.

### 1.9 Merkle membership against committed roots

CapTP variants (ExportSturdyRef, EnlivenRef, DropRef, ValidateHandoff) embed
Merkle witnesses in aux[0..1, 6..7], with the AIR asserting the chosen-hash
chain matches the root in a state field or PI position.

`RequirementKind::MerkleAtPosition { root, leaf, position, siblings, depth }`
exists. All three STARK backends emit **stubs**. `gen_air.rs:138–146`,
`gen_plonky3.rs:373–377`, `emit_stark_impl.rs:112–114`.

**Verdict: stubbed.**

### 1.10 The 46-row selector match

`Statement::Match` supports any number of arms. `gen_plonky3.rs:257–284` only
handles 2-arm matches with proper boolean selectors; for n-ary matches it
gates all arms by the same selector (line 276–280), which is *wrong* — it
collapses to a single arm. The IR has no notion of N selector columns one-hot.

**Verdict: malformed-encodable.** The IR can carry 46 arms but no backend
correctly emits one-hot selectors for them.

### 1.11 Cross-row PI accumulation (effects_hash chained per row)

Effects hash is built off-trace by `compute_effects_hash` (line 1104) and
pinned at row 0 boundary as `PI[EFFECTS_HASH_BASE]`. A future stage might
chain it across rows. Either way: the IR has no construct for an accumulator
that consumes per-row data and exposes the final value to PI.

**Verdict: not expressible.**

### 1.12 PI layout with variable-length custom-effect appendix

`pi::CUSTOM_PROOFS_BASE = 25` and the comment "For each custom effect i
(0..custom_count)" — PI grows with the number of custom effects. The IR has
no PI-layout construct at all; backends infer PI from non-mutable params.

**Verdict: not expressible.**

---

## 2. What the DSL would need to grow

If we wanted the IR to describe `EffectVmAir` declaratively, we'd add at
minimum:

1. **`StateBlock { name, fields: Vec<(name, ParamType)> }`** — a named record
   of columns. Allocates `state_before` and `state_after` as two adjacent
   blocks. Roughly displaces `Param`.

2. **`AuxColumn { name, semantic: PerRow | RunningSum | LagrangeWitness | BoundaryAnchor }`** —
   declared aux columns, indexed by name. Backends must agree on the encoding
   for each semantic.

3. **`Expr` as a real polynomial AST**, not the current `quote!(#left).to_string()`
   identifier-string hack. Sufficient: `Expr = Col(name) | Lit(u64) | Add | Sub | Mul`
   with parser sugar. The Effect VM's `s_setfield * (field_diff_sum -
   (new_value - old_value_at_idx))` shape requires Mul + Sub + parens.

4. **`Statement::Boundary { row: BoundaryRow, col_ref: ColRef, value: PiRef }`** —
   where `BoundaryRow ∈ {First, Last}`, `ColRef = (StateBlock, FieldName) | AuxName`,
   `PiRef = (PiName, Index)`. Backends without boundary support (gen_datalog,
   gen_rust) emit no-ops.

5. **`Statement::Transition { lhs: NextExpr, rhs: LocalExpr }`** — relates
   row *i+1*'s columns to row *i*'s. `NextExpr` and `LocalExpr` share the
   poly-AST. Backends without transition support (gen_kimchi, gen_midnight)
   either reject this IR or compile to a flattened single-row form.

6. **`SelectorTable { variants: Vec<VariantId>, columns: Vec<usize>, exclusivity: OneHot }`** —
   first-class N-ary selector. Different from `Statement::Match` because
   selector columns are *trace columns*, not pattern matches on a Rust value.

7. **`VariantArm { variant: VariantId, body: Vec<Statement>, param_bindings: Vec<(slot: usize, name: Ident, ty: ParamType)>, aux_bindings: Vec<AuxName> }`** —
   per-variant rebind of shared param/aux slots.

8. **`PiLayout { static_fields: Vec<(name, len)>, dynamic_appendix: Option<(per_count: PiName, entry_size: usize, entry_shape: Vec<(name, len)>)> }`** —
   PI declaration, supporting Effect VM's variable-length appendix.

9. **Real implementations of `Poseidon2Hash` and `MerkleAtPosition`** in
   `gen_air.rs`, `gen_plonky3.rs`, `emit_stark_impl.rs`, `gen_kimchi.rs`,
   `gen_sp1.rs`. Today they are stubs (`gen_air.rs:138–154`,
   `gen_plonky3.rs:373–382`); the AIR would silently emit `assert_zero(0)` if
   we tried to author Constraint Group 4 in DSL.

10. **Composite expressions in `RequirementKind::Equal`**, replacing the
    current identifier-string parsing in `parse.rs:341`.

---

## 3. Estimate the lift

Rough engineering effort per change. Each row: aggregate LOC × 7 backends + IR
+ parser. "Risk" is the probability of a backend silently producing an unsound
constraint.

| # | Extension | IR | Parser | gen_air | gen_p3 | gen_kimchi | gen_sp1 | gen_mid | gen_dl | gen_rust | Risk |
|---|-----------|----|--------|---------|--------|------------|---------|---------|--------|----------|------|
| 1 | StateBlock | 40 | 60 | 80 | 100 | 60 | 40 | 80 | 20 | 60 | LOW |
| 2 | AuxColumn (semantics) | 80 | 100 | 150 | 200 | 100 | 80 | 100 | 30 | 80 | **HIGH** (RunningSum semantics differ across backends; easy to silently lose continuity) |
| 3 | Poly Expr AST | 200 | 300 | 200 | 200 | 200 | 100 | 100 | 50 | 100 | MED (Kimchi has hard 5-coeff limit; Plonky3 has degree cap from AirBuilder) |
| 4 | Boundary | 40 | 40 | 60 | 80 | 0 (n/a) | 0 (n/a) | 0 (n/a) | 0 | 0 | MED (backends without boundary silently no-op) |
| 5 | Transition | 60 | 50 | 80 | 200 | 0 (n/a, ABORT) | 0 (n/a, ABORT) | 0 (n/a, ABORT) | 0 | 50 | **HIGH** (kimchi/midnight cannot represent multi-row; silently lossy) |
| 6 | SelectorTable (N-ary one-hot) | 50 | 50 | 80 | 150 | 80 | 60 | 100 | 30 | 50 | MED |
| 7 | VariantArm rebind | 80 | 100 | 150 | 200 | 150 | 100 | 150 | 50 | 100 | **HIGH** (aux slot reuse encoding bugs cause cross-variant interference) |
| 8 | PiLayout (variable appendix) | 50 | 50 | 80 | 100 | 50 | 50 | 50 | 30 | 30 | MED |
| 9 | Poseidon2 real impl | 0 | 0 | 200 | 400 | 200 | 200 | 200 | 0 | 100 | **HIGH** (each backend's hash gadget; gen_plonky3 currently asserts zero) |
| 10 | MerkleAtPosition real impl | 0 | 0 | 300 | 500 | 300 | 200 | 200 | 0 | 100 | **HIGH** (same) |

Sum: roughly **8,000–10,000 lines across the 7 backends + IR + parser**, with
3–4 high-risk extensions where a backend can plausibly emit a constraint that
type-checks, passes the proof-roundtrip differential test on toy inputs, and is
still *unsound* on the Effect VM's combinatorics. The current Effect VM is
8,339 lines.

There is no net engineering win. Worse: the DSL surface area would more than
double. We'd be inventing a second programming language to author a single AIR
that already works.

---

## 4. The honest verdict: **FOOL'S ERRAND** (for the strict question)

The strict question — "can the IR be enhanced so a single declarative source
regenerates the Effect VM circuit + executor projection through all 7
backends?" — fails on several grounds simultaneously:

1. **Three of the seven backends fundamentally cannot represent the Effect
   VM's shape.** `gen_datalog` is Datalog: no field arithmetic, no multi-row
   continuity. `gen_midnight` targets Compact: no native equivalent of an
   `Air<AB>::eval(local, next)` continuity row. `gen_kimchi` targets a
   Pickles-style circuit: copy constraints and gates, no across-row
   transitions. To make the DSL faithful to *those* backends, the IR has to
   forbid multi-row constructs; to make it faithful to the Effect VM, the IR
   has to *require* them.

2. **Cross-variant aux-column sharing is not a "row constraint" thing.** The
   Effect VM has 46 selector arms that overlap on 23 aux columns. Several aux
   columns (`SEAL_POW2_IDX`, `RESERVED_BIT_*`) are written by one set of arms
   and consumed by another. Modeling this in a row-DSL means inventing a
   register-allocator and a per-arm rebind. That's not "extending the IR" —
   that's writing an SSA frontend for VM circuits.

3. **The existing DSL primitive stubs prove the maintenance cost.** Today
   `Poseidon2Hash` and `MerkleAtPosition` parse, type-check, and emit code in
   every backend — but all four STARK backends emit `assert_zero(ZERO)` (a
   tautology). If we add the Effect VM's commitment tree to the DSL, the
   default backend behavior is to silently produce an unsound circuit. The
   exact bug class is: "DSL author writes the right declaration; backend X
   silently emits a placeholder; nobody notices for months."

4. **The custom-effect-count sum-check and PI variable-length appendix
   together require IR features that no row-oriented DSL has: a column whose
   semantic is `RunningSum`, plus a PI layout where `len(PI) =
   BASE_COUNT + count * 8` and `count` is itself a PI element.** This is not a
   minor extension. It is changing the IR from "describe the constraints on
   one row" to "describe an entire abstract machine."

5. **The Effect VM is still actively growing.** STAGE-7-PLUS-DESIGN and
   STAGE-7-GAMMA-AGGREGATION-DESIGN both contemplate *more* variants and
   *cross-cell* binding (a second level of aggregation above the per-cell AIR).
   Investing 8–10kloc to lift today's Effect VM into the DSL just to chase a
   moving target through DSL extensions afterward is a poor allocation.

The Effect VM is a specific, hand-tuned compiler IR for a specific abstract
machine. Pyana-dsl is a row-shaped constraint description language. Saying
"can the second express the first" is roughly like asking "can our YAML schema
language emit our Rust borrow checker." The answer is yes, in some Turing-
universal sense, by growing the YAML schema language into a programming
language. But you don't actually want to do that.

---

## 5. PARTIAL fallback: per-variant authoring is real and useful

The cut: **the Effect VM scaffold stays hand-written, but the per-variant
arithmetic body can be DSL-authored.**

What "scaffold" means:
- The 14-col state layout (`state::*`).
- The 8-col param layout (`pub mod param`).
- The 23-col aux layout (`pub mod aux_off`) and *allocation* of slots.
- The 46-way selector exclusivity (Group 1).
- Row-to-row continuity (Group 3).
- Boundary constraints (`boundary_constraints` method).
- Constraint Group 4 (state-commitment integrity).
- Constraint Groups 5–7 (sign boolean, net_delta binding, custom-count
  sum-check).
- PI layout.

What "per-variant" means:
- The body of `Transfer` (lines ~1592–1637): `new_bal_lo = old_bal_lo +
  amount * (1 - 2 * direction)`, hi unchanged, fields unchanged, cap_root
  unchanged, direction boolean.
- The body of `SetField` (~1639–1796): conditional field write, with the
  sealed-bit Lagrange check.
- The body of each of the other 44 variants.

Each variant body is roughly 30–80 lines of *single-row* arithmetic over
declared state/aux/param columns. *This* is what the DSL is good at. With the
following minimum IR additions:

- A new `Statement::VariantBody { variant: Ident, body: Vec<Statement> }` that
  *consumes* a pre-declared scaffold's columns.
- A poly-AST `Expr` (item 3 of §2 above) covering `Add`, `Sub`, `Mul`, `Lit`,
  `ColRef(StateBlock, field)`, `ColRef(Aux, name)`, `ColRef(Param, name)`.
- A pre-declared scaffold as a Rust trait the macro consumes
  (`trait EffectVmScaffold { fn state_before_col(field: &str) -> usize; ... }`)
  so the DSL can resolve names.
- Real (non-stub) backend emission for `Equal`, `Mul` expressions, and
  selector-gated bodies. The Plonky3 and gen_air backends already handle
  selector-gated `assert_zero` via `Statement::Match`; extending this to
  N-arm one-hot selectors driven by a column-vector is bounded.

Scope: about **1,500–2,500 lines across IR + parser + 4 STARK backends**
(gen_kimchi, gen_midnight, gen_datalog can flatly reject `VariantBody` for
their target, since the scaffold doesn't exist on those backends).

What this **does NOT buy**:
- Re-generating the Effect VM in Kimchi/Midnight/Datalog. The scaffold is
  STARK-specific; the cut means only `gen_air`, `gen_plonky3`, `gen_rust`,
  `gen_sp1` (with caveats) are relevant.
- Eliminating the hand-written scaffold (~3,000 lines of effect_vm.rs).
- Removing the existing Stage 1/2 invariants documented in
  `EFFECT-VM-SHAPE-A.md`.

What it **does buy**:
- New variants (Stage 7-γ's micro-AIRs, possibly Bridge variants) authored in
  ~50 lines of DSL each, instead of ~150 lines of Rust + manual aux allocation.
- A single source of truth per variant's arithmetic, so the Rust evaluator
  (`gen_rust`) and the STARK circuit (`gen_air` / `gen_plonky3`) stay in sync
  *for the arithmetic core* — `gen_diff_test.rs` already exercises this
  exact pattern at the caveat level.

This is the **PARTIAL** verdict. It is meaningful, it has a clean cut, and it
is roughly 20% the effort of the FEASIBLE version.

---

## 6. If FOOL'S ERRAND: what to do instead

The user's other options:

### (b) Make `Effect::Custom` actually wire DSL-authored programs

Today `sel::CUSTOM` (effect_vm.rs:163, ~2176–2211) is a state-passthrough
selector that binds a `(vk_hash, proof_commitment)` pair into the PI. The
verifier separately checks that the external proof matches `vk_hash` and
hashes to `proof_commitment`. The verifier glue is documented but the
DSL→Custom path is not end-to-end:

- `gen_air` produces an `AirConstraintSet` descriptor, not a callable
  `StarkAir` for invocation by the Custom-effect verifier. The descriptor is
  presently used only to *describe* — not to verify — DSL constraints.
- The Custom dispatch needs a VK registry: `vk_hash → StarkAir + verifier
  parameters`. That registry doesn't exist.
- The DSL produces three things per `#[pyana_effect]`: a Rust evaluator
  (used in `turn/src/executor.rs`), an AIR descriptor (currently unused at
  runtime), and a Plonky3 Air struct (currently unused). Wiring Custom to
  invoke either of the latter two is a finite engineering task: ~300 lines,
  largely in `turn/src/executor.rs` and a new VK-registry crate.

**Recommendation: this is the high-leverage move.** It makes the existing DSL
*matter* for the Effect VM without requiring any IR extensions. Today
DSL-authored caveats and effects can be evaluated in Rust but cannot be
*proved* through the Custom path because the Custom path lacks plumbing, not
because the DSL lacks expressiveness.

### (c) Author *new* AIR variants in DSL — incremental adoption

The Effect VM's Stage 7-γ design contemplates micro-AIRs for cross-cell
binding (`STAGE-7-GAMMA-AGGREGATION-DESIGN.md` §1c — Introduce, §4.4 —
ExerciseViaCapability projections). Each such micro-AIR is bounded: 1–3
selectors, a fixed state shape, no cross-row continuity. **These are exactly
the right shape for the PARTIAL extension above** *if* it lands. Without that
extension, they're still small enough to hand-write — micro-AIRs by
construction are bounded.

**Recommendation: pursue (b) first; (c) becomes natural after PARTIAL §5 lands
or after the micro-AIRs accumulate enough hand-written boilerplate that the
DSL ROI tips positive (probably 4+ micro-AIRs).**

### (d) Cross-backend differential testing for the Effect VM

`pyana-dsl/src/gen_diff_test.rs` already builds differential tests that run
the Rust evaluator and the proven AIR against the same inputs and assert they
agree on accept/reject. For the **Effect VM specifically**, an analogous
differential between the executor's Rust evaluator and `EffectVmAir` is the
soundness story today: the executor independently checks balance ranges, net
deltas, and commitment recomputation, then verifies the AIR proof, then
compares.

What it would benefit from:
- A formal `EffectVmAir` *reference evaluator* that runs the AIR's polynomial
  constraints in plain Rust on the trace (no FRI, no STARK) and confirms
  every constraint evaluates to zero. This is roughly the existing
  `verify_state_integrity` (line 4739) generalized. ~500 lines.
- A property-based testing harness that generates random Effect sequences and
  asserts (Rust executor result) == (AIR-evaluated result) == (proved-then-
  verified result). The existing `tests` module in effect_vm.rs (line 4831)
  is the seed.

**Recommendation: a property-test harness is high-value and low-cost. ~1,000
lines, all in `circuit/tests/` or a new test crate.**

---

## 7. Soundness landmine inventory

If anyone proceeds with §5's PARTIAL plan and DSL backends start authoring
real Effect VM constraints, the audit story is:

1. **Backends silently emitting placeholders.** Today
   `gen_air.rs:138–154`, `gen_plonky3.rs:373–382`, `emit_stark_impl.rs:112–117`
   all emit `Constraint::Equality { desc: "merkle_at_position (stub)" }` or
   `AB::Expr::ZERO` for `MerkleAtPosition` and `Poseidon2Hash`. These compile,
   they pass the IR-level type checks, they may even round-trip the
   differential test for *trivial* witnesses where the stub happens to hold.
   They are unsound. **Audit story: ban any DSL author from using a kind
   whose backend emission is a stub. Mechanism: add a `Backend::supports(kind)
   -> bool` method, fail the macro when a target backend lacks the kind.**

2. **`Statement::Match` with >2 arms in `gen_plonky3.rs`.** Lines 274–280
   gate *all* arms by the same selector when arms.len() ≠ 2 — which is wrong
   (no exclusivity, all arms fire simultaneously). The current macro produces
   2-arm matches in practice; a 3-arm match silently emits broken code. **Audit
   story: reject N-arm matches in gen_plonky3 until N-ary one-hot lands.**

3. **Aux-column allocation drift.** `emit_stark_impl.rs::compute_layout` and
   `gen_plonky3.rs::compute_p3_layout` are *two independent* allocators
   walking the same IR. They use the same widths today (see comments). If a
   new aux-using requirement is added to one but not the other, the column
   offsets diverge and constraints reference the wrong columns. **Audit
   story: unify aux allocation into one shared module before adding any new
   IR construct.**

4. **Constraint degree.** `compute_max_degree` (`emit_stark_impl.rs:142–176`)
   estimates degree statically. The Effect VM's degree is *9* (because of the
   field_idx range-check product `∏(field_idx - k)`). The current DSL
   estimator caps degree-9 constructs as degree 2 or 3. If we add poly-Expr
   without updating the estimator, the prover may attempt FRI with an
   under-sized quotient polynomial → unsound. **Audit story: any expression-
   construct addition requires a static-degree analyzer update *and* a
   property-based test that randomly compiles DSL inputs and checks the
   declared degree matches the actual degree of the emitted polynomial.**

5. **Continuity holes in Datalog/Midnight/Kimchi.** If `Statement::Transition`
   is added (§2 item 5), and these backends silently elide it because their
   target doesn't support row-successor reasoning, a developer reading the
   Datalog encoding will see a constraint set that *looks* complete but isn't.
   **Audit story: backend Mismatch returns a hard error when a kind it cannot
   represent appears in the IR. No silent passthrough.**

6. **PI matching outside the AIR.** The Effect VM's PI matching loop in
   `turn/src/executor.rs:1192–1235` and the boundary constraints in
   `effect_vm.rs:3342–3509` are *complementary*: some PI positions are bound
   by AIR boundary constraints, others (Stage 1 widened positions 1..3 of the
   4-felt commitments) are bound only by executor PI-match. If a DSL-authored
   variant of the Effect VM changes the PI layout, the executor's matching
   loop must be regenerated in lockstep. **Audit story: PI layout must be a
   shared declaration (item 8 of §2) that both the AIR generator and the
   executor consume.**

---

## 8. Closing

The Effect VM is not a constraint, it is a compiler IR. The DSL is a
constraint description language. They sit at different rungs of the same
ladder, and lifting one to the other is not an "enhance the IR" project — it
is a "write a new IR" project. The work would be ~8–10kloc of careful
backend engineering with several high-risk soundness landmines, in service of
a fixed-size deliverable (the existing 8,339 lines of `effect_vm.rs`) that is
*already done*.

The PARTIAL cut (§5) is real, well-bounded, and gets the DSL into the Effect
VM's per-variant arithmetic without rebuilding the scaffold. It's worth doing
when there are 4+ new variants on the docket (e.g. Stage 7 micro-AIRs land
and we have to author them anyway).

The highest-leverage move *today* — independent of DSL extensions — is (b):
make `Effect::Custom` actually invoke DSL-authored programs end-to-end. That
gives the DSL meaningful runtime presence in the Effect VM without any IR
work. Stack (d) on top (property-based diff testing of the executor against
the AIR) and the Effect VM gets a much stronger soundness story than any DSL
extension could deliver.

Recommended ordering, descending value:

1. **(b) Custom dispatch wiring** — high value, no IR work, finite scope (~300 LOC).
2. **(d) Property-based differential testing** — high value, no DSL changes (~1,000 LOC).
3. **PARTIAL §5** — only if Stage 7-γ micro-AIRs land and the marginal
   variant cost begins to bite (~2,000 LOC).
4. **Full FEASIBLE** — do not pursue.
