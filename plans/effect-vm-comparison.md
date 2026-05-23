# Effect VM vs. o1vm: Design Comparison and Analysis

## Executive Summary

Our Effect VM (65 columns, 18 selectors, BabyBear STARK) is fundamentally a different
kind of circuit than o1vm (143 columns, 66 selectors, IPA over Pasta curves). o1vm proves
arbitrary MIPS/RISC-V execution with full memory addressing; our VM proves a fixed set of
18 domain-specific effects operating on a small structured cell state. **Our design is
appropriate for our use case** but has specific gaps that o1vm handles better via lookup
arguments and explicit RAM checking.

---

## 1. Architecture Comparison

| Dimension | Effect VM | o1vm (MIPS flavor) |
|-----------|-----------|-------------------|
| Total trace width | 65 columns | 143 columns |
| Selector columns | 18 (one-hot) | 66 (one-hot) |
| Relation/scratch columns | 47 | 77 (63 scratch + 12 inverse + counter + error) |
| Constraint degree (max) | 9 | 6 |
| Proof system | FRI-based STARK (BabyBear) | IPA over Pasta (Kimchi/Pickles) |
| Memory model | State commitment hash (Poseidon2) | RAM lookup argument (Logup) |
| Lookup tables | None | 11 tables (byte, range-16, memory, register, etc.) |
| Trace length | Power-of-2, typically 2-32 rows | Fixed 2^16 per segment |
| Instruction set | 18 fixed effects | ~65 MIPS instructions |
| Constraint count | ~180 (estimated) | 466 |

---

## 2. Selector Efficiency

**Question:** We use one-hot (18 columns). Should we use binary encoding (5 columns)?

**o1vm's approach:** Also one-hot. 66 selector columns for 65 instructions + NoOp. They
chose one-hot despite the column cost because:

1. **Constraint gating is trivial:** `selector_i * constraint = 0` is degree 2. With
   binary encoding, gating requires decoding first (product of selector bits), adding
   degree log2(N) to every gated constraint.

2. **Selector validity is cheap:** One-hot requires N boolean checks + sum=1 (all degree
   1-2). Binary encoding requires only log2(N) boolean checks but then each constraint
   needs an N-factor decoder polynomial.

3. **o1vm has 66 selectors for 65 instructions.** They did NOT compress.

**Verdict:** Our 18 one-hot selectors cost 18 columns but keep constraint degree at
`selector * expression` = max degree 9. With binary encoding (5 columns), the selector
decode would be degree 5 (product of 5 bits/complements), making our field-index range
check `decode * prod(idx-k)` = degree 5+8 = degree 13. This is worse. **Keep one-hot.**

The 13-column savings (18 -> 5) would save ~20% of columns but raise constraint degree
from 9 to 13+, requiring a proportionally larger quotient domain. Net effect: likely
negative for our small traces.

---

## 3. State Threading: Hash vs. RAM Argument

**Our approach:** Every row hashes all 14 state elements into a `state_commitment` via
Poseidon2 tree (3 intermediate + 1 root = 4 hash calls per row). State continuity is
enforced by `next_row.state_before == this_row.state_after` on all 14 columns.

**o1vm's approach:** Memory and registers use a **RAM lookup argument (Logup/permutation)**:
- Memory reads/writes are logged as lookup entries: `(address, value, timestamp)`
- A permutation argument proves that every read was preceded by a matching write
- No hashing needed per row; the lookup argument is amortized over the full trace

**Analysis for our use case:**

Our state is *tiny*: 14 field elements per row. A RAM argument would require:
- 3-4 extra lookup columns per memory access
- A separate accumulator polynomial
- Larger verifier work for the grand product check

For o1vm with ~19 memory/register accesses per instruction (MAX_ACC = 19), the RAM
argument is essential since hashing 32 registers + arbitrary memory per row would be
astronomically expensive.

For us: 14 elements hashed via Poseidon2 (which is native to BabyBear STARKs, ~1 hash
per round) is actually very efficient. The hash approach also gives us:
- **Succinct public inputs:** Only old_commitment and new_commitment in PI
- **Composability:** External proofs can reference our state by commitment
- **Privacy:** The commitment hides internal state from the verifier

**Verdict:** Our hash-based approach is correct for our use case. A RAM argument would
add complexity without benefit for 14 elements. However, see Section 5 for when this
might change.

---

## 4. Constraint Degree

**Effect VM:** Max degree 9 (SetField/Seal/Unseal: selector * prod_{k=0}^{7}(idx - k))

**o1vm:** Max degree 6 (selector * constraint, where inner constraints are degree 5 for
things like `num_bytes * (num_bytes - 1) * (num_bytes - 2) * (num_bytes - 3) * (num_bytes - 4)`)

**Why o1vm is lower:** o1vm uses **lookup tables** to handle range checks and value
decomposition. Where we do `prod_{k=0}^{7}(field_idx - k) == 0` (degree 8, gated to 9),
o1vm would do a lookup into a table of valid values (degree 1-2 for the lookup itself).

**Impact:**
- Degree 9 requires evaluating on a domain of size >= 9N (we use the trace domain with
  appropriate blowup). FRI blowup factor must accommodate this.
- Degree 6 (o1vm) allows evaluation on 8N domain (hence their d8 evaluation domain).
- For our small traces (16-32 rows), the absolute domain sizes are still tiny:
  9*32 = 288 vs 6*32 = 192. Both are negligible.

**Verdict:** Degree 9 is fine for our small traces. If we later need to support longer
traces (100+ effects per turn), consider replacing the degree-8 range check product with
a lookup table. This would reduce max degree from 9 to 3 (selector * expression).

---

## 5. Trace Padding

**Effect VM:** Pad to power-of-2. For 3 effects: pad to 4 rows (25% wasted). For 1
effect: pad to 2 rows (50% wasted). For 5 effects: pad to 8 rows (37.5% wasted).

**o1vm:** Fixed segment size of 2^16 = 65536 rows. Each segment proves exactly 65536
instructions. The last segment is padded. For a program with 100K instructions: 2
segments, second one is 46% wasted.

**Analysis:** o1vm's waste is *far worse* in absolute terms (padding 30K+ rows vs our
1-15 rows). They accept this because:
1. They batch-prove millions of instructions (waste is small relative to total)
2. They use fixed SRS size (IPA commitment requires known degree)
3. Multiple segments are aggregated via recursive composition (Pickles)

For us: typical turns have 1-18 effects. Padding waste:
- 1 effect -> 2 rows (50% waste, but 2 rows is tiny)
- 5 effects -> 8 rows (37.5% waste)
- 18 effects -> 32 rows (43.75% waste)

**With BabyBear FRI-STARK, the cost of padding is minimal.** The prover work is
dominated by NTT and Poseidon hashing, both of which scale with trace_height * width.
For 32 * 65 = 2080 field elements, the entire trace fits in a few KB.

**Verdict:** Our padding approach is appropriate. The waste is negligible in absolute
terms. If we wanted to optimize, we could use a variable-length trace with a
"last real row" marker, but the complexity is not justified for traces under 64 rows.

---

## 6. Memory Model

**Effect VM:** State is a flat vector of 14 fields. The entire state is materialized in
every row (state_before and state_after). Total: 28 state columns per row.

**o1vm:** Registers are 32 GP + 5 special = 37 registers, accessed via lookup. Memory is
page-based (4KB pages), also accessed via lookup. Only the *accessed* registers/memory
appear in each row (via scratch columns).

**For our cell state model:**

Our cells have a fixed, small state: balance (2 limbs), nonce, 8 fields, cap_root,
commitment, reserved = 14 elements. This is smaller than MIPS registers (37) and MUCH
smaller than MIPS memory (4GB addressable).

The tradeoff:
- **Materializing full state per row (our approach):** 28 columns dedicated to state,
  but no lookup overhead. Simple transition constraints. State is always available.
- **Lookup-based state (o1vm approach):** Only accessed state appears in scratch columns,
  but requires RAM argument infrastructure (accumulator, grand product, timestamp
  tracking).

For 14 elements, materialization wins. The break-even point would be ~50+ state elements,
where the lookup overhead (3-4 columns + accumulator) starts paying for itself by not
materializing unused state.

**Verdict:** Our approach is correct. The cell state model is small enough that full
materialization is cheaper than a RAM argument.

---

## 7. Soundness Analysis

### 7.1 Zero-Selector Attack

**Risk:** Can an adversary set all selectors to 0, bypassing all gated constraints?

**Our defense:** `sum(selectors) == 1` constraint. This is NOT gated by any selector,
so it is always enforced. If all selectors are 0, sum = 0 != 1, and the constraint
fails. **Sound.**

**o1vm's approach:** Identical. They enforce boolean + sum=1 for all selectors as
ungated constraints.

### 7.2 Balance Underflow (documented in our code)

**Risk:** Modular arithmetic in BabyBear means `old_bal - amount` wraps around when
`amount > old_bal`, producing a valid-looking field element.

**Our defense (multi-layered):**
1. Executor-side validation (rejects underflow before trace generation)
2. State commitment hash chain (wrapping produces wrong commitment)
3. Boundary constraints pin initial and final commitments to public inputs

**o1vm's approach:** Explicit range checks via **RangeCheck16** lookup table. Every
arithmetic result that must be non-negative is decomposed into 16-bit limbs, and each
limb is looked up in the range table. This is provably sound without relying on
executor honesty.

**Gap in our design:** A malicious prover (not using our executor) could craft a trace
with wrapped balance values on interior rows. The state commitment chain catches this
at boundaries, but the security relies on Poseidon2 preimage resistance rather than
explicit range proofs.

**Recommendation:** When we add lookup support, add a range check for `new_balance_lo`
on all debit rows. Two lookups into a 2^15 table suffice for 30-bit range proof.
Priority: MEDIUM (current defense via commitment chain is sound assuming Poseidon2
security, but explicit range checks are defense-in-depth).

### 7.3 Selector-Index Mismatch

**Risk:** A malicious prover could set `field_idx` to a value outside {0..7} on a
SetField row, causing undefined behavior.

**Our defense:** Degree-8 vanishing product `prod_{k=0}^7(field_idx - k) == 0`, gated
by selector. This is sound: any value outside {0..7} makes the product non-zero.

**o1vm's approach:** Would use a lookup into a table of valid values. Lower degree
but equivalent soundness.

### 7.4 Auxiliary Column Manipulation

**Risk:** A prover controls aux column values. Can they set aux values to bypass hash
constraints?

**Our defense (post-soundness-fix):** Hash constraints in eval_constraints compute
`hash_2_to_1(...)` directly on trace values. The constraint is:
`selector * (new_cap_root - hash_2_to_1(old_cap_root, cap_entry)) == 0`

The hash is computed by the VERIFIER at each FRI evaluation point, not taken from
prover-supplied aux values. **Sound.** (The earlier version trusted aux[1] which was
unsound; this was fixed.)

State commitment tree intermediates (aux[8..10]) are constrained to equal specific
hash computations. A malicious prover cannot forge these without breaking Poseidon2.

---

## 8. Proof Size Comparison

### Effect VM (BabyBear FRI-STARK, 65 columns, 32 rows)

Estimated proof components:
- Trace commitments: Merkle roots for 65 columns (65 * 32 bytes = ~2KB hashes)
- FRI layers: log2(32) = 5 layers, each with ~32 * field_size queries
- Query phase: ~30 queries * path length * column count
- **Estimated total: ~50-100 KB** for security parameter ~100 bits

### o1vm (IPA over Vesta, 143 columns, 65536 rows)

Proof components:
- Column commitments: 143 IPA commitments (143 * 33 bytes = ~4.7KB)
- Quotient commitment: 7 chunks * 33 bytes = 231 bytes
- Evaluations at zeta, zeta_omega: 143 * 2 * 32 bytes = ~9KB
- IPA opening proof: ~32 rounds * 2 group elements = ~2KB
- **Estimated total: ~15-20 KB** (IPA is succinct)

### Key Insight

o1vm has MUCH smaller proofs despite wider traces because:
1. IPA commitments are succinct (single group element per polynomial)
2. The opening proof size is logarithmic in trace length
3. FRI proofs are larger (Merkle paths for each query)

However, our proof is for a **much simpler computation** (18 effects vs 65536 MIPS
instructions). The comparison is not apples-to-apples.

For our use case, proof size of 50-100KB is acceptable for on-chain verification
(compressed to ~20-30KB with standard techniques). If proof size becomes critical,
switching to a Plonky3 backend (which we already have) with better FRI parameters
can reduce this.

---

## 9. Specific Recommendations

### Keep As-Is (our design is appropriate):

1. **One-hot selectors** - Same approach as o1vm, correct tradeoff for our degree budget
2. **Hash-based state threading** - Correct for 14-element state; enables composability
3. **Full state materialization** - Cheaper than RAM argument for our state size
4. **Power-of-2 padding** - Negligible waste for traces under 64 rows
5. **Selector-sum=1 constraint** - Sound defense against zero-selector attack

### Adopt from o1vm (priority improvements):

1. **[HIGH] Lookup tables for range checks** - Replace degree-8 vanishing products with
   lookups. Benefits:
   - Reduces max constraint degree from 9 to 3
   - Enables in-circuit balance range proofs (currently executor-only)
   - Plonky3 supports log-derivative lookups natively
   - Implementation: Add a 2^8 or 2^15 range table, use for field_idx and balance limbs

2. **[MEDIUM] Explicit balance non-negativity proof** - Add lookup-based range check on
   `new_balance_lo` for all debit effects (Transfer out, NoteCreate, CreateObligation).
   Currently relies on commitment chain + executor validation.

3. **[LOW] Batch inversion column** - o1vm uses dedicated `ScratchStateInverse` columns
   (12 of them) for batch-computing inverses. We currently compute inverses inline in
   witness generation for DropRef. If we add more non-zero proofs, a dedicated inverse
   column would be cleaner.

### Do NOT adopt from o1vm:

1. **RAM lookup argument** - Overkill for 14-element state. Would add ~20 columns and
   significant prover complexity for no benefit.

2. **Fixed large trace segments** - o1vm uses 2^16 row segments. Our traces are 2-32
   rows. Fixed large segments would waste >99.9% of the trace.

3. **IPA/Pasta curves** - We correctly use BabyBear + FRI for prover speed. IPA gives
   smaller proofs but slower proving. Our use case (turn execution on user devices)
   prioritizes prover speed.

4. **Symbolic constraint framework (Expr)** - o1vm uses Kimchi's expression AST for
   symbolic constraint manipulation. Our direct evaluation approach is simpler and
   sufficient for 18 fixed effects. (If we ever need dynamic constraint composition,
   reconsider.)

---

## 10. Summary

| Aspect | Assessment | Action |
|--------|-----------|--------|
| Selector encoding | Correct (matches o1vm) | None |
| State model | Correct for our state size | None |
| Constraint degree | Acceptable but improvable | Add lookups when ready |
| Balance soundness | Adequate but not optimal | Add range check lookups |
| Trace efficiency | Good for our workload | None |
| Proof size | Acceptable | Monitor; Plonky3 helps |
| Zero-selector | Sound | None |
| Composability | Better than o1vm (hash commits) | None |

**Bottom line:** Our Effect VM is well-designed for its purpose. It is simpler, narrower,
and more efficient than o1vm for our workload (small structured state, few effects per
turn). The main gap is the lack of lookup-based range checks, which would improve both
soundness guarantees and constraint degree. This should be the next improvement when we
integrate Plonky3's lookup infrastructure.
