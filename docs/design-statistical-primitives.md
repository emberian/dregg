# Statistical Primitives in the Pyana DSL

## Problem

The compute marketplace requires provable statistical claims: SLA compliance, reputation scoring, service quality attestation. Concrete examples:

- "This worker's p95 latency is below 200ms"
- "Uptime was 99.5% over 30 days"
- "Latency variance stayed below threshold"
- "Response time distribution fits within these buckets"

These must be expressed as AIR constraints over BabyBear (31-bit prime field), which has no floats, no real division, and no square root.

## Core Insight: Separate Accumulation from Interpretation

The circuit proves ACCUMULATION was correct. The verifier INTERPRETS the accumulated values off-chain. This avoids division and irrational arithmetic inside the field entirely.

The proof says: "I correctly computed sum=X, sum_squares=Y, count=N, over_threshold_count=K, bucket_counts=[a,b,c,d,e]." The verifier computes mean = X/N, variance = Y/N - (X/N)^2 in real arithmetic and checks whatever policy threshold applies. The circuit never divides.

## What Exists Today

The temporal accumulator (`design-temporal-accumulation.md`) already defines columns for `sum`, `sum_squares`, `min_val`, `max_val`, `ema`, and wires them through IVC. The `ConstraintExpr` enum in `pyana-dsl-runtime/src/circuit.rs` provides `Polynomial`, `Transition`, `Binary`, `Gated`, and `SelectiveWrite` -- all needed for statistical constraints.

No new `ConstraintExpr` variants are required. Statistical primitives decompose entirely into existing constraint types.

## Four Patterns

### 1. Running Accumulators (mean, variance)

Transition constraints on dedicated columns:

```
next.sum == local.sum + local.measurement
next.sum_squares == local.sum_squares + local.measurement * local.measurement
next.count == local.count + 1
```

These are degree-1 and degree-2 `Polynomial` transition constraints. The boundary constraint exposes final values as public inputs. The verifier computes mean and variance from `(sum, sum_squares, count)`.

Constraint cost: 3 transition constraints, 3 columns. Negligible.

### 2. Threshold Percentile (p95, p99)

Instead of computing exact percentiles (which requires sorting -- O(n log n) constraints), prove the equivalent: "at most K% of measurements exceeded threshold T."

```
// Per-step: increment counter when measurement > threshold
// Uses existing range-check pattern: decompose (measurement - threshold) into bits,
// check the sign bit to determine over/under
next.over_count == local.over_count + local.is_over
```

Boundary constraint (integer arithmetic, no division):

```
row(last).over_count * 100 <= row(last).count * max_percent
```

The `<=` compiles to: `count * max_percent - over_count * 100` is non-negative, proven via bit decomposition (existing `Binary` constraints on range bits).

Constraint cost: 1 transition constraint + 1 range check per step for the is_over flag, 1 range check at boundary. Columns: `over_count`, `is_over` (binary), plus ~30 range bits for the boundary check.

### 3. Committed Histogram

The prover assigns each measurement to exactly one bucket. Per step:

```
// Selector columns: exactly one is 1
binary!(bucket_sel_0); binary!(bucket_sel_1); ... binary!(bucket_sel_k);
require!(bucket_sel_0 + bucket_sel_1 + ... + bucket_sel_k == 1);

// Range check: measurement falls within selected bucket boundaries
// (gated range checks per bucket)
gated!(bucket_sel_i, range_check(measurement, bucket_lo_i, bucket_hi_i));

// Accumulate counts
next.bucket_count_i == local.bucket_count_i + bucket_sel_i;
```

Boundary constraint:

```
row(last).bucket_count_0 + ... + row(last).bucket_count_k == row(last).count
```

Constraint cost: k selector columns (binary), k transition constraints for counters, k gated range checks. For 5 buckets: ~5 selectors + 5 counters + 5 gated range checks = ~40 additional columns (including range bits).

### 4. Exponential Moving Average

EMA with rational smoothing factor alpha = p/q:

```
next.ema * q == local.measurement * p + local.ema * (q - p)
```

This is a SINGLE degree-2 polynomial constraint. For alpha = 1/10: `next.ema * 10 == measurement + 9 * ema_old`. Linear in the trace, quadratic only because of the multiplication by q (which is a constant, so actually degree 1 via `Polynomial` with constant coefficients).

Constraint cost: 1 polynomial constraint, 1 column. The cheapest statistical primitive.

## DSL Sugar (Built-in Macros)

These expand to combinations of existing `ConstraintExpr` types at compile time:

```rust
// Expands to: Transition polynomial + Boundary PiBinding
running_sum!(sum_col, value_col)

// Expands to: Transition polynomial (degree 2) + Boundary PiBinding
running_sum_squares!(sum_sq_col, value_col)

// Expands to: Binary selector + range check + Gated transition + Boundary range check
threshold_percentile!(over_count, total, value, threshold, percent_num, percent_den)

// Expands to: k Binary constraints + sum==1 + k Gated range checks + k Transition polynomials
histogram!(value, buckets: [b0, b1, ..., bk], counts: [c0, c1, ..., ck])

// Expands to: single Polynomial constraint (degree 1-2)
ema!(output_col, input_col, alpha_num, alpha_den)
```

No new `ConstraintExpr` variants. No changes to `DslCircuit` evaluation. No changes to the STARK prover/verifier. Pure syntactic expansion.

## Complete Example: GPU Worker Latency SLA

```rust
#[pyana_circuit]
mod latency_sla {
    layout! {
        measurement: Field,           // col 0: this step's latency (ms)
        sum: Field,                   // col 1: running sum
        sum_squares: Field,           // col 2: running sum of squares
        count: Field,                 // col 3: measurement count
        over_200ms_count: Field,      // col 4: measurements > 200ms
        is_over: Binary,              // col 5: 1 if measurement > 200
        ema: Field,                   // col 6: exponential moving average
        bucket_0_50: Field,           // col 7: histogram 0-50ms
        bucket_50_100: Field,         // col 8: 50-100ms
        bucket_100_200: Field,        // col 9: 100-200ms
        bucket_200_plus: Field,       // col 10: 200ms+
        over_diff_bits: [Binary; 16], // cols 11-26: range bits for (measurement - 200)
        boundary_bits: [Binary; 30],  // cols 27-56: range bits for p95 check
        state_root: Field,            // col 57: IVC chain binding
    }

    transition! {
        // Running accumulation (3 constraints, all degree <= 2)
        next.sum == local.sum + local.measurement;
        next.sum_squares == local.sum_squares + local.measurement * local.measurement;
        next.count == local.count + 1;

        // EMA: alpha = 1/10 (1 constraint, degree 1)
        next.ema * 10 == local.measurement + 9 * local.ema;

        // Threshold detection: is_over = (measurement > 200)
        // Proven via range-check on (measurement - 201): if non-negative, is_over=1
        range_check!(local.measurement - 201, over_diff_bits, local.is_over);
        next.over_200ms_count == local.over_200ms_count + local.is_over;

        // Histogram bucket accumulation (gated by is_over and range checks)
        next.bucket_200_plus == local.bucket_200_plus + local.is_over;
        // (bucket_0_50, bucket_50_100, bucket_100_200 use similar gated patterns)
    }

    boundary! {
        first {
            sum == 0;
            sum_squares == 0;
            count == 0;
            over_200ms_count == 0;
            ema == 0;
            state_root == public.initial_root;
        }
        last {
            count == public.total_steps;
            sum == public.final_sum;
            state_root == public.final_root;

            // P95 guarantee: over_200ms_count * 100 <= count * 5
            // i.e., count*5 - over_200ms_count*100 >= 0 (proven via range bits)
            range_check!(count * 5 - over_200ms_count * 100, boundary_bits);
        }
    }
}
```

Trace width: 58 columns. Constraint degree: 2. Per-step cost: ~10 constraints. This fits comfortably within the existing `DslCircuit` framework and compresses via IVC into a single constant-size proof.

## Approximate Standard Deviation (Without Square Root)

Exact stddev requires sqrt, which is not field-native. The workaround: prove a BOUND on variance using only integer arithmetic.

To prove "variance < max_var":
```
sum_squares * count - sum * sum < count^2 * max_var
```

Both sides are computable in BabyBear. The `<` is a range check on the difference. The verifier knows `max_var` as a public parameter. No sqrt needed.

## Integration with IVC and Temporal Accumulator

The statistical accumulator IS the temporal accumulator with histogram columns added. The `state_root` column binds each step to the IVC chain. After N steps, `IvcBuilder::finalize()` produces one proof covering the full measurement history. The verifier checks O(1) data regardless of how many measurements were accumulated.

Columns added beyond what `design-temporal-accumulation.md` already specifies:
- `histogram_counts: [Field; NUM_BUCKETS]` (bucket counters)
- `over_threshold_count: Field` (percentile counter)
- `is_over: Binary` (per-step threshold flag)
- Range bits for threshold detection (~16 columns)
- Range bits for boundary p95 check (~30 columns)

Total additional: ~50 columns. Combined with the existing temporal accumulator (~40 columns for window size 32), the full statistical accumulator is ~90 columns. Well within the 1024-column deployment limit.

## What Needs Implementation

| Component | Status | Work |
|-----------|--------|------|
| Running sum/sum_squares transition constraints | Expressible NOW | Zero -- use existing `Polynomial` transition |
| Threshold percentile (is_over + boundary check) | Expressible NOW | Zero -- use existing `Binary` + `Polynomial` |
| EMA constraint | Expressible NOW | Zero -- single `Polynomial` term |
| Histogram bucket selectors + gated accumulation | Expressible NOW | Zero -- use `Binary` + `Gated` + `Transition` |
| DSL macro sugar (`running_sum!`, `histogram!`, etc.) | Needs new code | Macro expansion in `pyana-macro` crate |
| Witness generation for range-check bits | Needs new code | `WitnessOracle` impl for bit decomposition |
| IVC wiring for statistical accumulator | Exists | Wire `state_root` column to `IvcBuilder` |

The constraint system already supports everything. The work is sugar (macros) and witness generation (prover-side bit decomposition). No changes to the verifier, no new constraint types, no new AIR machinery.
