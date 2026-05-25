# AUDIT — `trace/` (pyana-trace)

> Read-only audit of the `trace/` workspace member. Generated 2026-05-24
> against `main` @ `8a66164`. Working tree has unrelated WIP edits to
> `circuit/`, `intent/`, `turn/`, `wire/` (out of scope).
>
> Companion: `BACKWATER-CRATES-AUDIT.md` (which flagged `trace/policy.rs`
> as "pyana's de facto policy language … load-bearing but never deeply
> audited") plus `PREDICATE-INVENTORY.md`, `BOUNDARIES.md`,
> `SLOT-CAVEATS-DESIGN.md`.

---

## Cargo manifest

`trace/Cargo.toml` is striking for its minimality:

```toml
[package]
name = "pyana-trace"
description = "Derivation trace format and reference evaluator for the pyana ZK token system"

[dependencies]
blake3 = "1"
serde = { workspace = true, features = ["std"] }

[dev-dependencies]
serde_json = { workspace = true }
```

- **Zero pyana-crate dependencies.** Not on `commit`, `types`, `token`,
  `macaroon`, or `circuit`. This is the most self-contained module in
  the auth stack — a fact §7 returns to.
- **Two runtime deps only.** `blake3` for `symbol_from_str` hashing,
  `serde` for trace (de)serialisation. `serde_json` is dev-only.
- **No `thiserror`, no `anyhow`, no `tracing`, no `hex`.** The crate
  refuses ambient stdlib-shaped utility deps.

That isolation is the most important structural fact about the crate.
It can be lifted out of the pyana tree wholesale.

---

## File-by-file walk

LOC counts (including blank lines / comments):

| File | LOC | Role |
|------|-----|------|
| `lib.rs` | 22 | Re-exports + module wiring |
| `types.rs` | 255 | Datalog AST + canonical encoding rules |
| `eval.rs` | 527 | Bottom-up Datalog evaluator (DoS-bounded) |
| `verify.rs` | 420 | Standalone trace verifier (the ZK target spec) |
| `check.rs` | 232 | Constraint-check evaluator (`MemberOf`, `Contains`, comparators) |
| `policy.rs` | **1216** | Standard / legacy / secure / minimal / time-bounded policies + named rule IDs |
| `tests.rs` | 1246 | 44 integration tests; 1:1 with implementation LOC |

Total ≈ 3.9 kLOC of which ≈ 60% is implementation, ≈ 40% tests.

### `lib.rs` (`/Users/ember/dev/breadstuffs/trace/src/lib.rs`)

22 lines. Re-exports the entire public surface:

- `check::eval_check`
- `eval::Evaluator`
- `policy::{secure_policy, standard_policy}` — but **not** `legacy_policy()`,
  `minimal_policy()`, or `time_bounded_policy()`. Those are reachable only
  via `pyana_trace::policy::*`.
- `types::*` — including `symbol_from_str`, `symbol_from_bytes`, every
  enum.
- `verify::{verify_trace, verify_trace_with_request}`.

The module doc comment names four jobs: "Data structures for representing
Datalog derivation traces; A bottom-up Datalog evaluator that records
proof traces; A standalone trace verifier; Standard policy rules for the
pyana authorization model." That's the whole crate.

### `types.rs` (`/Users/ember/dev/breadstuffs/trace/src/types.rs`)

Defines the Datalog AST and the trace data model.

**Key types.**

- `Symbol = [u8; 32]` — BLAKE3 hash of a predicate / constant name.
- `Variable = u32`.
- `Term::{Const(Symbol), Int(i64), Var(Variable)}` — three-way term sum.
- `Atom { predicate: Symbol, terms: Vec<Term> }` — predicate application;
  doc says "Maximum 3 terms per atom" (not enforced by types — see open
  issues).
- `Check::{LessThan, GreaterThan, GreaterThanOrEqual, Equal, Contains, MemberOf}` —
  the six constraint kinds.
- `Rule { id: u32, head: Atom, body: Vec<Atom>, checks: Vec<Check> }` —
  doc says "Maximum 4 body atoms" (also not type-enforced).
- `Fact { predicate, terms }` — ground atom (debug-assert no `Var`).
- `Substitution { bindings: Vec<(Variable, Term)> }` — note: `Vec`, not
  `HashMap`. Lookup is linear; this matters at the verifier (verify.rs
  re-derives the substitution by sequential unification).
- `DerivationStep { rule_id, substitution, body_fact_indices, derived_fact }` —
  the per-step witness shape that the ZK circuit replicates.
- `Conclusion::{Allow { policy_rule_id: u32 }, Deny }`.
- `AuthorizationRequest { app_id, service, action, features: Vec<Symbol>,
  user_id, now: i64 }`.
- `AuthorizationTrace { request, steps: Vec<DerivationStep>, conclusion }`.

**Canonical encoding rule.** Lines 219–255 (`types.rs:219-255`) carry a
prominent doc-comment block: **all string-valued terms MUST go through
`symbol_from_str` (BLAKE3 hash); `symbol_from_bytes` is reserved for raw
32-byte material**. This rule is documented but not enforced at type
level. The `legacy_policy()` tests deliberately violate it to exercise
`Contains` substring matching. See §6 and §2 for the consequences.

**Design choices worth flagging.**

- The two-symbol-constructor design (`symbol_from_str` for namespaces
  and labels, `symbol_from_bytes` for binary handles) is *the* source
  of the substring-vulnerability story in §2 below.
- `Substitution` is a `Vec` of bindings, not a map. Lookups are linear
  scans. For typical pyana rule bodies (≤4 atoms × ≤3 terms ≈ ≤12
  variables) this is fine; if the rule complexity grows, this becomes
  a re-evaluation hotspot.
- `Fact::new`'s `debug_assert` ground-check is debug-only. The verifier
  re-checks groundness on every derived fact (verify.rs:255-262), so
  the assertion is informational.

**TODOs / surprises.** None in the file. Docs are honest about what is
checked vs. what is convention.

### `check.rs` (`/Users/ember/dev/breadstuffs/trace/src/check.rs`)

Shared by `eval` and `verify`. The two are required to agree on `Check`
semantics or the verifier would reject honest traces.

**Six check kinds.**

| Check | Semantics | Notes |
|---|---|---|
| `LessThan(l, r)` | `Int(a) < Int(b)` only | Const-Const, Const-Int, mixed all false |
| `GreaterThan(l, r)` | `Int(a) > Int(b)` | same |
| `GreaterThanOrEqual(l, r)` | `Int(a) >= Int(b)` | same |
| `Equal(l, r)` | full term equality after substitution | works for both `Const` and `Int` |
| `Contains(col, elem)` | UTF-8 substring of zero-trimmed bytes | **DEPRECATED for actions** — see §2 |
| `MemberOf(elem, set_elem)` | exact 32-byte hash equality | secure replacement for `Contains` |

`Contains` carries a long warning doc comment about the substring
collision risk (`"threadwrite"` matches `"write"`). The crate's own
test `test_old_contains_vulnerability_demonstration`
(`policy.rs:1182-1215`) **deliberately demonstrates** the
vulnerability — i.e. the crate keeps a CVE-shaped test green to
preserve a contract with `legacy_policy()` consumers.

**`MemberOf` semantics.** Implemented (`check.rs:53-59`) as
exact equality of `Const(e) == Const(s)` or `Int(e) == Int(s)`. The
doc comment notes that in the *evaluator* this is "belt and suspenders"
because unification of the rule body already binds the action variable
to the matched fact — `MemberOf(Term::Var(1), Term::Var(1))` is always
trivially true after unification. The check exists explicitly so that
the **ZK circuit** has a concrete constraint to enforce: in the
`secure_policy()` rules, `Check::MemberOf(Var(1), Var(1))` is a
deliberate redundancy that compiles to an action-equality constraint in
the prover.

**Test coverage in this file.** 16 tests covering each check kind,
the substring-collision proof, and var-substituted forms. Good.

### `eval.rs` (`/Users/ember/dev/breadstuffs/trace/src/eval.rs`)

Bottom-up Datalog evaluator. ≈ 530 LOC, half of which is tests.

**`Evaluator { facts, rules }`** runs `evaluate(&request) -> AuthorizationTrace`:

1. Clone facts, inject request facts via `inject_request_facts`
   (lines 131–166) — the request becomes `request_app(Const)`,
   `request_service(Const)`, `request_action(Const)`,
   `request_feature(Const)` (one per feature), `request_user(Const)`,
   `request_time(Int)` facts.
2. Loop bounded by `MAX_EVAL_ROUNDS = 1000` (`eval.rs:66`).
3. Per round, call `derive_one_round` over all rules, accumulate
   `DerivationStep`s, push derived facts into the working set.
4. Compute `Conclusion` via `find_conclusion` (`eval.rs:345-379`):
   **explicit `deny` always wins over `allow`** — search for deny facts
   first; if any, return `Deny`. Otherwise return `Allow` with the rule
   id that derived the first `allow` fact. If neither, default `Deny`.

**DoS bounds** (`eval.rs:64-74`):
- `MAX_EVAL_ROUNDS = 1000`
- `MAX_SUBSTITUTIONS_PER_ROUND = 100_000` — enforced in
  `find_all_substitutions_indexed` at line 270
- `MAX_FACTS = 100_000` — enforced after each round at line 115

These exist because user-supplied rules and facts can in principle cause
combinatorial explosion. The bounds are deliberate — they cap memory
and CPU at constants. A run that hits any bound terminates and falls
through to `find_conclusion`, which means **hitting a bound typically
yields `Deny`** (no `allow` derived yet). That's fail-closed in spirit
but does mean a malicious rule set could DoS the prover without
benefiting from a partial trace.

**Predicate indexing.** `build_predicate_index` (`eval.rs:222-228`) is
a `HashMap<Symbol, Vec<usize>>` mapping predicate symbols to fact
indices. Used by `find_all_substitutions_indexed` to skip predicates
that don't match any body atom — an O(1) optimisation that significantly
reduces the inner-loop cost. The non-indexed version
`find_all_substitutions` (line 290) is kept for parity with tests.

**Unification.** `unify_atom_with_fact` (`eval.rs:297-339`) — atom vs
fact, returns extended substitution on success. Standard Datalog
unification: predicates must match; arity must match; per term,
`Var` extends substitution (failing if already bound to a different
term), `Const`/`Int` literals must match exactly.

**Predicate name conventions** (sub-module `eval::predicates`, lines
22–56). Eight well-known predicates: `allow`, `deny`, `request_app`,
`request_service`, `request_action`, `request_feature`,
`request_user`, `request_time`. These are the *engine-controlled*
predicates the request injector populates. **Token consumers (`token`,
`bridge`) extend this set with more "engine-controlled" predicates
that the trace verifier must not allow user facts to spoof** —
this is the policy-injection-attack story called out in
`token/src/datalog_verify.rs:111-178`.

**TODOs.** None visible.

### `verify.rs` (`/Users/ember/dev/breadstuffs/trace/src/verify.rs`)

The verifier — the *spec* the ZK circuit replicates.

Two entry points:
- `verify_trace(facts, rules, trace) -> bool` — the core verifier.
- `verify_trace_with_request(facts, rules, trace, expected_request) -> bool` —
  the **safe wrapper** that also checks `trace.request == expected_request`.
  See open issues below.

**Checks performed (in order).** The block comment at `verify.rs:23-44`
enumerates them:

1. **Request authentication** (only in `_with_request` wrapper).
   `trace.request` MUST equal the caller-supplied `expected_request`.
   This is **Issue #9** in the file — without it, a prover can embed
   *any* request in the trace and prove allow against *that* request,
   then claim the result applies to a different request.
2. **Base fact groundness** (`verify.rs:73-78`). Any base fact
   containing `Term::Var` is rejected. Otherwise a forged base fact
   `app(Var(999))` would unify trivially with any rule body.
3. **Trace size bound.** `MAX_TRACE_STEPS = 10_000`
   (`verify.rs:12-13`). Rejects oversize traces (memory DoS).
4. **Base-fact conclusion guard** (`verify.rs:80-88`). Rejects traces
   where `allow(...)` or `deny(...)` appears in *base* facts. Those
   predicates are engine-controlled outputs; if user-supplied facts
   could include them, the policy is trivially bypassable.
5. **Revocation closing** (`verify.rs:90-108`). If a `revocable(T)`
   base fact exists, there must also be a `not_revoked(T)` base fact
   with the same terms. Documented as fail-closed defence-in-depth —
   the *authoritative* revocation check is in the executor, not the
   trace.
6. **Per-step verification.** `verify_step` (`verify.rs:200-265`):
   - Rule ID must reference a real rule.
   - Body indices count must match rule body length.
   - Each referenced fact must exist (index in range).
   - Each body atom must unify with its referenced fact under the
     reconstructed substitution.
   - The claimed substitution must equal the reconstructed
     substitution (with the additional check that the claimed
     substitution does NOT contain extra variables that were never
     bound — `substitutions_consistent`, `verify.rs:270-287`).
   - All `Check`s must pass under the claimed substitution.
   - The derived fact must equal the head atom under the substitution
     and must be ground.
7. **Policy rule ID attribution.** **Issue #7** (`verify.rs:130-147`):
   if conclusion is `Allow { policy_rule_id }`, that rule id must
   *actually* be the one whose step derived the `allow` fact — a
   prover can't claim "rule 7 allowed me" when actually rule 3 did.
8. **Deny completeness.** **Issue #2** (`verify.rs:149-157`). If the
   conclusion is `Allow`, the verifier *re-derives* using **only the
   deny-producing rules** to confirm no deny fact was *omitted* from
   the trace. A malicious prover cannot drop a `BUDGET_DENY` or
   `REVOCATION_DENY` step to silently convert deny to allow.
9. **Conclusion consistency.** `verify_conclusion`
   (`verify.rs:299-332`): deny wins over allow; an allow conclusion
   requires both no deny anywhere AND an allow step matching the
   claimed rule id.

**Key surprise.** The "issue numbers" in the verifier comments (`#2`,
`#3`, `#7`, `#8`, `#9`) refer to a non-public bug tracker / earlier
audit. They're a *contractual record* of what each check defends
against — a deliberate breadcrumb trail for the next auditor. Worth
preserving.

**`has_derivable_deny`** (`verify.rs:168-197`). Re-runs **one round**
of bottom-up derivation, filtered to deny-producing rules only. This
is sound for *single-step* deny rules (NOT_BEFORE_DENY, BUDGET_DENY,
REVOCATION_DENY — all single-body-fact rules in `policy.rs`). For
deny rules that require multi-step chaining (none exist today), this
would be incomplete — a tripwire to remember if `policy.rs` grows.

**TODOs.** None in file. The "issue" numbers are issue *references*,
not open items.

### `policy.rs` (`/Users/ember/dev/breadstuffs/trace/src/policy.rs`) — **the de facto policy language**

This is the file `BACKWATER-CRATES-AUDIT.md` flagged. 1216 LOC, the
largest single file in the crate, **40% of crate LOC** for a single
file.

**Five exported policy constructors.**

| Function | Status | Body |
|---|---|---|
| `secure_policy()` | **PRIMARY** | 3 rules: APP_ACTION_SECURE (40), SERVICE_ACTION_SECURE (41), UNRESTRICTED (3). Hash-based MemberOf action matching. |
| `standard_policy()` | re-exported | secure_policy core PLUS time-bounded variants (10, 11), NOT_BEFORE_DENY (50), and budget/revocation rules (20, 21, 30, 31). 9 rules. |
| `legacy_policy()` | **`#[deprecated]`** | Contains-based (substring) action matching. 7 rules + budget/revocation. |
| `minimal_policy()` | testing | 3 rules: APP_ACTION (1), SERVICE_ACTION (2), UNRESTRICTED (3). Uses `Contains`. |
| `time_bounded_policy()` | reference | Single 5-body-atom rule; doc says "exceeds the ZK circuit's 4-atom limit" — kept as reference semantics, not for production. |

**Named rule IDs** (`policy.rs:11-45`, module `rule_ids`):

```text
APP_ACTION                   = 1     (Contains-based, deprecated)
SERVICE_ACTION               = 2     (Contains-based, deprecated)
UNRESTRICTED                 = 3
APP_ANY_ACTION               = 4     (legacy)
SERVICE_ANY_ACTION           = 5     (legacy)
APP_ACTION_TIME_BOUNDED      = 10
SERVICE_ACTION_TIME_BOUNDED  = 11
BUDGET_OK                    = 20
BUDGET_DENY                  = 21
REVOCATION_OK                = 30
REVOCATION_DENY              = 31
APP_ACTION_SECURE            = 40
SERVICE_ACTION_SECURE        = 41
NOT_BEFORE_DENY              = 50
```

That's the **public policy vocabulary**. Reading-order of the numbers
tells the story:
- `1..5` are the original (Contains-based) rules; `40/41` are their
  secure (MemberOf-based) replacements.
- `10/11` are time-bounded variants — also moved to MemberOf in the
  standard policy (`policy.rs:142-207`).
- `20/21` budget enforcement.
- `30/31` revocation enforcement.
- `50` not-before enforcement.

**Surface for a policy rule.** A pyana policy can express:

- *Allow if* one of these intersected facts holds: an `action_allowed(app, act)`
  + `request_app(app)` + `request_action(act)`; ditto for `svc_action_allowed`;
  or an `unrestricted(1)` + any `request_action(_)`.
- *Optionally bounded by time*: a `valid_until(exp)` + `request_time(t)` with
  the `Check::LessThan(t, exp)` constraint. Rules 10/11.
- *Negative*: `NOT_BEFORE_DENY` derives `deny()` if `valid_after(s) ∧
  request_time(t) ∧ t < s`. `BUDGET_DENY` derives `deny()` if
  `budget_remaining(B, R) ∧ request_cost(C) ∧ C > R`. `REVOCATION_DENY`
  derives `deny()` if `revocable(T) ∧ revoked(T)`.
- Composition is via *derived intermediate facts*: `BUDGET_OK(B)` and
  `not_revoked_ok(T)` are intermediate predicates derivable by rules
  20 and 30; they could be referenced by other rules (but none in
  the in-tree policy do — see open issues).
- Two arithmetic ordering checks (`<`, `>=`); one substring check
  (`Contains`, deprecated); one equality check (`MemberOf`, secure).
  Plus generic `Equal`. No multiplication, no addition, no aggregation.

**Examples** (paraphrased from the rule definitions):

```text
// Rule 40 (APP_ACTION_SECURE):
allow() :- action_allowed($app, $act),
           request_app($app),
           request_action($act),
           MemberOf($act, $act).

// Rule 50 (NOT_BEFORE_DENY):
deny()  :- valid_after($start),
           request_time($t),
           $t < $start.

// Rule 21 (BUDGET_DENY):
deny()  :- budget_remaining($B, $R),
           request_cost($C),
           $C > $R.

// Rule 31 (REVOCATION_DENY):
deny()  :- revocable($T),
           revoked($T).
```

**The "shared budget/revocation" helper** `budget_revocation_rules()`
(`policy.rs:445-536`) is concat'd onto both `standard_policy()` and
`legacy_policy()` so that all production policies share the same
denial-rule core. This is the only point of policy reuse in the file —
otherwise every constructor is a copy-paste of `Rule { id, head, body,
checks }` literals.

**Surprises in this file.**

1. **There is no DSL surface.** Every rule is a `Rule { id, head: Atom {
   ... }, body: vec![Atom { ... }, ...], checks: vec![Check::...] }`
   literal. Adding a new rule requires editing this Rust file. No
   TOML, no JSON, no parser. The "policy language" exists only as a
   *data shape* (`types::Rule`) and a *set of accepted predicate
   names* (which is determined by what `eval.rs::predicates::*` and
   token consumers like `bridge::authorize::committed_facts_to_trace`
   inject).
2. **Two policy worldviews coexist forever.** `legacy_policy()` and
   `standard_policy()` are mutually inconsistent on action encoding
   (`symbol_from_bytes` vs `symbol_from_str`), yet both are exported.
   `bridge::authorize::evaluate_with_revocation_and_budget`
   (`bridge/src/authorize.rs:444-445`) actually **concatenates them**:
   `let mut rules = pyana_trace::policy::legacy_policy();
   rules.extend(pyana_trace::standard_policy());` That's a 17-rule
   policy where rule 1 (Contains-based) coexists with rule 40
   (MemberOf-based) and a *single token presentation* could in
   principle hit either depending on its caveat encoding. The
   designer wanted this audit to call it out — this is the load-bearing
   concern §2 returns to.
3. **`#[deprecated]` only on `legacy_policy`**, not on
   `minimal_policy()` or `time_bounded_policy()` which also use
   `Contains`. They're "for tests" but importable.
4. **No "default" function and no policy-version field on traces.** The
   trace records `policy_rule_id` (which rule fired) but **not** which
   rule set was loaded. A trace generated against `legacy_policy()`
   and a trace generated against `standard_policy()` are structurally
   indistinguishable unless you cross-reference the `rule_id` to your
   knowledge of which constructor produced rule 1 vs rule 40.

**TODOs.** No explicit `TODO` markers; the gap items above are
*structural*, not labelled.

### `tests.rs` (`/Users/ember/dev/breadstuffs/trace/src/tests.rs`)

44 integration tests. Test-mass-to-impl-mass ratio is ~ 1:1. The test
list reads as a contract:

- Positive auth (allow paths) for app, service, unrestricted.
- Negative auth (deny paths) for wrong app, wrong action, missing
  facts, missing rules.
- Multi-step derivation, transitive derivation, fixpoint termination.
- Time-bounded allow vs deny.
- Verifier tamper tests: tampered derived fact, substitution, body
  indices, conclusion-flip both directions, invalid rule id,
  out-of-bounds fact index.
- Standard-policy scope tests (`standard_policy_app_read`,
  `standard_policy_service_scope`, `standard_policy_multiple_apps`,
  `standard_policy_combined_app_and_service`).
- Serialization roundtrip of full trace and individual rules.
- `test_symbol_from_str_long_strings_no_collision` and
  `test_symbol_from_str_deterministic` — the canonical-encoding
  contract.
- Legacy / secure time-bounded both directions.

The tampering tests are the meat: they directly assert that the
verifier rejects each class of adversarial mutation listed in
verify.rs's "Issue" comments.

**Gaps.** No test for the `verify_trace_with_request` request-mismatch
case (Issue #9). The narrative is in `verify.rs` but no test in
`tests.rs` constructs a trace whose embedded request mismatches the
expected. Worth filing.

---

# Synthesis

## §1. What `trace` *is*

`trace` is **two things at once**, both load-bearing for the pyana token
authorization path, neither of which is "observability" in the modern
distributed-tracing sense:

1. **A Datalog AST + evaluator + verifier** (`types.rs`, `eval.rs`,
   `verify.rs`, `check.rs`). The verifier is *the executable
   specification* that the STARK circuit replicates. Quote
   `lib.rs:3-7`:

   > "This crate provides:
   > - Data structures for representing Datalog derivation traces
   > - A bottom-up Datalog evaluator that records proof traces
   > - A standalone trace verifier
   > - Standard policy rules for the pyana authorization model"

   The "trace" word in the crate name refers to *the Datalog
   derivation trace* — the sequence of `DerivationStep`s recording
   how an `allow` or `deny` fact was reached — not to spans, logs, or
   telemetry.

2. **The de facto pyana policy language** (`policy.rs`). Quote the
   `secure_policy()` doc (`policy.rs:47-64`):

   > "Returns the standard pyana authorization policy rule set. This
   > is the secure policy that uses exact hash matching (`MemberOf`)
   > instead of substring matching (`Contains`)."

   The policy is **defined inline** as a `Vec<Rule>` constructed by
   hand-written Rust. There is no external surface; what a token can
   express is exactly what these constructors encode.

The crate is **not** the observability sidecar. `pyana-observability/`
is a completely separate crate (now ~2 kLOC, four src files plus a
binary) that emits Studio-shape `TraceEvent` JSON for the turn
substrate. The two share the word "trace" and **nothing else** —
different audience, different data shape, different consumers, no
import in either direction (`pyana-observability/Cargo.toml` does
NOT depend on `pyana-trace`). See §3.

So `trace` *is*: the seam between (a) the imperative caveat world
(macaroon / biscuit) and (b) the ZK proof world (circuit), expressed
as a typed Datalog program whose execution shape is a sequence of
witness rows the prover can publish and the verifier can independently
re-derive. The 4-atom/3-term shape limits are deliberate: they bound
the proof system's per-row complexity.

## §2. The de facto policy language in `policy.rs`

### Surface

- **Atoms** with up to 3 terms over a 32-byte symbol space, integer
  literals, or variables.
- **Rules** with a head atom + up to 4 body atoms + 0..N checks.
- **Six check kinds**: `LessThan`, `GreaterThan`, `GreaterThanOrEqual`,
  `Equal`, `Contains` (deprecated), `MemberOf`.
- **Two engine-controlled conclusions** (`allow`, `deny`) plus an
  open-ended set of derived facts (`budget_ok`, `not_revoked_ok`,
  etc.) that other rules can chain off.
- **Six request slots** injected by the evaluator from
  `AuthorizationRequest`: `request_app`, `request_service`,
  `request_action`, `request_feature` (one per feature),
  `request_user`, `request_time`.

### What a policy can express

- **Positive authorization**: "if `action_allowed(myapp, read)` is in
  the committed facts and the request is `request_app(myapp) +
  request_action(read)`, allow." Rule shape: a head `allow()` with up
  to 4 body atoms.
- **Time-bounded authorization**: "additionally require
  `request_time < valid_until`." Adds two body atoms + a `LessThan`
  check.
- **Not-before deny**: "if `valid_after(s) ∧ request_time(t) ∧ t < s`,
  derive `deny`." A standalone deny-producing rule.
- **Budget deny**: "if `budget_remaining(B, R) ∧ request_cost(C) ∧
  C > R`, derive `deny`."
- **Revocation deny**: "if `revocable(T) ∧ revoked(T)`, derive
  `deny`." Note the **prover-controlled gap**: the prover can omit
  `revoked(T)` from base facts. The crate compensates with two
  defences: (a) verifier's `revocable → not_revoked` closing check
  (`verify.rs:90-108`), and (b) the executor independently consults
  the authoritative revocation set outside the trace (this part is
  *not* in the trace crate — it's in `token::revocation`).
- **Compound positive conditions** via shared variables across body
  atoms (e.g. `$app` must be the same in `action_allowed($app, $act)`
  and `request_app($app)`).
- **Negation is by absence**, not by `NOT`. The language has no
  literal negation operator. Deny is expressed as a separate rule
  whose head is `deny`, and deny *overrides* allow in conclusion
  resolution.

### What a policy CANNOT express

- **General first-order negation** ("there is no fact F such that
  ..."). No NAF; only "deny if explicit deny fact exists".
- **Arithmetic computation** beyond ordering. No `+`, `-`, `*`. The
  budget rule's "is `R >= C`" works only because remaining/cost are
  pre-committed integers; the policy can't compute *new* integers.
- **Aggregation** (count, sum, max). No `COUNT(*)`.
- **Recursive rules over large depths** safely. The `MAX_EVAL_ROUNDS
  = 1000` bound means recursion past 1000 levels silently truncates
  and falls through to `Deny`.
- **More than 4 body atoms per rule** in production (the
  `time_bounded_policy()` 5-atom example is documented as the *spec*
  shape that "would need to be split" for the circuit).
- **More than 3 terms per atom** — documented as a hard cap.

### Composition with slot caveats

Slot caveats live in `cell::program::StateConstraint` (21 variants per
`PREDICATE-INVENTORY.md §1.1`). They are a *different* policy
vocabulary that fires *after* a turn's effects on cell state. They do
NOT compose with `trace`'s Datalog in either direction:

- Slot caveats reason over `(old_state, new_state, ctx)` of a cell.
  Their inputs are integers / hashes drawn from cell slots and turn
  context.
- Trace rules reason over a *token's* `(committed_facts,
  request_facts, derived_facts)`. Their inputs are caveats lowered to
  the trace fact-shape by `token::factset::caveat_set_to_factset`.

The two converge at the **executor**, which independently consults:
(a) the trace verifier to authorise the action's *capability*, and
(b) the slot-caveat evaluator to authorise the action's *effect on
state*. The two sit on opposite sides of the auth check; the trace
crate does not know slot caveats exist.

### Composition with `WitnessedPredicate`

Per `PREDICATE-INVENTORY.md §3` the proposed unification is
`WitnessedPredicate { kind, commitment, input_ref, proof_witness_index }`.
The 15 witness-attached predicate sites listed at §1.6 **do not
include the Datalog-trace predicate**. The Datalog trace's relationship
to the unification is:

- The **trace itself** is the witness that the bridge presentation
  STARK consumes (`bridge::present::BridgePresentationProof`,
  itself a `WitnessedPredicate { kind: BridgePredicate,
  commitment: federation_issuer_root, ... }` per the inventory).
- But the **Datalog policy** isn't a `WitnessedPredicate` kind — it's
  the *combiner* that the BridgePresentation predicate's STARK
  computes inside. The trace fits the `WitnessedPredicate` inventory
  *one level up* (as the proof body) rather than *as a kind itself*.

So `trace::policy` is a separate predicate-kind that the inventory
**does not name explicitly**. The closest match in
`PREDICATE-INVENTORY.md §1` would be a hypothetical "§1.X. Datalog
policy rules" with site `trace/src/policy.rs`, site count = 14 named
rule IDs, no STARK enforcement *here* (the STARK enforcement is in
`bridge::present` / `circuit::derivation_air`), no witness attachment
*here* (it's the input to the witness-attached
`BridgePresentationProof`). See §6.

### Composition with `pyana-dsl` predicates

`pyana-dsl` (per inventory §1.9 and §1.6) defines a richer
caveat-authoring DSL (`#[pyana_caveat]`) that compiles to AIR rows
with `RequirementKind::{LessEqual, GreaterEqual, Equal, NotEqual,
Membership, BitRange, MerkleAtPosition, Poseidon2Hash}`. That DSL is
**strictly more expressive** than `trace`'s `Check` enum (it has
Merkle inclusion, Poseidon hashes, bit-range proofs).

The relationship is that `pyana-dsl` produces a *witnessed proof
predicate* per caveat (e.g. `BridgePredicateProof` for a single
GTE/LTE/GT/LT/NEQ/InRange comparison), while `trace`'s checks express
the *outer combinator* that the policy uses to stitch caveats into a
yes/no decision. They are not redundant; they are at different layers.

A token caveat that wants to express "user's reputation > 100"
becomes:
1. A `pyana-dsl` predicate inside the caveat, witnessed by a
   `BridgePredicateProof` (private value, public threshold,
   commitment).
2. A `trace`-level fact like `predicate_satisfied(rep_predicate_hash)`
   injected into the committed fact set after the DSL proof verifies
   off-line.
3. A `trace` rule that requires this fact: `allow :- ...,
   predicate_satisfied(rep_predicate_hash), ...`.

This split is implicit in the code; nothing names it as a layering
diagram.

## §3. Composition with `observability/`

`pyana-observability` (`observability/Cargo.toml`, `observability/src/`)
is a **separate, recently upgraded** crate. As of 2026-05-24 it's ~2
kLOC across `lib.rs`, `emitter.rs`, `events.rs`, `schema.rs`, `main.rs`,
not the 378-LOC single-binary form `BACKWATER-CRATES-AUDIT.md`
described (which has been superseded by Lane Observability-Upgrade).

### Surface

`observability/src/lib.rs:1-92` says it emits **typed structured
TraceEvents** to a Studio inspector. The vocabulary is:

- `TraceEvent` with `EventEnvelope { schema_version, seq, timestamp,
  turn_hash, actor, federation_id, cell_id }` and a per-variant
  `payload`.
- Six payload kinds: `AuthorizationPayload`, `BilateralReceiptPayload`,
  `FederationPayload`, `SovereignWitnessPayload`,
  `StateConstraintPayload`, `TurnLifecyclePayload`.
- `JSON` wire shape with `kind` / `envelope` / `payload`.
- Schema versioning + boundary discipline (`SovereignWitnessPayload`
  emits `(cell_id, sequence, has_stark_proof)` only per
  `BOUNDARIES.md` §2.5).

### Relationship to `trace`

**None at the code level.** `pyana-observability/Cargo.toml` does
**not** depend on `pyana-trace`; `pyana-trace/Cargo.toml` does not
depend on `pyana-observability`. The two crates share zero types.

**At the design level**: they are at **opposite ends of the privacy
boundary**. `trace` produces a private artifact (the
`AuthorizationTrace`) that is the prover-side witness for the
*confidentiality-preserving* STARK proof of authorisation. Per
`bridge::present::BridgePresentationProof` doc, the trace field "MUST
NOT be transmitted over the wire" — it is destroyed (or kept local)
when the proof goes to a remote verifier.

`observability` is the *outside-the-fed-boundary* publication of
event metadata. Per `lib.rs:62-79`, it deliberately emits
**non-confidential** event shapes: certificate hashes, public keys,
nonces, slot indices, constraint kinds, presence of a STARK proof —
**never** the slot values, the cleartext caveats, or the trace
contents.

So they cover **disjoint audiences**:
- `trace::AuthorizationTrace` → prover-side internals, ZK-proof
  witness shape.
- `observability::TraceEvent` → operator / monitor surface, sanitised
  event log.

**Should they merge?** No — see §7 for the recommendation.

**Should `trace::policy` move to a different crate?** Possibly — see §7.

### A naming collision the workspace lives with

The word "trace" is used in *three* distinct senses across the
workspace:

1. **`pyana-trace`** = Datalog derivation trace (this crate).
2. **`pyana-observability::TraceEvent`** = Studio-shape event log.
3. **`stark_trace` / `execution_trace` / `witness_trace` / `poseidon2_trace`**
   in `circuit/` = AIR execution-row matrix (the prover's witness
   tableau).

All three are load-bearing; none of them know about the others. New
contributors discover this the hard way.

## §4. Where it appears in the final system

Concrete consumer code pointers, from the dep graph:

### Direct workspace dependents (8 crates)

| Consumer | File | Used for |
|---|---|---|
| `token` | `token/src/datalog_verify.rs:18-21` | **canonical token verification**: token decode → caveat→FactSet → `pyana_trace::Evaluator::evaluate` → Allow/Deny |
| `bridge` | `bridge/src/authorize.rs:12-15, 92, 444-445` | bridges `token::AuthRequest` → `pyana_trace::AuthorizationTrace` for STARK proving; concatenates `legacy_policy() + standard_policy()` |
| `bridge` | `bridge/src/present.rs:30, 178, 1661, 2142` | embeds `AuthorizationTrace` in `BridgePresentationProof`; recomputes the evaluator's fact set for STARK input; computes `revealed_facts_commitment` (Poseidon2 hash of `pyana_trace::Fact`s) for selective disclosure |
| `circuit` | `circuit/Cargo.toml:108` declares the dep but `circuit/src` doesn't `use pyana_trace`. The comment at `circuit/sp1-guest/src/main.rs:353` says the SP1 guest uses a "self-contained evaluator that doesn't need pyana-trace/pyana-commit" — the declared dep is therefore vestigial in current code | dead dep (?) |
| `intent` | `intent/Cargo.toml:22` declares dep but `intent/src` doesn't use it. Probably for future trustless intent paths | dead dep (?) |
| `sdk` | `sdk/src/runtime.rs:572`, `sdk/src/cipherclerk.rs:28, 2001-2258`, `sdk/src/verify.rs:219, 647-660, 854-856` | cclerk emits trace facts, builds revealed-facts commitments, checks `Conclusion::Allow` on auth results |
| `wasm` | `wasm/src/lib.rs:634-635` | wasm binding for the evaluator + standard policy |
| `demo-agent` | `demo-agent/examples/*.rs` | examples showing Datalog auth, token revocation, RBAC, progressive disclosure |
| `tests` (workspace integration tests) | `tests/src/trace_attacks.rs`, `tests/src/fuzz.rs` | adversarial trace tampering, fuzzing the verifier |

### Crates that **do not** depend on `trace` (notable absences)

`node`, `wire`, `federation`, `turn`, `cell`, `captp`, `coord`,
`blocklace`, `net`, `store`, `audit`, `commit`, `secrets`,
`tokenizer`, `macaroon`, `observability`.

That means: the **executor (`turn`), the consensus stack
(`blocklace`/`federation`/`coord`), the cell state machine, the
networking, the persistent storage, and the gossip layer do not
participate in Datalog evaluation directly**. Trace is *upstream of*
the executor — by the time `turn::executor` runs, the trace verifier
has already (or has not) emitted a STARK proof that gets verified by
`turn::ProofVerifier` (impl in `bridge::verifier::StarkProofVerifier`).

The trace's narrative is **token →trace→ bridge →circuit→ STARK
proof →verifier→ executor**. The executor sees an opaque
"ProofVerifier said yes"; the trace was *consumed* before the
executor was ever consulted.

## §5. Privacy / boundary contract (per `BOUNDARIES.md`)

`BOUNDARIES.md` does not have a dedicated section for `pyana-trace`,
but the implied contract follows from the surrounding
credential-presentation boundary (`BOUNDARIES.md §2.11`):

- **Inside (prover-side).** The cclerk / token holder builds the
  `AuthorizationTrace` locally. They see the full derivation tree:
  every `DerivationStep`'s `substitution`, `body_fact_indices`,
  `derived_fact`, plus the entire committed `FactSet` (caveats in
  cleartext as facts) and the request facts. The trace is **not**
  redacted at this layer.
- **Trace-bundle audience (scope-2, per `BOUNDARIES.md §10.4`).**
  Anyone holding the `WitnessBundle` (the trace rows + witness_hash)
  can re-derive the proof and learn the private trace columns. This
  is the same scope-2 the effect-VM trace uses.
- **Proof-receiver (scope-1, public-input audience).** Receives
  `BridgePresentationProof` over the wire. They see only:
  `federation_root`, `final_state_root`, `composition_commitment`,
  optionally `revealed_facts_commitment` (selective disclosure mode).
  **They do NOT see the trace**. `bridge::present::BridgePresentationProof::into_wire_proof`
  (referenced at `present.rs:174-178`) is responsible for stripping
  the trace before transmission. The doc-comment at lines 170-177
  warns this in capitals: "SECURITY: This field MUST NOT be
  transmitted over the wire."
- **Selective disclosure mode.** The prover may reveal a subset of
  facts; the verifier checks a Poseidon2 commitment of the revealed
  facts against `revealed_facts_commitment` (`present.rs:2142-2176`).
  This **does** leak the chosen facts; everything else stays inside.

**Boundary failure modes specific to `trace`:**

1. If `present.rs::into_wire_proof` ever forgets to strip the trace,
   wire-level privacy is broken silently. This is a load-bearing
   sanitisation step *outside* the trace crate.
2. If a consumer calls `verify_trace` directly without
   `verify_trace_with_request` and forgets to manually compare
   `trace.request` to the actual request, the trace-replay-against-
   different-request attack (Issue #9) opens up. The crate's
   primary export should be `verify_trace_with_request` — and the
   plain `verify_trace` should perhaps be `pub(crate)`.
3. The `revocable → not_revoked` closing rule (`verify.rs:90-108`)
   is in-trace defence-in-depth. The *authoritative* revocation check
   lives in `token::revocation::RevocationRegistry`. If the executor
   ever ships without that registry check, the in-trace check is the
   only fallback and (per its own doc comment) is *not sufficient*
   alone — see Issue #2 commentary at `verify.rs:149-157`.

## §6. Open design questions

### Does `trace`'s policy fit the `WitnessedPredicate` inventory?

**No, not as a `WitnessedPredicateKind`**. The WitnessedPredicate
inventory (PREDICATE-INVENTORY.md §1.6) lists 15 witness-attached
predicate sites. The Datalog-policy-rule shape is not among them.
The closest is `bridge::present::BridgePresentationProof`, which the
inventory categorises as a `WitnessedPredicate` whose commitment is
the federation issuer Merkle root and whose **witness includes the
trace**. The trace is *one level inside* the WitnessedPredicate that
the inventory does name.

### Predicate kinds the inventory does **not** capture

The audit task asked to name what's missing. I claim:

1. **"Datalog rule" as a predicate kind.** The inventory has
   `MatchSpec` (intent matching, also "structural Datalog over
   `(action, resource, app_id, ...)`") and the credential
   presentation "Datalog rule" mentioned in `BOUNDARIES.md §2.11`,
   but it does not give a row in the §1 inventory to
   `pyana_trace::Rule`. The omission is consistent with the
   inventory's framing — it inventories *atomic* predicates, not
   *combinators* — but a `Combinator` axis is missing from §2.
   Adding "§1.11. Datalog rule combinators" with sites
   `trace/src/policy.rs`, 14 named rule IDs, replay = re-evaluation,
   would make the picture complete.
2. **Policy version / rule-set selector.** Nothing in the trace
   carries a `policy_set_id` or `policy_set_root`. Two policies with
   overlapping rule numbers (eg. `standard_policy` vs
   `legacy_policy`) emit indistinguishable traces for shared rule
   ids. The inventory's "snapshot DSL-hash" pattern (the
   `dsl_hash` commitment in `TemporalPredicate`) could give the trace
   a `policy_root` field — a Merkle root over the rule set used,
   committed in the trace alongside the request. Without it, a trace
   verifier in 2027 has to remember which rules `rule_id = 1` meant
   in 2026.
3. **Negative requirements ("MUST-NOT predicates").** Today deny is
   expressed as "if a `deny` fact was derived". A policy can't say
   "this token MUST NOT be presented in this context" except by
   constructing a deny rule. That's structurally fine but
   syntactically clunky, and the *trustless* enforcement of
   revocation already lives outside the trace, so the deny-rule path
   is partial. If a `WitnessedPredicate::NonMembership` kind landed
   (it's prefigured by `cell::note_bridge::BridgedNullifierSet`), the
   trace could absorb revocation natively rather than delegating to
   the executor.

### Other open questions

4. **Why two policy worldviews coexist.** `legacy_policy()` and
   `standard_policy()` are concatenated in
   `bridge/src/authorize.rs:444-445`. That's a 17-rule policy where
   `Contains`-based and `MemberOf`-based rules can both fire.
   Either the migration to MemberOf is incomplete or
   `legacy_policy()` should be feature-gated off-by-default. The
   designer's `BACKWATER-CRATES-AUDIT.md` recommendation to "make
   `secure_policy` the default and deprecate `standard_policy`"
   reads inverted to me — `secure_policy` is the *subset*
   (`standard_policy` includes secure + time-bounded + budget +
   revocation + not-before). The right move is to delete
   `legacy_policy()` and possibly delete `standard_policy()`'s
   substring vestiges in favour of a single secure-by-default
   constructor.
5. **The 4-atom limit is not enforced.** `time_bounded_policy()`
   demonstrates a 5-atom rule and a doc comment notes it "exceeds the
   ZK circuit's 4-atom limit". Nothing in `types::Rule` or
   `eval::Evaluator` rejects > 4 body atoms; the limit lives only in
   the circuit. A policy author can write a 7-atom rule that
   evaluates fine in the local evaluator but cannot be proved
   in-circuit. The mismatch is a tripwire.
6. **Substitution as `Vec<(Variable, Term)>`** is O(n) lookups
   per term application. For tiny rules this is irrelevant; the
   designer should know in case the policy language grows.
7. **No fuzz coverage for `verify_trace_with_request`'s request
   mismatch.** Test plan gap.
8. **`MAX_EVAL_ROUNDS = 1000` fall-through is silent.** A
   pathological rule set hits the bound and emits a `Deny` trace
   that's structurally valid (no allow was reached). There's no way
   to distinguish "policy denies" from "policy timed out". A separate
   `Conclusion::Indeterminate` would help.
9. **`circuit` declares `pyana-trace` as a dep but doesn't use it.**
   Either the dep should be removed or there's a planned wire-up
   that hasn't landed. `intent` is the same.

## §7. Recommendations

### Keep, with the following actions

1. **Keep `trace` as its own crate.** Its no-pyana-dependency
   structure makes it a clean reusable component; the temptation to
   fold it into `token` or `bridge` should be resisted because the
   ZK-circuit replicates the verifier and benefits from the verifier
   living somewhere that doesn't import every pyana crate transitively.
2. **Promote `policy.rs` discussion to a dedicated `AUDIT-trace-policy.md`**
   or a `POLICY-LANGUAGE.md` design doc. The 1216-LOC file deserves
   the airtime: every rule ID is part of a public ABI, every check
   shape has soundness implications.
3. **Make `verify_trace_with_request` the only public entry point.**
   Demote `verify_trace` to `pub(crate)` or rename it
   `verify_trace_unauthenticated` so the request-mismatch attack
   surface is harder to introduce by accident.
4. **Delete `legacy_policy()`**. It's `#[deprecated]`, it carries the
   substring vulnerability the `secure_policy` family was built to
   close, and `bridge::authorize::evaluate_with_revocation_and_budget`
   already concatenates it with `standard_policy()` rather than
   choosing — that concatenation is doing harm. Either keep one
   semantics (MemberOf-only) or carve a feature flag.
5. **Add a `policy_root` (or `policy_set_id`) to `AuthorizationTrace`.**
   Today a `policy_rule_id` is unambiguous only if both sides agree
   on which constructor was used. A 32-byte Merkle root over the rule
   set (computed once at policy-load time) committed alongside the
   request closes the long-term-ABI gap and matches the inventory's
   "snapshot DSL-hash" pattern.
6. **File the §6 gaps in `PREDICATE-INVENTORY.md`.** Specifically:
   add a `§1.11. Datalog policy rules` row pointing to
   `trace/src/policy.rs` with the 14 rule IDs; note in §3.6 that
   Datalog rules are *combinators*, not predicates, so they don't
   collapse into `WitnessedPredicate` but they *do* form the body
   of the witnessed `BridgePresentationProof`.
7. **Test the request-mismatch case.** Add a test to `tests.rs` that
   builds a valid trace for request A and confirms
   `verify_trace_with_request(.., .., trace, request_B) == false`.
8. **Remove the vestigial dep from `circuit/Cargo.toml` and
   `intent/Cargo.toml`** *or* finish the wire-up. The audit'd
   reverse-dep graph says these are dead today.

### Do NOT merge with `observability/`

The two crates' audiences are disjoint:
- `pyana-trace`'s artefact is the *prover's private witness shape*.
  It can never go out the door.
- `pyana-observability`'s artefact is the *operator's sanitised event
  log*. It must go out the door.

A merge would require both crates to grow careful per-field
visibility wrappers; today the type-level separation does that work
for free. Keep them apart. Update the BACKWATER audit's stale view of
`observability/` (it has grown well past 378 LOC) to reflect the
upgraded shape.

### Do NOT move `policy.rs` to a different crate (yet)

There is a temptation to spin `policy.rs` into a separate
`pyana-policy` crate so the verifier (which the ZK circuit
replicates) can live without it. **Resist for now.** Three reasons:

1. The policy is small (14 rule IDs) and unlikely to be authored
   externally. A separate crate would add workspace overhead without
   reducing complexity at the call sites.
2. The verifier's correctness checks are tied to the predicate
   vocabulary (`allow`, `deny`, `revocable`, `not_revoked`). Splitting
   policy out would force `verify.rs` to import policy or duplicate
   the predicate names.
3. The right time to split is when a **policy DSL** (TOML / JSON /
   pyana-dsl-style proc macro) lands. Then `pyana-policy` becomes
   the *parser + compiler* crate and `pyana-trace` stays the AST +
   evaluator + verifier crate. Until then, keep them together.

### Long-term: invest in a policy authoring DSL

The biggest gap is that **the only way to add a pyana policy rule
today is to edit `trace/src/policy.rs`**. If apps want their own
rules, they have to construct `Rule { id, head, body, checks }`
literals in Rust. A small DSL — even just a `[[rule]]` TOML schema
with named predicates — would:

- Decouple policy authoring from crate releases.
- Make policy diff/review-able outside Rust.
- Enable per-app policy registration (federations with custom rules).
- Let `pyana-dsl`'s `RequirementKind` lower naturally into
  `Check`s once the bridging types are sketched.

This is the natural place where `pyana-trace` and `pyana-dsl` meet:
the DSL describes individual caveats; the policy language combines
them. A future `pyana-policy` crate would own that boundary.

---

## Coda — for the next auditor

The most important sentence to internalise about `trace/`:

> The verifier in `verify.rs` is **the executable specification of
> what the ZK circuit must enforce**. Every `Check` kind, every
> per-step check in `verify_step`, every guard in `verify_trace`
> (request authentication, base-fact groundness, base-fact conclusion
> guard, revocation closing, policy_rule_id attribution, deny
> completeness, conclusion consistency) **must have a matching
> constraint row inside `circuit::derivation_air`** (or the bridge
> presentation AIR, depending on the path).

If `verify.rs` rejects, the circuit must also reject. If the circuit
accepts, `verify.rs` must also accept. Any divergence is a soundness
bug. The 44 tampering tests in `tests.rs` are the verifier-side
fence; the differential coverage between
`pyana-trace::verify_trace(forged) == false` and
`circuit::derivation_air::prove(forged_witness) == fail` is *the* sign
that the two layers are in sync. That differential test is **not in
`tests.rs`** today — it would belong in `tests/src/trace_attacks.rs`
or `protocol-tests/`.

That cross-layer differential is the next-best investment after the
recommendations above.
