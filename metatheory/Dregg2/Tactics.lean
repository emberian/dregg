/-
# Dregg2.Tactics — shared proof automation for the dregg2 metatheory.

Small helpers shared across modules and executable protocols. These close routine
goals (reflexivity, definitional simp, injection cleanup, linear arithmetic) — not a way
to make a real obligation look discharged. If a helper does not close a goal, the goal is
real: prove it properly or leave it as an explicit open obligation with a one-line reason.
(Never `admit`, never a fresh `axiom`, never `native_decide` on a non-decidable prop.)
-/
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.Ring
import Lean

/-! ## Axiom-hygiene tripwire — the faked-green regression guard.

`#assert_axioms` elaborates to an error if the named declaration's axiom set escapes
`{propext, Classical.choice, Quot.sound}` (notably: any faked-green axiom). It can only reject,
never close a goal. Pin it under each proved keystone.

Defined at top level (outside the namespace) so the command token parses in every
importing module without needing `open`.

(Honest note on §8 oracles: `CryptoKernel`/`World`/`Verifiable` obligations enter as
typeclass parameters/hypotheses, NOT `axiom`-keyword declarations, so they do not appear
in `collectAxioms` and do not trip this guard. A genuine `axiom`-keyword oracle, were one
ever added, would need to be allow-listed by name with a comment — by design.) -/

/-- The kernel-clean triple. ONE source of truth for what "axiom-clean" means; every
checker below (`#assert_axioms`, `#assert_clean`, `#assert_all_clean`,
`#assert_namespace_axioms`) consults this list, so the discipline cannot drift per-command. -/
def Dregg2.cleanAxioms : List Lean.Name := [``propext, ``Classical.choice, ``Quot.sound]

open Lean Elab Command in
/-- The shared one-name checker the verbose, terse, and batch commands all call. Runs
`collectAxioms name` and throws on the first axiom outside `Dregg2.cleanAxioms` (notably
a faked-green axiom ⇒ a silent faked-green leak). Pure rejector — never closes a goal. Returns `()` on
clean. Centralizing here means the terse/batch forms are *exactly* as strict as the verbose
one (same allow-list, same error), by construction. -/
def Dregg2.assertNameClean (name : Lean.Name) : Lean.Elab.Command.CommandElabM Unit := do
  let axs ← Lean.collectAxioms name
  let bad := axs.filter (fun a => !Dregg2.cleanAxioms.contains a)
  unless bad.isEmpty do
    throwError "axiom-hygiene FAIL: {name} depends on non-kernel axioms {bad.toList} \
      (a faked-green axiom here means a silent faked-green leak into a 'PROVED' keystone)"

open Lean Elab Command in
/-- `#assert_axioms foo` errors unless every axiom `foo` depends on is one of the three
standard kernel axioms (`propext`, `Classical.choice`, `Quot.sound`). In particular it
FAILS on a faked-green axiom, catching a silent faked-green inheritance at build time. -/
elab "#assert_axioms" id:ident : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  Dregg2.assertNameClean name

open Lean Elab Command in
/-- `#assert_clean foo` — terse synonym for `#assert_axioms foo` (identical strength: same
allow-list, same loud failure on the first non-clean axiom). The short token to pin a single
keystone without the noun-heavy `#assert_axioms`. -/
elab "#assert_clean" id:ident : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  Dregg2.assertNameClean name

open Lean Elab Command in
/-- `#assert_all_clean [a, b, c]` — pin a comma-separated LIST of keystones kernel-clean in
ONE command, replacing N verbose `#assert_axioms` lines. Each name is checked by the same
`Dregg2.assertNameClean` the per-theorem form uses, so it is exactly as strict; the FIRST
non-clean name throws (with its offending axiom). A typo'd name is an `unknownConstant` error
— the list cannot silently drop a pin. An EMPTY list is a hard ERROR, not a pass (see below).
Logs the count pinned. -/
elab "#assert_all_clean" "[" ids:ident,* "]" : command => do
  let idArr := ids.getElems
  -- ⚑ NON-VACUITY FLOOR. `ident,*` happily accepts `[]`, and the loop below then never runs:
  -- the command logs "0 keystones pinned" and SUCCEEDS. A guard that pins nothing always
  -- passes. This is the same floor `#assert_not_depends_on`/`#assert_depends_on` carry
  -- (`:EMPTY forbidden list`, `:EMPTY expected list`) — applied here because a refactor that
  -- empties one of these lists must RED, not go quietly green.
  if idArr.isEmpty then
    throwError "#assert_all_clean: EMPTY keystone list — a guard that pins nothing always \
      passes, so this would certify NOTHING while reading as a pin. Name the theorems this \
      line is meant to hold kernel-clean, or delete the command; do not leave an empty one."
  let mut n : Nat := 0
  for id in idArr do
    let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    Dregg2.assertNameClean name
    n := n + 1
  logInfo m!"#assert_all_clean: {n} keystones pinned kernel-clean"

/-! ## `#assert_compiled` — the COMPILER-TRUSTED pin, for the facts a `#guard` used to hide.

⚑ **THE MEASUREMENT THAT MOTIVATES THIS COMMAND.** `#guard e` is implemented (Lean 4.30,
`Lean/Elab/Tactic/Guard.lean:154-167`) as

    let v ← unsafe evalExpr (checkMeta := false) Bool (mkConst ``Bool) e

— the **unsafe compiled evaluator**, the same engine `native_decide` runs on. So a `#guard` is not
a weaker check than a `native_decide` theorem; it is the SAME check with three things deleted:

  * the **name** — nothing can cite it, so nothing composes on it;
  * the **term** — no declaration enters the environment, so no later proof can use it;
  * the **axiom record** — `collectAxioms` sees nothing, so `#assert_axioms` cannot account for it
    and the compiler-trust is INVISIBLE.

That last one is the wound. A `#guard` does not avoid trusting the compiler; it trusts the compiler
*silently*. `theorem foo : e = true := by native_decide` asserts the identical fact at the identical
cost and makes the trust show up in `#print axioms foo`.

`#assert_compiled foo` is the pin for that class. It passes iff every axiom `foo` rests on is either
kernel-clean (`Dregg2.cleanAxioms`) or a compiled-evaluation oracle **that this command has itself
re-run and watched return `true`**, AND at least one such oracle is present. All three halves are
load-bearing:

  * a `sorry`/faked-green axiom is still a hard ERROR — this is not a laxer `#assert_axioms`, it
    widens the allow-list by exactly one named class and nothing else;
  * **zero oracle axioms is ALSO an error** — if the fact is kernel-clean, it must be pinned with
    the STRONGER `#assert_axioms`, and quietly accepting it here would let a kernel-clean keystone
    get labelled compiler-trusted and lose its real pin. The command therefore has a red path in
    both directions, and cannot be used to launder a proof downward.
  * **an oracle axiom is not taken on its word.** See the next note.

⚑ **WHY A NAME CANNOT BE THE TEST (measured 2026-08-09, this command accepted a forgery).** Until
today `Dregg2.isNativeOracleAxiom` recognised an oracle by NAME PATTERN — "any `Name` with a
`native_decide` or `_native` component". Names are chosen by whoever writes the declaration, so

```lean
axiom Evil._native.forged : (1 : Nat) = 1
theorem rests_on_forged : (1 : Nat) = 1 := Evil._native.forged
#assert_compiled rests_on_forged      -- passed, silently
```

The one command whose job is to make compiler trust VISIBLE certified a hand-written axiom, with no
output at all. `#assert_axioms` would have caught it. Sharpening the pattern does not help: the
generated name is `<decl>._native.native_decide.ax_<i>_<j>` (`Lean.mkAuxDeclName`, `Lean/CoreM.lean`),
and `axiom myThm._native.native_decide.ax_1 : decide (1 = 2) = true` is a legal declaration that a
later `myThm` can then rest on. **Every name test is a test of a string the adversary writes.**

Nor is there provenance to consult. `Lean.Meta.nativeEqTrue` (`Lean/Meta/Native.lean`) adds the axiom
with a plain `addDecl` and registers it in NO environment extension; the only trace is a declaration
range, which a source `axiom` command also gets. **There is nothing in the environment that
distinguishes a generated oracle axiom from a hand-written one.**

So this command stops asking where the axiom came from and asks the only question its own label
makes a claim about: **is what it says true under the evaluator whose trust I am declaring?** For
each non-kernel-clean axiom it requires the type shape `nativeEqTrue` emits — `<closed Bool expr> =
true` — and then RE-RUNS that expression through the same compiled evaluator (`Lean.Meta.evalExpr`,
the engine behind `native_decide` and `#guard`) and requires `true`. A forged axiom either fails the
shape (`(1 : Nat) = 1`) or fails the evaluation (`decide (1 = 2) = true`). Anything else — an
unrunnable claim, a universe-polymorphic one, an axiom missing from the environment — is REFUSED
rather than accepted.

Two consequences worth stating. (1) The check now costs a second compiled evaluation per pinned
oracle; that is the price of the certificate being about the FACT rather than about a spelling.
(2) It also catches DRIFT: an oracle axiom whose claim has since stopped evaluating to `true` — a
later `@[implemented_by]`, a changed dependency — now reds, where before the stale axiom stayed
green forever. Note that an `@[implemented_by]` twin IS inside the trust surface this command
declares, by construction: `native_decide` would have produced the same axiom. That seam is closed
by moving the attribute onto an alias, not here.

Read the label literally: `#assert_compiled foo` says **"`foo` is true by compiled evaluation, and I
am saying so out loud."** It is strictly more honest than the `#guard` it replaces and strictly
weaker than `#assert_axioms`. Never write it under a fact that `decide`/`rfl` closes. -/

/-- The Boolean claim a `native_decide`/`bv_decide` oracle axiom makes, if its type has the shape
that machinery emits. `Lean.Meta.nativeEqTrue` builds the axiom type as
`mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool) e (mkConst ``Bool.true)` for a CLOSED `e : Bool` it has
just watched evaluate to `true`; this returns that `e`.

Returning the CLAIM rather than a yes/no about the name is the whole point: it is what lets the
caller go and re-run `e` for itself. A type that is not of this shape is not a compiled-evaluation
claim at all and there is nothing to re-run — which is a refusal, not a pass. -/
def Dregg2.nativeOracleClaim? (type : Lean.Expr) : Option Lean.Expr :=
  match type.eq? with
  | some (α, lhs, rhs) =>
      if α.isConstOf ``Bool && rhs.isConstOf ``Bool.true then some lhs else none
  | none => none

open Lean Elab Command in
/-- `#assert_compiled foo` — see the section note above. For every axiom `foo` rests on that is not
kernel-clean, this command requires an axiom asserting `<closed Bool expr> = true` whose
expression this command RE-RUNS through the compiled evaluator and watches return `true` (Lean
v4.35 removed `Lean.ofReduceBool`/`Lean.ofReduceNat`, so this per-theorem oracle axiom is the only
form compiled evaluation takes). Anything
else is a hard ERROR. It ALSO errors if `foo` rests on no oracle at all (then `#assert_axioms` is
the correct, stronger pin). A name is never the test — see the `⚑ WHY A NAME CANNOT BE THE TEST`
note above, which records the forgery this command used to accept. -/
elab "#assert_compiled" id:ident : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let axs ← Lean.collectAxioms name
  let env ← getEnv
  let mut candidates : Array (Name × Expr) := #[]
  let mut refusals : Array MessageData := #[]
  for a in axs do
    if Dregg2.cleanAxioms.contains a then continue
    match env.find? a with
    | none =>
      refusals := refusals.push m!"{a} — not present in the environment, so its claim cannot be \
        re-run"
    | some info =>
      match Dregg2.nativeOracleClaim? info.type with
      | none =>
        refusals := refusals.push m!"{a} : {info.type} — NOT a compiled-evaluation claim. A \
          `native_decide`/`bv_decide` oracle has type `<closed Bool expr> = true`; this axiom \
          asserts something else, so there is nothing to re-run and nothing here is checkable \
          by compiled evaluation"
      | some claim =>
        if info.levelParams.isEmpty then
          candidates := candidates.push (a, claim)
        else
          refusals := refusals.push m!"{a} — universe-polymorphic ({info.levelParams}), so its \
            claim is not a single closed Boolean this command can re-run"
  -- ⚑ THE TEST. Not "is it named like an oracle" — "does the evaluator I am declaring trust in
  -- still say what this axiom says". Same engine `native_decide` and `#guard` run on.
  unless candidates.isEmpty do
    let evalRefusals ← liftTermElabM do
      let mut fails : Array MessageData := #[]
      for (a, claim) in candidates do
        let verdict : Option MessageData ←
          try
            let b ← unsafe Lean.Meta.evalExpr Bool (Lean.mkConst ``Bool) claim (checkMeta := false)
            pure <| if b then none else
              some m!"{a} — the compiled evaluator returns `false` for the claim this axiom \
                asserts TRUE:{Lean.indentExpr claim}\nThis axiom is either forged or stale; \
                either way nothing may rest on it"
          catch ex =>
            pure <| some m!"{a} — its claim could not be re-run through the compiled evaluator \
              ({ex.toMessageData}), so the compiled-evaluation label is unsupported"
        if let some f := verdict then fails := fails.push f
      pure fails
    refusals := refusals ++ evalRefusals
  unless refusals.isEmpty do
    throwError "compiled-pin FAIL: {name} rests on {refusals.size} axiom(s) this command REFUSES \
      to certify as compiled evaluation:{Lean.indentD (MessageData.joinSep refusals.toList m!"\n")}\
      \nA compiled-evaluation pin certifies a FACT re-run through the evaluator, never a name."
  if candidates.isEmpty then
    throwError "compiled-pin REFUSED: {name} rests on NO compiled-evaluation oracle — it is \
      kernel-clean, so pin it with the STRONGER `#assert_axioms {name}`. Labelling a \
      kernel-clean fact 'compiled' throws away its real pin"

/-! ## `#assert_not_depends_on` — the SEMANTICS-FREEDOM tripwire (proof-term closure guard).

`#assert_axioms` pins which AXIOMS a proof rests on. It says nothing about which DEFINITIONS a proof
walks through — so a theorem advertised as "syntactic, independent of the denotational tower" can be
re-proved through that tower and stay axiom-clean, hence green. Declaration ORDER makes the
independence true at the moment of writing but does not KEEP it true: a later edit that moves the
theorem, or that cites a denotational lemma proved earlier in some other file, restores the
dependency silently.

`#assert_not_depends_on foo [Bar, baz]` closes that hole. It walks the TRANSITIVE constant closure of
`foo`'s proof term (`ConstantInfo.value?` with `allowOpaque := true` — required for theorems, whose
values are opaque; a walk that omits it sees an EMPTY closure and passes everything) and throws a
build-time ERROR, naming the full dependency PATH, if any forbidden constant is reachable.

Anti-toothless conditions, each a hard ERROR rather than a pass:
  * an EMPTY forbidden list — a guard forbidding nothing;
  * a forbidden ident that does not resolve (`unknownConstant` from `realizeGlobalConst…`);
  * a root that is not in the environment at all (a closure of 0 constants).
A forbidden name MATCHES a reached constant if it is equal to it or a `Name` PREFIX of it, so
generated companions (`Matches.eq_def`, `Matches._eq_2`, `Foo.match_1`) count as hits and cannot
launder the dependency.

**The scanned-count is NOT a blindness detector — MEASURED FALSE, do not reintroduce that claim.**
An earlier revision asserted that a low `scanned` count would catch a lost `allowOpaque := true`.
It does not. Built with `allowOpaque := false` and run against a deliberately SEMANTIC re-proof of
`PredRE.sim_null` (`simpa only [derives] using sim_derives h []`), the walk reported `hit = none`
with `scanned = 36`: the forbidden dependency was MISSED while the count sat far above any
tripwire, because the root's TYPE constants are still walked even when its VALUE is invisible. A
blind walk therefore reports every `#assert_not_depends_on` in the tree CLEAN, vacuously.

Blindness is covered instead by `#assert_depends_on` — the exact DUAL rejector, sharing this same
`findForbiddenPath` walk, so the two go blind together or not at all. Pinning a dependency that
exists ONLY through a proof term (`#assert_depends_on PredRE.sim_derives [PredRE.sim_sound]`) makes
a value-blind walk a BUILD FAILURE rather than a green vacuous pass. Every module that relies on
`#assert_not_depends_on` should carry at least one such positive control. -/

/-- Does forbidden name `f` match reached constant `n`? Equality, or `f` a component-wise `Name`
prefix of `n` — so a proof reaching `Matches.eq_def` is caught by forbidding `Matches`, while
`sim_der` does NOT spuriously match `sim_derives` (different final atoms). -/
def Dregg2.forbiddenMatches (f n : Lean.Name) : Bool := f == n || f.isPrefixOf n

open Lean Elab Command in
/-- Walk the transitive constant closure of `root`'s proof term (and type), returning the first
dependency PATH `root → … → hit` that reaches a forbidden constant, plus the number of constants
visited. `allowOpaque := true` is REQUIRED: theorem values are opaque and a walk without it reports
an empty closure (⇒ vacuous pass). -/
def Dregg2.findForbiddenPath (root : Lean.Name) (forbidden : List Lean.Name) :
    CommandElabM (Option (List Lean.Name) × Nat) := do
  let env ← getEnv
  let mut visited : NameSet := NameSet.empty.insert root
  let mut parent : NameMap Name := {}
  let mut queue : Array Name := #[root]
  let mut head : Nat := 0
  let mut count : Nat := 0
  let rebuild : Name → NameMap Name → List Name := fun hit par => Id.run do
    let mut path := [hit]
    let mut cur := hit
    while cur != root do
      match par.find? cur with
      | some p => path := p :: path; cur := p
      | none => break
    return path
  while head < queue.size do
    let cur := queue[head]!
    head := head + 1
    let some info := env.find? cur | continue
    count := count + 1
    let mut refs : Array Name := info.type.getUsedConstants
    if let some v := info.value? (allowOpaque := true) then
      refs := refs ++ v.getUsedConstants
    for r in refs do
      if visited.contains r then continue
      visited := visited.insert r
      parent := parent.insert r cur
      if forbidden.any (fun f => Dregg2.forbiddenMatches f r) then
        return (some (rebuild r parent), count)
      queue := queue.push r
  return (none, count)

open Lean Elab Command in
/-- `#assert_not_depends_on foo [Bar, baz]` — ERROR (build-time, not a warning) if any of the named
forbidden constants is reachable in the transitive constant closure of `foo`'s proof term; the error
names the full dependency PATH. The tripwire for a theorem whose VALUE is that it is independent of
some other development (e.g. a syntactic proof that must never touch the denotational tower).
An empty forbidden list, an unresolvable forbidden name, or a root absent from the environment are
all ERRORS — a guard that can only pass is not a guard. Logs the constants scanned on success. Pure
rejector; its blindness is covered by the dual `#assert_depends_on`, NOT by the scanned count. -/
elab "#assert_not_depends_on" id:ident "[" bads:ident,* "]" : command => do
  let root ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let badIds := bads.getElems
  if badIds.isEmpty then
    throwError "#assert_not_depends_on {root}: EMPTY forbidden list — a guard that forbids nothing \
      always passes; name the constants this proof must not reach."
  let mut forbidden : List Name := []
  for b in badIds do
    -- A typo/renamed target is an `unknownConstant` error here: the guard cannot silently
    -- degrade into forbidding a name that does not exist.
    let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo b
    forbidden := n :: forbidden
  let (hit?, scanned) ← Dregg2.findForbiddenPath root forbidden
  match hit? with
  | some path =>
    throwError "semantics-freedom FAIL: {root} DEPENDS on forbidden constant {path.getLast!} \
      via {path} — this declaration is claimed independent of that development; a proof route \
      through it silently restores the dependency the claim denies. Re-prove it without that \
      route (or retract the independence claim); do NOT relax the guard."
  | none =>
    if scanned == 0 then
      throwError "#assert_not_depends_on {root}: root not found in the environment (0 constants \
        scanned) — nothing was walked, so this check passes vacuously."
    logInfo m!"#assert_not_depends_on {root}: clean of {forbidden.reverse} \
      ({scanned} constants scanned)"

open Lean Elab Command in
/-- `#assert_depends_on foo [Bar, baz]` — the POSITIVE CONTROL, exact dual of
`#assert_not_depends_on`: ERROR unless EVERY named constant IS reachable in the transitive constant
closure of `foo`'s proof term. Shares `findForbiddenPath`, so both commands see the same walk and go
blind together or not at all.

Its job is to fail LOUDLY when the walk stops seeing proof terms (a lost `allowOpaque := true`, a
stale environment): pin a dependency that exists ONLY through a proof term, and a blind walk cannot
report it clean. A rejector alone cannot detect its own blindness — a count heuristic was tried and
MEASURED FALSE (see the module note above). -/
elab "#assert_depends_on" id:ident "[" goods:ident,* "]" : command => do
  let root ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let goodIds := goods.getElems
  if goodIds.isEmpty then
    throwError "#assert_depends_on {root}: EMPTY expected list — a positive control that expects \
      nothing detects nothing; name the constants this proof MUST reach."
  let mut expected : List Name := []
  for g in goodIds do
    let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo g
    expected := n :: expected
  expected := expected.reverse
  for e in expected do
    let (hit?, scanned) ← Dregg2.findForbiddenPath root [e]
    if hit?.isNone then
      throwError "POSITIVE CONTROL FAIL: {root} does NOT reach {e} ({scanned} constants scanned). \
        Either the dependency was really removed — then re-pin this control on a live one — or the \
        closure walk has gone BLIND (a lost `allowOpaque := true`, a stale environment), in which \
        case every `#assert_not_depends_on` in the tree is now passing VACUOUSLY. Do not delete \
        this control to get green."
  logInfo m!"#assert_depends_on {root}: reaches {expected} (walk is not blind)"

/-! ## `@[gate_projection]` — the gate-EXTRACT marker (NOT an authority guarantee).

A `@[gate_projection]` theorem has the shape `<step> = some _ → <the step def's OWN gate>` and is proved
by `unfold <step>; exact h.1` (a `by_cases` on the gate conjunction, projecting the held conjunct out of
the commit). It RE-LISTS the executor's own `if`-guard: it reds on any gate edit (so it pins the gate's
SHAPE), but in ISOLATION it constrains nothing — proving "the committed step satisfies its own gate" is a
tautology-in-spirit, not an independent authority fact.

The GENUINE authority binding for an effect is the iff/triangle over an INDEPENDENT spec — e.g.
`Circuit.Spec.SupplyCreation.mintA_authorized`, derived through `execMintA_iff_spec` over the
linter-PASS `MintASpec` (`Verify.LoadBearingLint`). A `@[gate_projection]`-tagged lemma is fine as a
LOCAL helper (handler-floor `auth_gated`, fail-closed plumbing); it must NEVER be cited as a top-level
authority GUARANTEE. The tag is a documentation marker (no proof power) so a reader/auditor cannot
mistake a gate-extract for the real binding. -/

/-- The `@[gate_projection]` tag — marks a `<step> = some _ → <own-gate>` gate-EXTRACT (proved
`unfold; exact h.1`). A documentation marker ONLY: it carries no proof power and gates nothing. Its job
is to STOP a gate-extract from reading as an authority guarantee — the genuine binding is the
executor⟺independent-spec iff (see the module note above). -/
initialize gateProjectionAttr : Lean.TagAttribute ←
  Lean.registerTagAttribute `gate_projection
    "marks a gate-EXTRACT (`step = some _ → its own gate`, `unfold; exact h.1`) — NOT an authority \
     guarantee; the genuine binding is the executor⟺independent-spec iff"

/-! ## `@[linter_calibration]` — the DELIBERATE-linter-fixture marker.

A `@[linter_calibration]` declaration is a fixture that exists SOLELY to exercise (calibrate) a
rejector — it is constructed to be the kind of thing a checker MUST reject, so that a checker which
fails to reject it is provably toothless. It is NOT spec debt: it is a negative test masquerading, by
shape, as the thing being tested. Two such fixtures calibrate `Verify.LoadBearingLint`:

  * `Dregg2.Verify.LoadBearingAuditKey.gateCopyBurnSpec` — a "spec" that calls the executor STEP gate
    `recCBurnAsset` directly. It calibrates the linter's BOUNDARY check (#1): the linter MUST FAIL it.
  * `Dregg2.Spec.execGraph` — a graph reconstructed VERBATIM as the executor's `.any confersEdgeTo`
    lookup gate, so it is `isDefEq` to that gate (`execGraph_eq_any := rfl`). It calibrates the
    linter's DEFEQ check (#2): the linter MUST FAIL it. Its GENUINE counterpart — the independent
    authority-connectivity spec the C-c1 legs actually attest against — is `Spec.authConnects`
    (linter-PASS, grounded in `Metatheory.AuthorizedProduction`). `execGraph` survives only as (a) this
    calibration fixture and (b) the executor-side gate-relation that TRANSPORTS onto `authConnects`
    (`execGraph_iff_authConnects` / `execGraph_has_iff_authConnects_has`).

The two together are the linter's INTENDED NEGATIVE-CALIBRATION PAIR: every `#load_bearing_audit*`
sweep is expected to produce exactly these two FAILs, and the calibration is ASSERTED (not left a
silent FAIL count) by `#load_bearing_calibration_expect_fail` in the audit modules. The tag is a
documentation marker only — it carries no proof power and gates nothing; its job is to STOP an auditor
reading a deliberate gate-copy as a real-but-broken authority spec. -/

/-- The `@[linter_calibration]` tag — marks a DELIBERATE checker-calibration fixture (a gate-copy /
boundary-violator built to be REJECTED, so the rejector is proven non-toothless). A documentation
marker ONLY: no proof power, gates nothing. Its job is to STOP a deliberate gate-copy from reading as
real spec debt — see the module note above. The genuine counterpart of the `execGraph` calibration is
the independent `Spec.authConnects`. -/
initialize linterCalibrationAttr : Lean.TagAttribute ←
  Lean.registerTagAttribute `linter_calibration
    "marks a DELIBERATE linter-calibration fixture (a gate-copy / boundary-violator built to be \
     REJECTED) — NOT spec debt; carries no proof power"

/-! ## `#assert_namespace_axioms` — module-wide axiom-hygiene pinning.

`#assert_namespace_axioms` pins every theorem under a namespace to the three standard
kernel axioms in one line: it walks `getEnv`, finds every theorem under the prefix, runs
`collectAxioms`, and throws if any depends on an axiom outside
`{propext, Classical.choice, Quot.sound}` (notably a faked-green axiom). Pure rejector — it can only
error, never close a goal.

**The `except` list (honesty caveat).** A name in the `except` clause is skipped (and
reported). Use this for keystones that legitimately rest on a §8 oracle or a Law-1
open primitive — each skip must be justified by a comment, preserving the discipline
that a keystone resting on a primitive is not pinned.

(Like `#assert_axioms`, this only sees `axiom`-keyword declarations; §8 oracles that enter
as typeclass parameters / hypotheses do not appear in `collectAxioms`. By design.) -/

/-- `#assert_namespace_axioms NS (except a b …)?` — pin EVERY theorem under namespace `NS` to the
three standard kernel axioms, erroring on the first one that escapes (a faked-green axiom ⇒ a silent
faked-green leak). Names listed in `except` are skipped (they legitimately rest on a §8/Law-1
primitive — justify each with a comment). Logs the count pinned. Pure rejector. -/
syntax (name := assertNamespaceAxioms)
  "#assert_namespace_axioms" ident (" except " ident+)? : command

open Lean Elab Command in
elab_rules : command
  | `(command| #assert_namespace_axioms $ns:ident $[ except $excIds:ident*]?) => do
  let env ← getEnv
  let prefixName := ns.getId
  let allowed : List Name := Dregg2.cleanAxioms
  -- Resolve the `except` names to fully-qualified constants (a typo is an `unknownConstant`
  -- error here, so the allow-out list cannot silently drift — same discipline as a bad pin).
  let exceptIdents : Array Ident := match excIds with
    | some arr => arr
    | none => #[]
  let exceptNames ← exceptIdents.toList.mapM fun id =>
    liftCoreM <| realizeGlobalConstNoOverloadWithInfo id.raw
  let mut checked : Nat := 0
  let mut skipped : Nat := 0
  let mut seenExcept : List Name := []
  -- Walk the whole environment; `env.constants` is an `SMap Name ConstantInfo`.
  for (name, info) in env.constants.toList do
    -- direct or nested members of the namespace (`Dregg2.Spec.Guard.admits_all` etc.)
    unless prefixName.isPrefixOf name && prefixName != name do continue
    -- theorems only — skip defs, inductives, constructors, recursors, axioms themselves
    unless info.isThm do continue
    -- skip compiler-internal names (`_proof_`, `.match_`, equation lemmas, …)
    if name.isInternalDetail then continue
    if exceptNames.contains name then
      skipped := skipped + 1
      seenExcept := name :: seenExcept
      continue
    let axs ← collectAxioms name
    let bad := axs.filter (fun a => !allowed.contains a)
    unless bad.isEmpty do
      throwError "axiom-hygiene FAIL: {name} depends on non-kernel axioms {bad.toList} \
        (a faked-green axiom here means a silent faked-green leak into a 'PROVED' keystone). \
        If this keystone legitimately rests on a §8/Law-1 primitive, add it to the \
        `except` clause with a justifying comment — do NOT weaken the theorem to pass."
    checked := checked + 1
  -- An `except` name that matched nothing in the namespace is dead allow-listing — surface it
  -- (a renamed/retired keystone left in the allow-out list is itself a drift to catch).
  for e in exceptNames do
    unless seenExcept.contains e do
      logWarning m!"#assert_namespace_axioms {prefixName}: `except` name {e} matched no \
        pinned theorem in this namespace (retired/renamed? remove it from the allow-out list)"
  -- ⚑ NON-VACUITY FLOOR. Without this the command logs "0 theorems pinned kernel-clean" and
  -- PASSES whenever the walk found nothing — a renamed namespace, a typo'd prefix, or (the
  -- one that actually happens) a declaring module that is not in this pin site's import
  -- closure, so `env.constants` simply does not contain the theorems. Nothing was walked, so
  -- the check passed vacuously. Same floor as `#assert_not_depends_on`'s zero-scan error.
  if checked == 0 then
    throwError "#assert_namespace_axioms {prefixName}: 0 theorems pinned — NOTHING WAS WALKED, \
      so this check would pass vacuously.{if skipped > 0 then
        m!" ({skipped} theorem(s) matched but every one was allow-listed out via `except`, \
          which pins nothing either.)" else
        m!" No theorem in the environment has `{prefixName}` as a proper name prefix — either \
          the namespace was renamed, or the module that declares it is NOT in this file's \
          import closure (add the import; a pin can only see what is imported)."} \
      Fix the prefix or the import, or delete the pin; do not leave one that certifies nothing."
  logInfo m!"#assert_namespace_axioms {prefixName}: {checked} theorems pinned kernel-clean\
    {if skipped > 0 then m!", {skipped} skipped via `except`" else m!""}"

namespace Dregg2.Tactics

/-- `dregg_auto` — best-effort closer for *routine* obligations only: reflexivity,
`trivial`, definitional/hypothesis `simp`, linear arithmetic, propositional tautology.
Use it as the last step of a proof; if it fails, the goal carries real content. -/
macro "dregg_auto" : tactic =>
  `(tactic| first
    | rfl
    | trivial
    | (intros; first | rfl | trivial | simp_all | omega | tauto)
    | simp_all
    | omega
    | tauto)

/-- `option_inj at h` — collapse `some x = some y` (and any nested `(·,·) = (·,·)`) in `h`
to its component equalities; the standard first move when reading back a protocol step
that returned `some (newState…)`. -/
macro "option_inj" "at" h:ident : tactic =>
  `(tactic| simp only [Option.some.injEq, Prod.mk.injEq] at $h:ident)

/-! ## Effect-arm combinators (per-effect dispatch-proof helpers).

The `cases fa with` dispatch proofs over `FullActionA` repeat a small vocabulary of moves
per arm: reject the `none` (fail-closed) branch, substitute the committed state on `some`,
peel an `if gate then … else none`, discharge a balance-neutral edit. Each combinator below
expands to exactly those tactic steps — no oracle, no `native_decide`, so a wrong arm still
fails loudly. -/

/-- `reject_none h hk` — the FAIL-CLOSED `none` branch. `hk : f = none` rewrites the commit
hypothesis `h : f = some _` to `none = some _`, closed by `absurd`. -/
macro "reject_none" h:ident hk:ident : tactic =>
  `(tactic| (rw [$hk:ident] at $h:ident; exact absurd $h:ident (by simp)))

/-- `commit_subst h hk` — the `some` branch. `hk : f = some k'` rewrites `h`, peels the
`some`-injection, and substitutes the committed state into the goal. -/
macro "commit_subst" h:ident hk:ident : tactic =>
  `(tactic| (rw [$hk:ident] at $h:ident; simp only [Option.some.injEq] at $h:ident; rcases $h:ident with ⟨rfl⟩))

/-- `gate_peel hk with finisher` — peel an `if guard then some _ else none` inside a chained step
`hk : (if … then some _ else none) = some _`. Uses `split` (so the guard need NOT be named): the
`then` branch substitutes the committed kernel and runs `finisher`; the `else` branch is
FAIL-CLOSED against `hk`. -/
macro "gate_peel" hk:ident " with " fin:tactic : tactic =>
  `(tactic|
    (split at $hk:ident
     · simp only [Option.some.injEq] at $hk:ident
       subst $hk:ident
       $fin
     · exact absurd $hk:ident (by simp)))

-- NOTE: the balance-NEUTRAL finisher `bal_neutral` (the fourth combinator) lives in
-- `Dregg2/Exec/RecordKernel.lean`, next to the per-asset measure (`recTotalAsset`)
-- it unfolds — a tactic-macro must reference user globals from a site where they are in
-- scope (macro hygiene resolves the simp-lemma names at the DEFINITION site, not the use
-- site), so a domain-specific finisher belongs with its domain, not in this generic file.

end Dregg2.Tactics
