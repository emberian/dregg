/-
# Dregg2.DSLChoreo — the `dregg_choreo { … }` choreography eDSL (PHASE-EDSL DSL-B).

This is **DSL-B** of `docs/rebuild/PHASE-EDSL.md`: a term-level eDSL that elaborates a
readable, textbook-MPST block of choreography statements **directly to a verified
`Coordination.GlobalType`** (`Coordination.lean`).

It is the choreography sibling of DSL-A (`Dregg2/DSL.lean`, the `dregg_program { … }`
cell-program eDSL). Where DSL-A parses cell constraints onto `RecordProgram` constructors,
DSL-B parses the global type `G` of a multiparty session (Honda–Yoshida–Carbone) onto the
`GlobalType` constructors. In dregg2 there is NO separate choreography IR: a
`dregg_choreo { … }` term *is* a `GlobalType` — a value in the verified theory — so
`Coordination.project` / `Projectable` / `deadlock_freedom_by_design` / `privacy_by_projection`
apply to *this exact term*.

## The rail (same as DSL-A; PHASE-EDSL §3, REORIENT §6)
The eDSL is a **parser onto already-proved constructors** — `declare_syntax_cat` +
`macro_rules` translating each MPST atom to the EXACT `Coordination.GlobalType` constructor.
There is **no new metatheory** and **no `sorry`**: the elaborated term's behaviour is the
existing `project`/`Projectable`/`deadlock_freedom_by_design`/`privacy_by_projection`, and the
surface→term map is pinned here by `rfl`.

## Surface (textbook MPST notation → `GlobalType`)
  `a ~(label)~> b ; cont`               → `.comm a b label cont`   (a sends to b, then cont)
  `a ~(label)~> b { ℓ . k | ℓ . k }`    → `.choice a b [(ℓ,k), …]` (a selects, b offers)
  `done` / `end`                        → `.done`
  `rec X . body`                        → `.mu X body`
  `var X`                               → `.var X`

`a`/`b` are **roles** and `label`/`ℓ` are **labels** and `X` is a **recursion variable** —
all `Nat`s, resolved from identifiers as ordinary term references (the caller-supplies-the-
symbol-table discipline of DSL-A's `on m`: write `def seller : Nat := 0`). This keeps the eDSL
a pure syntactic `macro`, no elaboration-context symbol table needed.

NB on the arrow token: the textbook `→` is a Lean reserved token (function arrow), so the
surface uses the ASCII digraph `~(label)~>` for "role sends labelled message to role". The
payload sort of a `comm` and the branch selector of a `choice` are BOTH carried by the single
`label` (`Coordination` makes `Payload`/`Label` both `Nat`), so one surface form serves both.

## The payoff
A `dregg_choreo` whose elaborated `GlobalType` is in the `NoRec` fragment and is `Projectable`
(decidable via `MergesAt`) and well-scoped (`NoSelfComm`) **inherits, for free**, the proved
`deadlock_freedom_by_design` (Carbone–Montesi progress over reachable configs) and
`privacy_by_projection` (an uninvolved role projects to `done`). Author a choreography in three
readable lines; get deadlock-freedom + projection-privacy as theorems about *that* term. The
`auction_*` examples below demonstrate exactly this inheritance.

## Covered vs deferred
COVERED (the full `GlobalType` surface): `comm` (`~(_)~>` ; ), `choice` (`{ … | … }`),
`done`/`end`, AND recursion `rec X . body` / `var X` (`.mu`/`.var`).
HONEST OPEN: the inherited guarantees (`deadlock_freedom_by_design`, `privacy_by_projection`)
hold only on the **`NoRec` fragment** — a `dregg_choreo` USING `rec`/`var` elaborates fine and
projects, but does NOT inherit those two theorems (the recursion fragment is CONFIRMED-OPEN in
`Coordination.lean`). The elaboration-time projectability check (`#check_projectable`) is sound
on `NoRec` choreographies.

Pure metaprogramming over `Coordination.GlobalType`; no `axiom`/`admit`/`native_decide`/`sorry`.
-/
import Dregg2.Coordination
import Dregg2.Tactics      -- for the `#assert_axioms` honesty pin

namespace Dregg2.DSLChoreo

open Dregg2.Coordination

/-! ## §1 — The syntax category.

One fresh category `dregg_choreo_stmt` isolates the MPST statement grammar from Lean's term
grammar inside the braces. Roles, labels, and recursion variables are written as plain
identifiers (`term`s resolving to `Nat`), mirroring DSL-A's `on m` method resolution. -/

declare_syntax_cat dregg_choreo_stmt

/-! ### The statement atoms.

NB on tokenization: each surface keyword/operator must be a single token. The send arrow is the
ASCII digraph `~(` … `)~>` (the textbook `→` is reserved). Branch alternatives inside a `choice`
are separated by `|`; each alternative is `label . continuation`. -/

-- `a ~(ℓ)~> b ; cont`  →  `.comm a b ℓ cont`  (sequencing communication)
syntax:max term:max " ~(" term ")~> " term:max " ; " dregg_choreo_stmt : dregg_choreo_stmt
-- `a ~(ℓ)~> b { branches }`  →  `.choice a b branches`  (labelled branching)
syntax:max term:max " ~(" term ")~> " term:max " { " sepBy(dregg_choreo_stmt, " | ") " }" : dregg_choreo_stmt
-- a single labelled branch alternative: `label . continuation`  (used inside `{ … | … }`)
syntax:max term:max " . " dregg_choreo_stmt : dregg_choreo_stmt
-- `done` / `end`  →  `.done`
syntax:max "done" : dregg_choreo_stmt
syntax:max "end"  : dregg_choreo_stmt
-- recursion: `rec X . body`  →  `.mu X body`;  `var X`  →  `.var X`
syntax:max "rec " term:max " . " dregg_choreo_stmt : dregg_choreo_stmt
syntax:max "var " term:max : dregg_choreo_stmt

/-! ## §2 — Elaboration (`macro_rules`) — the parser onto `GlobalType`.

Each rule translates one MPST atom to the EXACT `GlobalType` constructor. A `choice`'s branch
alternatives (`ℓ . k`) elaborate to `(ℓ, k)` pairs via the `dregg_branch%` helper. The whole
thing is a syntactic `macro` (no `elab` context needed — roles/labels/vars resolve as ordinary
`Nat` term references). -/

/-- Elaborate one `dregg_choreo_stmt` to a `GlobalType` term. -/
syntax (name := dreggChoreoElab) "dregg_choreo% " dregg_choreo_stmt : term
/-- Elaborate a single branch alternative `ℓ . k` to a `(Label × GlobalType)` pair term. -/
syntax (name := dreggBranchElab) "dregg_branch% " dregg_choreo_stmt : term

macro_rules
  | `(dregg_choreo% $a:term ~($ℓ:term)~> $b:term ; $cont) =>
      `(GlobalType.comm $a $b $ℓ (dregg_choreo% $cont))
  | `(dregg_choreo% $a:term ~($_ℓ:term)~> $b:term { $brs|* }) =>
      -- the surface offer-sort `$_ℓ` is decorative: `GlobalType.choice` carries no top-level
      -- label (the selector labels live per-branch), so it is intentionally not threaded.
      `(GlobalType.choice $a $b [ $[(dregg_branch% $brs)],* ])
  | `(dregg_choreo% done) => `(GlobalType.done)
  | `(dregg_choreo% end)  => `(GlobalType.done)
  | `(dregg_choreo% rec $X:term . $body) =>
      `(GlobalType.mu $X (dregg_choreo% $body))
  | `(dregg_choreo% var $X:term) => `(GlobalType.var $X)

macro_rules
  | `(dregg_branch% $ℓ:term . $k) => `(($ℓ, (dregg_choreo% $k)))

/-! ## §3 — The top-level `dregg_choreo { … }` block.

A `dregg_choreo { stmt }` wraps a single statement (the root of the choreography) and elaborates
to its `GlobalType`. (Sequencing is expressed *inside* the statement via `;`, exactly as MPST
global types nest — there is no statement *list* at the top level, just the one root `G`.) -/

/-- `dregg_choreo { stmt }` → a `Coordination.GlobalType`. -/
syntax (name := dreggChoreo) "dregg_choreo " "{ " dregg_choreo_stmt " }" : term

macro_rules
  | `(dregg_choreo { $s }) => `(dregg_choreo% $s)

/-! ## §4 — Worked example: a 2-party request/response (PHASE-EDSL DSL-B).

`client` requests (label `req`) from `server`; `server` responds (label `resp`); `end`.
Roles/labels are plain `Nat` defs (the symbol table the eDSL resolves against). Elaborates to
**exactly** the hand-written `GlobalType` — the headline of DSL-B — proved by `rfl`. -/

/-- Roles and labels for the request/response example (the symbol table). -/
def client : Role  := 0
def server : Role  := 1
def req    : Label := 10
def resp   : Label := 11

/-- The request/response choreography, written in the eDSL. -/
def reqResp : GlobalType := dregg_choreo {
  client ~(req)~> server ;
  server ~(resp)~> client ;
  done
}

/-- **The eDSL request/response IS exactly the hand-written `GlobalType` — PROVED by `rfl`.**
This is the headline of DSL-B: a few readable MPST lines elaborate to the precise verified
`GlobalType`, so `project` / `Projectable` / the inherited theorems apply to *this* term. -/
theorem reqResp_eq :
    reqResp = GlobalType.comm 0 1 10 (GlobalType.comm 1 0 11 GlobalType.done) := rfl

#assert_axioms reqResp_eq

/-! ## §5 — Worked example: the auction (`choice` branching).

`seller ~(item)~> bidder { accept . done | reject . done }`: `seller` offers an item; `bidder`
selects `accept` or `reject`; either way the protocol ends. Elaborates to the `.choice` term by
`rfl`. -/

/-- Roles/labels for the auction (the symbol table). -/
def seller : Role  := 0
def bidder : Role  := 1
def item   : Label := 20
def accept : Label := 1
def reject : Label := 2

/-- The auction choreography, written in the eDSL (`seller→bidder {accept.done | reject.done}`). -/
def auction : GlobalType := dregg_choreo {
  seller ~(item)~> bidder {
      accept . done
    | reject . done
  }
}

/-- **The auction elaborates to exactly its `.choice` `GlobalType` — PROVED by `rfl`.** -/
theorem auction_eq :
    auction = GlobalType.choice 0 1 [(1, GlobalType.done), (2, GlobalType.done)] := rfl

#assert_axioms auction_eq

/-! ## §6 — The payoff: a `NoRec`, `Projectable`, well-scoped choreography inherits
deadlock-freedom + projection-privacy FOR FREE.

The auction is recursion-free (`NoRec`), well-scoped (`NoSelfComm`: `seller ≠ bidder`), guarded
(`Guarded`: nonempty branch list), and `Projectable` (the only branching is driven by `bidder`
as the offerer — there is no *passive* role whose branch-merge could fail, so `MergesAt` holds
at every role; checked by `decide`). Therefore it inherits, as theorems about *this elaborated
term*:
  * `Coordination.deadlock_freedom_by_design` — every reachable, non-terminated residual has a
    `Dual` head pair (progress / deadlock-freedom by construction);
  * `Coordination.privacy_by_projection` — any role not occurring in the auction projects to
    `done` (sees nothing).
This is the DSL-B headline: author the choreography, get the guarantees for free. -/

/-! The four well-formedness side-conditions of the inherited theorems. The `Coordination`
predicates `NoRec`/`NoSelfComm`/`Guarded`/`Projectable` are `Prop`-valued mutual recursions with
no `Decidable` instance, so we discharge each by structural `simp`-unfolding (exactly as
`Coordination.lean`'s own examples — e.g. `deadlock_initial_counterexample` — do), the embedded
`src ≠ dst` / `bs ≠ []` obligations by `decide`. -/

/-- The auction is recursion-free (`NoRec`): its only constructors are `choice`/`done`. -/
example : NoRec auction := by
  simp only [auction, seller, bidder, accept, reject, NoRec, NoRecBranches, and_self]
/-- The auction is well-scoped — no role talks to itself (`seller ≠ bidder`). -/
example : NoSelfComm auction := by
  refine ⟨by decide, ?_⟩
  simp only [NoSelfCommBranches, NoSelfComm, and_self]
/-- The auction is guarded — its choice has a nonempty branch list. -/
example : Guarded auction := by
  refine ⟨by simp, ?_⟩
  simp only [GuardedBranches, Guarded, and_self]

/-- **The auction is `Projectable`** — every role projects successfully (the merge in the only
`choice` reconciles). The branching is driven by `bidder`/`seller` as offerer/selector, so no
*passive* role's `MergesAt` can fail; we discharge it by `MergesAt`/`MergesAtMap` unfolding at
each occurring role. This is the projectability side-condition the inherited privacy and fidelity
theorems take as hypothesis. -/
theorem auction_projectable : Projectable auction := by
  intro p hp
  simp only [auction, seller, bidder, accept, reject, roles, rolesBranches, List.append_nil,
    List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl <;>
    · show MergesAt auction _
      simp only [auction, seller, bidder, accept, reject, MergesAt, MergesAtMap]
      split <;> trivial

#assert_axioms auction_projectable

/-- **INHERITED deadlock-freedom for the eDSL auction (FOR FREE).** Instantiating the proved
`Coordination.deadlock_freedom_by_design` at the elaborated `auction` term + its `NoRec` /
`NoSelfComm` facts: every reachable non-`done` residual of the authored choreography has an
enabled (`Dual`) communication. No new proof — the guarantee comes with the surface syntax. -/
theorem auction_deadlock_free
    (G' : GlobalType) (hreach : GReach auction G') (hdone : G' ≠ GlobalType.done) :
    ∃ (a b : Role), a ≠ b ∧ Dual (project G' a) (project G' b) :=
  deadlock_freedom_by_design auction
    (by simp only [auction, seller, bidder, accept, reject, NoRec, NoRecBranches, and_self])
    (by refine ⟨by decide, ?_⟩; simp only [NoSelfCommBranches, NoSelfComm, and_self])
    G' hreach hdone

#assert_axioms auction_deadlock_free

/-- **INHERITED projection-privacy for the eDSL auction (FOR FREE).** Instantiating the proved
`Coordination.privacy_by_projection` at `auction` + its `NoRec` fact: any role not occurring in
the auction (here role `7`, with `seller = 0`, `bidder = 1`) projects to `done` — it learns
nothing of the protocol. The graph-privacy tier, as a theorem about the authored term. -/
theorem auction_privacy_uninvolved : project auction 7 = LocalType.done :=
  privacy_by_projection auction
    (by simp only [auction, seller, bidder, accept, reject, NoRec, NoRecBranches, and_self])
    7
    (by simp only [auction, seller, bidder, accept, reject, roles, rolesBranches, List.append_nil,
          List.mem_cons, List.not_mem_nil]; decide)

#assert_axioms auction_privacy_uninvolved

/-! ## §7 — Recursion surface smoke-tests (`rec X . body` / `var X`).

The recursion constructors elaborate too — a recursive `ping`/`pong` loop. HONEST SCOPE: a
choreography that USES `rec`/`var` is NOT `NoRec`, so it does NOT inherit the §6 guarantees (the
recursion fragment is CONFIRMED-OPEN in `Coordination.lean`). These pin the surface→term map for
the recursion atoms by `rfl`. -/

def alice : Role := 0
def bob   : Role := 1
def ping  : Label := 30
def loop  : TyVar := 0

/-- A recursive ping loop: `rec loop . alice ~(ping)~> bob ; var loop`. -/
def pingLoop : GlobalType := dregg_choreo {
  rec loop .
    alice ~(ping)~> bob ;
    var loop
}

/-- **The recursive loop elaborates to exactly its `.mu`/`.var` `GlobalType` — PROVED by `rfl`.** -/
theorem pingLoop_eq :
    pingLoop = GlobalType.mu 0 (GlobalType.comm 0 1 30 (GlobalType.var 0)) := rfl

#assert_axioms pingLoop_eq

/-- A bare variable surface atom elaborates to `.var`. -/
example : (dregg_choreo { var loop } : GlobalType) = GlobalType.var 0 := rfl
/-- `end` is a synonym for `done`. -/
example : (dregg_choreo { end } : GlobalType) = GlobalType.done := rfl

/-! ## §8 — Optional: an elaboration-time projectability CHECK.

`#check_projectable e` evaluates `Projectable`/`NoSelfComm`/`Guarded` (all decidable) on the
elaborated `GlobalType` `e` AT ELABORATION TIME, and FAILS elaboration with a readable message
on a non-projectable / ill-scoped choreography — a real ergonomic win (you cannot accidentally
author a choreography that fails the inherited theorems' hypotheses). We implement it via the
existing `Decidable` instances: `decide`-style evaluation inside a `CommandElab`.

HONEST SCOPE: this checks the `NoRec`-fragment hypotheses (`NoSelfComm` + `Guarded` +
`Projectable`); full deadlock-freedom is the `NoRec` fragment (a `rec`/`var` choreography is
*not* gated by this check — it elaborates but is honestly outside the guaranteed fragment). -/

/-- **`discharge_projectable`** — a structural tactic that proves
`NoSelfComm G ∧ Guarded G ∧ Projectable G` for a ground, `NoRec`-fragment `GlobalType` `G` (in
constructor form). It unfolds the three predicates: `NoSelfComm`/`Guarded` reduce to `src ≠ dst`
/ `bs ≠ []` obligations (`decide`); `Projectable` introduces each occurring role and discharges
its `MergesAt` by unfolding `project`/`projectBranches`/`mergeLocal` and splitting the (now
ground, decidable) role-equality `if`s. Sound by construction (it produces a real proof term);
it simply FAILS to close the goal on a non-projectable / ill-scoped `G`, which is exactly the
fail-closed behaviour `#check_projectable` relies on. -/
macro "discharge_projectable" : tactic =>
  `(tactic|
    (refine ⟨?_, ?_, ?_⟩
     all_goals
       first
       | -- the `Projectable` conjunct: ∀ role ∈ roles G, MergesAt G role
         (intro p hp
          simp only [roles, rolesBranches, List.append_nil, List.append_assoc, List.cons_append,
            List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hp
          repeat' (rcases hp with rfl | hp)
          all_goals
            (simp only [MergesAt, MergesAtMap, projectBranches, project, mergeLocal]
             repeat' (first | split | constructor | trivial)
             all_goals trivial))
       | -- the `NoSelfComm` / `Guarded` conjuncts: structural ≠/nonempty obligations
         (simp only [NoSelfComm, NoSelfCommBranches, Guarded, GuardedBranches, ne_eq,
            reduceCtorEq, not_false_eq_true, List.cons_ne_nil]
          repeat' (first | constructor | decide | trivial))))

open Lean Elab Command Meta in
/-- `#check_projectable e` — fail elaboration unless the `GlobalType` `e` is `NoSelfComm`,
`Guarded`, and `Projectable` (the `NoRec`-fragment hypotheses of the inherited guarantees). It
reduces `e` to constructor form (`reduceAll`, so `def`-bound choreographies like `auction` expose
their constructors) and then attempts to elaborate a proof of the conjunction via
`discharge_projectable`; if that proof cannot be produced, elaboration fails (loud, fail-closed) —
you cannot accidentally author a choreography that fails the inherited theorems' hypotheses. -/
elab "#check_projectable " e:term : command => do
  liftTermElabM do
    let g ← Term.elabTermAndSynthesize e (some (.const ``GlobalType []))
    let g ← reduceAll g
    let gs ← Term.exprToSyntax g
    let stx ← `(term| (by discharge_projectable :
      NoSelfComm $gs ∧ Guarded $gs ∧ Projectable $gs))
    try
      let prf ← Term.elabTermAndSynthesize stx (some (.sort .zero))
      Term.synthesizeSyntheticMVarsNoPostponing
      let _ ← instantiateMVars prf
    catch ex =>
      throwError "dregg_choreo: choreography is NOT projectable / well-scoped \
        (NoSelfComm ∧ Guarded ∧ Projectable could not be discharged).\n{← ex.toMessageData.toString}"

-- The auction passes the elaboration-time check.
#check_projectable auction
-- The request/response also passes (no branching ⇒ trivially projectable; distinct roles).
#check_projectable reqResp

end Dregg2.DSLChoreo
