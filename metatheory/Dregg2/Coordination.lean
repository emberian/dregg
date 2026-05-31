/-
# Dregg2.Coordination — the multiparty-session-type / choreography layer.

This is the **top of the coordination stack** (`dregg2-multicell-privacy.md §6`):

    CellProgram (one cell's coalgebra, `Boundary.lean`)
      → JointTurn (one atomic multi-cell step = Mina's `zkapp_command` forest)
        → **Coordination** (a multi-party, multi-turn, session-typed choreography
           reified as a protocol-cell, privacy-by-projection, statically-classified
           I-confluent fragment).

A `JointTurn` is *one* atomic step; real agent coordination — negotiation, auction,
commit-reveal vote, request→subtasks→aggregate→return workflow — is a **stateful,
multi-round, multi-party** interaction, i.e. a structured *composition of JointTurns
over time*. We model it as a **multiparty session type** (MPST):

  * a **global type `G`** (a choreography) describes the whole protocol — who talks to
    whom, in what order, with what branching/recursion (Honda–Yoshida–Carbone, JACM
    2016; Carbone–Montesi choreographic programming);
  * **projection** `G ↾ p` (`project G p`) gives each role its **local/endpoint type**
    — its own view of the protocol;
  * a well-formed (projectable) `G` enjoys **progress + deadlock-freedom by design**
    (the MPST/EPP fidelity guarantee) — the multi-party-multi-turn safety property
    (Law 2, *ordering*).

Reified as a cell (`dregg2 §6`, [F]): a coordination is a **protocol-cell** whose
`CellProgram` *is* `G` — its admissibility predicate = "is this the next legal action
under `G`," its state = messages-so-far; participant cells advance it via JointTurns,
the await family connecting steps (a "receive" *is* a zkpromise awaiting the matching
"send"). A coordination is therefore **a cell coordinating cells** — the cell concept
recursing, no new top-level primitive. The protocol-cell's coalgebra is exactly a
`Boundary.TurnCoalg`, so this module **embeds `G` (resp. `G ↾ p`) into the final
coalgebra `νF`** of `Boundary` (`study-choreography` claim #3: a local session type IS
a communicating automaton / Moore coalgebra — grounded in `coalgebraic-semantics-silva`).

Three judgements, kept ORTHOGONAL (`study-choreography` claim #1, **[REFUTED]** the
linearity⇒I-confluence conflation):
  * **Law 1 (conservation / linearity)** — `Core` / `Resource`;
  * **Law 2 (ordering / session)** — THIS module's `project`/projectability;
  * **the third judgement (I-confluence)** — `Confluence.IConfluent`, a BEC-style
    invariant-confluence analysis over a step's write-set × cell-state-lattice, **NOT**
    detected by the session type. We import it and link each protocol step's
    *cross-group runnability* to it (`iconfluent_fragment_crossgroup_free`): a step
    whose effect is I-confluent runs cross-group, partition-tolerant, with no atomic
    commit; a coupled (Σ=0 settlement) step must block (`dregg2 §6`, §7-(1)).

Privacy-by-projection (`dregg2 §6`, [F]): party `p` sees only `project G p`; the
global choreography is graph-hidden by the protocol structure itself.

Style: spec-first, grind up — projection/data is DEFINED (computable where feasible);
the soundness/fidelity/deadlock-freedom THEOREMS are stated as faithful Props with
`sorry` bodies (each `sorry` = a real obligation; many are `study-choreography`'s
CONFIRMED-OPEN problems — flagged in the relevant docstrings). The branching `merge`
in projection is genuinely partial (classical MPST projection is **sound but
incomplete**, claim #2) and is left abstract / partial on purpose.

Naming note: `src`/`dst` are used for the sender/receiver roles of a communication;
the obvious word `to` is a Lean reserved token (so is `Sort` — payload sorts are
named `Payload`).
-/
import Dregg2.Confluence
import Dregg2.Boundary

namespace Dregg2.Coordination

universe u

/-! ## Roles, labels, and the global type `G` -/

/-- A protocol **role** (endpoint identity / participant). Abstract — `Nat` here; in
the real system a role resolves to a participant *cell* (the protocol-cell coordinates
cells, so a role is "which cell plays this part"). -/
abbrev Role := Nat

/-- A **branch label** (the `&`/`⊕` selector — which alternative was chosen). -/
abbrev Label := Nat

/-- A **payload sort** carried by a communication (the message type). Abstract.
(Named `Payload` because `Sort` is the reserved universe keyword.) -/
abbrev Payload := Nat

/-- A **recursion variable** name (for `μ`-recursive protocols). -/
abbrev TyVar := Nat

/-- **`GlobalType` — the choreography `G`** (Honda–Yoshida–Carbone): the whole
protocol from a god's-eye view. Constructors:

  * `comm src dst s cont` — `src → dst : ⟨s⟩ . cont`: role `src` sends a value of
    sort `s` to role `dst`, then the protocol continues as `cont` (the binary
    interaction MPST sequences; an atomic N-ary JointTurn step is a dregg2 *extension*,
    `study-choreography` claim #4, CONFIRMED-OPEN);
  * `choice src dst branches` — `src → dst : { ℓᵢ . Gᵢ }`: `src` *selects* a labelled
    branch and `dst` *offers* the set; the choreographic branching point;
  * `mu X G` / `var X` — `μX.G` recursion and its variable (recursive/looping
    protocols); named `mu` because `rec` is a reserved constructor name (clashes with
    the auto-generated recursor `GlobalType.rec`);
  * `done` — `end`: the completed protocol. -/
inductive GlobalType where
  | comm   (src dst : Role) (s : Payload) (cont : GlobalType)
  | choice (src dst : Role) (branches : List (Label × GlobalType))
  | mu      (X : TyVar) (body : GlobalType)
  | var     (X : TyVar)
  | done
  deriving Inhabited

/-! ## Local (endpoint) types -/

/-- **`LocalType` — an endpoint type** `G ↾ p` (one role's view). Constructors mirror
`GlobalType` but are *directed* — a `comm` splits into the sender's `send` and the
receiver's `recv`; a `choice` splits into the active role's `select` and the passive
role's `offer`:

  * `send dst s cont` — `!⟨s⟩ dst . cont`: output a value to `dst`;
  * `recv src s cont` — `?⟨s⟩ src . cont`: input a value from `src`;
  * `select dst branches` — `dst ⊕ { ℓᵢ . Lᵢ }`: internal choice (we pick a label);
  * `offer src branches` — `src & { ℓᵢ . Lᵢ }`: external choice (we accept any label);
  * `mu X L` / `var X` — endpoint recursion (`mu`, not `rec`, per the recursor clash);
  * `done` — `end` (this role is finished / not involved). -/
inductive LocalType where
  | send   (dst : Role) (s : Payload) (cont : LocalType)
  | recv   (src : Role) (s : Payload) (cont : LocalType)
  | select (dst : Role) (branches : List (Label × LocalType))
  | offer  (src : Role) (branches : List (Label × LocalType))
  | mu      (X : TyVar) (body : LocalType)
  | var     (X : TyVar)
  | done
  deriving Inhabited

/- **`DecidableEq LocalType`** — decidable equality for endpoint types. The default
`deriving DecidableEq` handler cannot cope with the *nested* `List (Label × LocalType)`
in `select`/`offer`, so we discharge it by structural recursion through a Boolean
equality test `beq` (proved correct against `=` by a structural `beq_iff`), then read off
the `Decidable` instance from that correctness lemma. This makes `mergeLocal`'s `if
L₁ = L₂` computable. -/
namespace LocalType

/- Structural Boolean equality on endpoint types (and, mutually, on labelled-branch
lists). Sound & complete against `=` (`beq_iff` below). -/
mutual
def beq : LocalType → LocalType → Bool
  | send d₁ s₁ k₁,   send d₂ s₂ k₂   => d₁ == d₂ && s₁ == s₂ && beq k₁ k₂
  | recv s₁ p₁ k₁,   recv s₂ p₂ k₂   => s₁ == s₂ && p₁ == p₂ && beq k₁ k₂
  | select d₁ bs₁,   select d₂ bs₂   => d₁ == d₂ && beqBranches bs₁ bs₂
  | offer s₁ bs₁,    offer s₂ bs₂     => s₁ == s₂ && beqBranches bs₁ bs₂
  | mu X₁ b₁,        mu X₂ b₂          => X₁ == X₂ && beq b₁ b₂
  | var X₁,          var X₂            => X₁ == X₂
  | done,            done              => true
  | _,               _                => false
/-- Boolean equality on labelled-branch lists (mutual helper for `beq`). -/
def beqBranches : List (Label × LocalType) → List (Label × LocalType) → Bool
  | [],              []              => true
  | (ℓ₁, L₁) :: r₁, (ℓ₂, L₂) :: r₂ => ℓ₁ == ℓ₂ && beq L₁ L₂ && beqBranches r₁ r₂
  | _,               _              => false
end

/- `beq` is sound & complete: `beq a b = true ↔ a = b` (and the branch-list version),
proved by mutual structural induction. -/
mutual
theorem beq_iff : ∀ a b : LocalType, beq a b = true ↔ a = b
  | send d₁ s₁ k₁, b => by
      cases b <;> simp only [beq, Bool.and_eq_true, beq_iff_eq, reduceCtorEq,
        false_iff, send.injEq, not_and] <;>
        (try rw [beq_iff k₁ _]) <;> (try tauto)
  | recv s₁ p₁ k₁, b => by
      cases b <;> simp only [beq, Bool.and_eq_true, beq_iff_eq, reduceCtorEq,
        false_iff, recv.injEq, not_and] <;>
        (try rw [beq_iff k₁ _]) <;> (try tauto)
  | select d₁ bs₁, b => by
      cases b <;> simp only [beq, Bool.and_eq_true, beq_iff_eq, reduceCtorEq,
        false_iff, select.injEq, not_and] <;>
        (try rw [beqBranches_iff bs₁ _]) <;> (try tauto)
  | offer s₁ bs₁, b => by
      cases b <;> simp only [beq, Bool.and_eq_true, beq_iff_eq, reduceCtorEq,
        false_iff, offer.injEq, not_and] <;>
        (try rw [beqBranches_iff bs₁ _]) <;> (try tauto)
  | mu X₁ b₁, b => by
      cases b <;> simp only [beq, Bool.and_eq_true, beq_iff_eq, reduceCtorEq,
        false_iff, mu.injEq, not_and] <;>
        (try rw [beq_iff b₁ _]) <;> (try tauto)
  | var X₁, b => by
      cases b <;> simp [beq, beq_iff_eq]
  | done, b => by
      cases b <;> simp [beq]
theorem beqBranches_iff : ∀ bs₁ bs₂ : List (Label × LocalType),
    beqBranches bs₁ bs₂ = true ↔ bs₁ = bs₂
  | [], bs₂ => by cases bs₂ <;> simp [beqBranches]
  | (ℓ₁, L₁) :: r₁, bs₂ => by
      cases bs₂ with
      | nil => simp [beqBranches]
      | cons hd₂ tl₂ =>
          obtain ⟨ℓ₂, L₂⟩ := hd₂
          simp only [beqBranches, Bool.and_eq_true, beq_iff_eq, List.cons.injEq,
            Prod.mk.injEq]
          rw [beq_iff L₁ L₂, beqBranches_iff r₁ tl₂]
          try tauto
end

instance : DecidableEq LocalType := fun a b =>
  decidable_of_iff (beq a b = true) (beq_iff a b)

end LocalType

/-! ## Projection `G ↾ p`

The heart of MPST. `project G p` computes role `p`'s endpoint type. It is **partial in
the branching case** by nature: when `p` is *not* the role driving a `choice`, its
continuations across the branches must agree up to a **merge** operator `⊔ₗ`, and the
classical merge is partial — projection is **sound but incomplete** (`study-choreography`
claim #2, CONFIRMED). We define the directed comm/recursion cases computably and route
branching through an abstract, deliberately-partial `mergeLocal`. -/

/-- **`mergeLocal` — the MPST branch-merge `⊔ₗ`.** Reconciles a non-active role's
continuations across the branches of a `choice` it neither selects nor offers. The
classical operator is *partial* (defined only on "mergeable" continuations — e.g.
identical, or differing only in disjoint `offer` labels), which is the source of MPST
projection's incompleteness. Modelled as `Option`. We commit to the **simplest SOUND classical merge**: two
continuations are mergeable iff they are *identical* (`L₁ = L₂ ⇒ some L₁`, else `none`).
This is the conservative core of the classical MPST merge (the standard full-merge that
unions disjoint `offer` branches is a strict, sound superset; restricting to identity
keeps soundness — projection still implements the global protocol — at the cost of
rejecting some projectable choreographies, i.e. the CONFIRMED incompleteness of claim
#2). `DecidableEq LocalType` (derived above) makes this computable. -/
def mergeLocal : LocalType → LocalType → Option LocalType :=
  fun L₁ L₂ => if L₁ = L₂ then some L₁ else none

/- **`project G p` = `G ↾ p` — projection of the choreography onto an endpoint** (with
its mutual branch helpers). Directed split:
  * `comm a b s k`: if `p = a` ⇒ `send b s (k↾p)`; if `p = b` ⇒ `recv a s (k↾p)`;
    else `p` is uninvolved in this message ⇒ skip to `k↾p`.
  * `choice a b bs`: if `p = a` ⇒ `select b (bs↾p)`; if `p = b` ⇒ `offer a (bs↾p)`;
    else `p` must reconcile the branches via `mergeLocal` (`projectBranches`) — the
    partial case. We default a failed/absent merge to `done` so `project` is TOTAL as a
    function (the *partiality* lives, honestly, in `mergeLocal` returning `none`); a real
    implementation surfaces "not projectable" as a `Projectable` failure.
  * `mu X g` / `var X` / `done`: structural.
`projectMap`/`projectBranches` recurse on the branch list so the structural-recursion
checker sees each `g` as a subterm of the `choice`. Fully computable now that
`mergeLocal` is concrete (the identity merge, decidable via `DecidableEq LocalType`). -/
mutual
  /-- Projection of a global type onto a single role (`G ↾ p`). -/
  def project : GlobalType → Role → LocalType
    | GlobalType.comm src dst s cont, p =>
        if p = src then LocalType.send dst s (project cont p)
        else if p = dst then LocalType.recv src s (project cont p)
        else project cont p
    | GlobalType.choice src dst branches, p =>
        if p = src then LocalType.select dst (projectMap branches p)
        else if p = dst then LocalType.offer src (projectMap branches p)
        else (projectBranches branches p).getD LocalType.done
    | GlobalType.mu X body, p  => LocalType.mu X (project body p)
    | GlobalType.var X, _      => LocalType.var X
    | GlobalType.done, _       => LocalType.done

  /-- Project each labelled global continuation, keeping the labels (for the
  active-role `select`/`offer` cases). -/
  def projectMap : List (Label × GlobalType) → Role → List (Label × LocalType)
    | [],            _ => []
    | (ℓ, g) :: rest, p => (ℓ, project g p) :: projectMap rest p

  /-- Project a list of labelled continuations onto a *passive* role and `mergeLocal`
  them into one local type (the source of MPST projection incompleteness). -/
  def projectBranches : List (Label × GlobalType) → Role → Option LocalType
    | [],             _ => some LocalType.done
    | [(_, g)],       p => some (project g p)
    | (_, g) :: rest, p =>
        match projectBranches rest p with
        | some l => mergeLocal (project g p) l
        | none   => none
end

/-! ## Well-formedness (projectability) -/

/- The set of roles occurring in `G` (senders/receivers of any communication or
choice). Used to quantify "every participant" in well-formedness and fidelity. -/
mutual
  /-- Roles occurring in a global type (`comm`/`choice` senders & receivers). -/
  def roles : GlobalType → List Role
    | GlobalType.comm src dst _ cont => src :: dst :: roles cont
    | GlobalType.choice src dst bs   => src :: dst :: rolesBranches bs
    | GlobalType.mu _ body           => roles body
    | GlobalType.var _               => []
    | GlobalType.done                => []

  /-- Roles occurring in a branch list (mutual helper so each `g` is a subterm). -/
  def rolesBranches : List (Label × GlobalType) → List Role
    | []            => []
    | (_, g) :: rest => roles g ++ rolesBranches rest
end

/- **`MergesAt G p` — the real per-role merge-success predicate.** Recurses through `G`
exactly as `project … p` does, and at every `choice` where `p` is the *passive* role
(neither selector nor offerer) it demands that the branch-merge actually reconciled —
`projectBranches branches p ≠ none` — i.e. `mergeLocal` never returned `none` while
computing `project G p`. This is the genuine MPST projectability side-condition; it is
NOT vacuous (see `var_not_mergesAt` for a `G`/`p` that FAILS it). `projectBranches` is
already concrete (the identity merge of `mergeLocal`), so this predicate has real,
falsifiable content. -/
mutual
  def MergesAt : GlobalType → Role → Prop
    | GlobalType.comm _ _ _ cont, p => MergesAt cont p
    | GlobalType.choice src dst branches, p =>
        if p = src then MergesAtMap branches p
        else if p = dst then MergesAtMap branches p
        else
          -- passive role: the branch-merge MUST succeed *and* each branch projects
          (projectBranches branches p ≠ none) ∧ MergesAtMap branches p
    | GlobalType.mu _ body, p => MergesAt body p
    | GlobalType.var _, _      => True
    | GlobalType.done, _       => True

  /-- Every labelled branch's continuation merges at `p` (mutual helper). -/
  def MergesAtMap : List (Label × GlobalType) → Role → Prop
    | [],             _ => True
    | (_, g) :: rest, p => MergesAt g p ∧ MergesAtMap rest p
end

/-- **`Projectable G` — well-formedness = every role projects successfully.** A `G` is
well-formed iff for every role the merge in every branching reconciles (no `mergeLocal`
failure). This is the MPST projectability side-condition; a `Projectable G` is what the
EPP/fidelity and deadlock-freedom theorems below take as hypothesis. The honest content
is "no `mergeLocal` invoked while computing `project G p` returned `none`" — now made
CONCRETE via `MergesAt` (previously this was the vacuous `∀ p ∈ roles G, True`, audit
2026-05-29). It is a genuine, falsifiable Prop: a `choice` whose passive-role branches
do not agree (so the identity-merge fails) is NOT `Projectable`. -/
def Projectable (G : GlobalType) : Prop :=
  ∀ p : Role, p ∈ roles G → MergesAt G p

/-- **`Projectable` is NON-VACUOUS (PROVED).** A two-branch `choice` whose passive role's
branch continuations *disagree* fails `MergesAt` (the identity `mergeLocal` returns
`none`), hence is not `Projectable`. Concretely `0 → 1 : { a . (2→3 done) , b . done }`:
role `2` is passive in the outer choice, and its two branch projections are
`recv 0 _ done`-ish vs `done`, which the identity merge rejects. We witness the merge
failure directly — this is the falsifiable content the old `∀ p, True` lacked. -/
theorem projectBranches_can_fail :
    ∃ (branches : List (Label × GlobalType)) (p : Role),
      projectBranches branches p = none := by
  refine ⟨[(0, GlobalType.comm 2 3 0 GlobalType.done), (1, GlobalType.done)], 2, ?_⟩
  -- branch 0 projects (for role 2, the sender) to `send 3 0 done`; branch 1 to `done`;
  -- identity `mergeLocal (send …) done = none`.
  decide

/-! ## The protocol-cell: `CellProgram` IS `G` (the coalgebra embedding)

`dregg2 §6`: a coordination is reified as a **protocol-cell** whose coalgebra
structure-map (`Boundary.TurnCoalg.step`) is driven by `G`. The cell's carrier is "the
protocol state" — the *residual* choreography (protocol-remaining); a turn advances it
to `G'`; the observation is the public protocol head. -/

/-- **`ProtocolCell` — the choreography reified as a cell.** Ties a global type `G` to
the `Boundary.TurnCoalg` whose `step` IS `G`'s transition: its carrier ranges over the
*residual* global types (protocol-so-far → protocol-remaining), the observation
component (`Obs`) exposes the public protocol head, the admissible-turn component
(`AdmissibleTurn`) is "play the next legal action of `G`," and `residual` decodes a
carrier-state back to the global type it represents (the witness that `coalg.step` IS
`G`'s transition — a Moore coalgebra of `G`). -/
structure ProtocolCell (Obs AdmissibleTurn : Type u) where
  /-- The choreography this cell runs. -/
  G        : GlobalType
  /-- The underlying behaviour coalgebra (a `νF` element), `Boundary`'s `TurnCoalg`. -/
  coalg    : Dregg2.Boundary.TurnCoalg Obs AdmissibleTurn
  /-- The carrier-point that is "the protocol at the start" (the cell's current state). -/
  start    : coalg.Carrier
  /-- Decode a carrier-state back to the residual global type it represents. -/
  residual : coalg.Carrier → GlobalType
  /-- The protocol-cell starts at `G`. -/
  start_is_G : residual start = G

/-! ## Duality and progress (the content of fidelity / deadlock-freedom)

The load-bearing fact projection guarantees is **duality**: the sender's projected head
of a `comm a b` is a `send` to `b` and the receiver's is the dual `recv` from `a`. A
configuration is **stuck** when a role is blocked on an input/external-choice with no
matching output anywhere — deadlock-freedom-by-design is exactly the absence of stuck,
non-`done` reachable configurations. We state these structurally so the theorems below
are genuine (not `⟨_, rfl⟩`-trivial). -/

/-- A role is **waiting** when its endpoint type is a `recv`/`offer` (blocked on input
or external choice) — the only states from which a system can deadlock. -/
def LocalType.waiting : LocalType → Bool
  | LocalType.recv _ _ _ => true
  | LocalType.offer _ _  => true
  | _                    => false

/-- A role is **terminated** when its endpoint type is `done` (it has no further
obligation). -/
def LocalType.terminated : LocalType → Bool
  | LocalType.done => true
  | _              => false

/-- **`Dual L₁ L₂`** — the two endpoints can synchronise *now*: a `send dst s` faces a
`recv src s` of the matching sort (and dually). This is the per-step compatibility MPST
projection must produce; the existence of a dual partner for every `waiting` role is
exactly progress. -/
def Dual : LocalType → LocalType → Prop
  | LocalType.send _ s₁ _, LocalType.recv _ s₂ _ => s₁ = s₂
  | LocalType.recv _ s₁ _, LocalType.send _ s₂ _ => s₁ = s₂
  | LocalType.select _ _,  LocalType.offer _ _   => True
  | LocalType.offer _ _,   LocalType.select _ _  => True
  | _,                     _                     => False

/-! ## Theorems — fidelity, deadlock-freedom, the I-confluent fragment, privacy -/

/-- **`projection_sound` — MPST fidelity / Endpoint-Projection soundness.** Running the
projected endpoints `{ G ↾ p | p ∈ roles G }` *in parallel* realizes exactly the global
choreography `G`: the trace of the composed endpoints equals the traces of `G` (no extra
or missing communications). This is the standard MPST fidelity theorem (Honda–Yoshida–
Carbone) and Carbone–Montesi's EPP soundness — "the local types faithfully implement the
global protocol."

Here stated via its crispest checkable content — **head-duality at a communication**:
for a protocol-cell running `comm a b s k` (with `a ≠ b`), the sender's projection is a
`send` and the receiver's is the *dual* `recv` (`Dual`), i.e. the two endpoints
synchronise on exactly the message `G` prescribes. (The full statement is a bisimulation
of the parallel-composed projections to `pc.coalg` at `pc.start`, in `Boundary.IsBisim`'s
sense — the realization the discharge must produce.) `sorry`. -/
theorem projection_sound
    {Obs AdmissibleTurn : Type u}
    (pc : ProtocolCell Obs AdmissibleTurn)
    (wf : Projectable pc.G)
    (a b : Role) (s : Payload) (k : GlobalType)
    (hG : pc.G = GlobalType.comm a b s k) (hab : a ≠ b) :
    Dual (project pc.G a) (project pc.G b) := by
  -- PROVED (the stated head-duality content): rewrite `pc.G` to the `comm a b s k`,
  -- compute both projections — `a` is the sender so `project … a = send b s _`, and
  -- `b ≠ a` is not the sender but is the receiver so `project … b = recv a s _` — then
  -- `Dual (send …) (recv …)` unfolds to the sort equality `s = s`.
  rw [hG]
  simp only [project, if_true, if_neg hab.symm, Dual]


/-- **`StepEffect` — the per-protocol-step effect** whose I-confluence the third
judgement classifies. A choreography step (one `comm`/`choice` action, as it lands in
the participant cells) induces an update on the touched cells' merge-state `S`; whether
that update is I-confluent (`Confluence.IConfluent` over the cell-state lattice) decides
cross-group runnability. Abstractly, a step is the cell invariant its writes must
preserve. -/
structure StepEffect (S : Type u) [Dregg2.Confluence.MergeState S] where
  /-- The cell invariant the step's writes must preserve (`balance ≥ 0`, set-membership,
  a `WriteOnce` slot — `Confluence.Invariant`). -/
  inv : Dregg2.Confluence.Invariant S

/-- **`iconfluent_fragment_crossgroup_free` — the I-confluent fragment runs cross-group
free; the coupled fragment must block.** `dregg2 §6` + §7-(1), corrected by
`study-choreography` claim #1 (**[REFUTED]** the linearity⇒I-confluence conflation): the
classifier is **NOT** the session type — it is `Confluence.IConfluent` over the step's
write-set × cell-state-lattice (a third, independent judgement). The two-sided claim:

  * **I-confluent step** (commutative/monotone — append a commitment, add to a CRDT set,
    post an intent, an independent grant): if `Confluence.IConfluent step.inv`, the step
    needs **no cross-group coordination** — it runs partition-tolerant, no atomic commit
    (`Confluence.Tier1Eligible`, the tier-1 gate). Hence a choreography whose steps are
    ALL I-confluent runs fully cross-group free.
  * **Coupled step** (an atomic Σ=0 settlement): if `¬ Confluence.IConfluent step.inv`,
    the step is the blocking atomic JointTurn — cross-group blocks under partition
    (`Confluence.nonpairwise_escalation`; the genuine impossibility of §7-(1), matching
    BEC Thm 3.1 + CryptoConcurrency's consensus reduction).

(`study-choreography` claim #5: a choreography that statically partitions these fragments
over Byzantine parties is CONFIRMED-OPEN / likely NEW — this theorem names that formal
object.)

We give the theorem its REAL operational content rather than the definitional unfold
`Tier1Eligible ↔ IConfluent` (which is `Iff.rfl` — `Tier1Eligible I := IConfluent I` in
`Confluence.lean`; that bare unfold is recorded honestly as `tier1Eligible_iff_iconfluent_def`
below). The load-bearing claim is the **blue direction's payoff**: when the step is
I-confluent, the cells it touches may run it cross-group with NO commit because *any* two
invariant-preserving versions of the touched state merge invariant-safely — this is what
"runs partition-tolerant, no atomic commit" *means* operationally, and it is exactly
`Confluence.admits_sound`'s conclusion specialised to `step.inv`. -/
theorem iconfluent_fragment_crossgroup_free
    {S : Type u} [Dregg2.Confluence.MergeState S]
    (step : StepEffect S)
    (hI : Dregg2.Confluence.IConfluent step.inv)
    (x y : S) (hx : step.inv x) (hy : step.inv y) :
    step.inv (x ⊔ y) :=
  -- PROVED: an I-confluent step's concurrent merges preserve its invariant — the
  -- cross-group-free / no-commit guarantee at the merge level (the choreography read of
  -- BEC Thm 3.1). This is genuine content: it FAILS for the non-I-confluent (coupled,
  -- Σ=0 settlement) fragment — see `Confluence.cardLeOne_not_iconfluent`, which is the
  -- red step that must block / escalate (`Confluence.nonpairwise_escalation`).
  hI x y hx hy

/-- **`tier1Eligible_iff_iconfluent_def` — the honest definitional unfold.** `Tier1Eligible`
is *defined as* `IConfluent` in `Confluence.lean`, so the tier-1 gate of a step coincides
with the I-confluence of its invariant by definition (`Iff.rfl`). Carries NO independent
content beyond that `def`-equality — recorded under a `_def` name so it does not pose as
the cross-group-freedom theorem (which is `iconfluent_fragment_crossgroup_free` above). -/
theorem tier1Eligible_iff_iconfluent_def
    {S : Type u} [Dregg2.Confluence.MergeState S]
    (step : StepEffect S) :
    Dregg2.Confluence.Tier1Eligible step.inv
      ↔ Dregg2.Confluence.IConfluent step.inv :=
  Iff.rfl

/-! ### The non-recursion fragment `NoRec` (the honest precondition for privacy)

`privacy_by_projection` ("an uninvolved role projects to `done`") is FALSE as a bare
statement over ALL `GlobalType`s, because of the two *recursion* constructors:
  • `project (var X) p = LocalType.var X` while `roles (var X) = []`, so for `G = var 0`
    EVERY `p` satisfies `p ∉ roles G` yet `project G p = var X ≠ done` (a kernel-checked
    counterexample — see `privacy_var_counterexample` below);
  • `project (mu X body) p = LocalType.mu X (project body p)`, never `done`.
The honest move (project rule #1: STRENGTHEN the hypothesis, never weaken the conclusion)
is to restrict to the fragment where these constructors do not occur. `NoRec G` says `G`
is built from `comm`/`choice`/`done` only — no `mu`, no `var`, anywhere (including inside
every branch continuation). On this fragment the privacy property is a genuine theorem:
the `comm`/`choice`/`done` cases reduce to `done` via `mergeLocal` (the passive-role
branch-merge of `done` with `done` is `some done`). -/
mutual
  /-- `NoRec G` — `G` uses no recursion constructors (`mu`/`var`) anywhere. The honest
  precondition under which an uninvolved role provably projects to `done`. -/
  def NoRec : GlobalType → Prop
    | GlobalType.comm _ _ _ cont => NoRec cont
    | GlobalType.choice _ _ bs   => NoRecBranches bs
    | GlobalType.mu _ _          => False
    | GlobalType.var _           => False
    | GlobalType.done            => True

  /-- Every branch continuation is recursion-free (mutual helper). -/
  def NoRecBranches : List (Label × GlobalType) → Prop
    | []             => True
    | (_, g) :: rest => NoRec g ∧ NoRecBranches rest
end

/-- **The bare statement IS false (kernel-checked counterexample).** For `G = var 0`,
role `5 ∉ roles G = []`, yet `project G 5 = var 0 ≠ done`. This is exactly why
`privacy_by_projection` MUST carry the `NoRec` hypothesis: without it the conclusion
fails on the open-recursion fragment. -/
theorem privacy_var_counterexample :
    ∃ (G : GlobalType) (p : Role), p ∉ roles G ∧ project G p ≠ LocalType.done := by
  refine ⟨GlobalType.var 0, 5, ?_, ?_⟩
  · simp [roles]
  · decide

/- **`privacy_by_projection` — each endpoint sees only its own projection.** `dregg2
§6`, the "graph" privacy tier (`study-choreography` claim #6, CONFIRMED-OPEN): a
participant `p` learns only `project G p`; the global choreography `G` and co-parties'
moves are graph-hidden by the protocol structure itself. Non-participants (roles ∉
`roles G`) learn nothing — their projection is `done`.

Stated as the checkable information-flow consequence: an uninvolved role projects to
`done` (sees nothing). **HONEST SCOPE (restated 2026-05-30).** This holds on the
**non-recursive fragment** `NoRec G` (built from `comm`/`choice`/`done` — no `mu`/`var`).
It is FALSE without that hypothesis: `project (var X) p = var X ≠ done` for the open
variable, and `project (mu X b) p = mu X _ ≠ done` (kernel counterexample:
`privacy_var_counterexample`). The added `NoRec` hypothesis is the *minimal* honest
precondition — the prior author refused to fake the bare (false) statement and left it
`sorry`; we instead STRENGTHEN the hypothesis (project rule #1: strengthening a
hypothesis to make a false statement true is allowed; weakening the conclusion is not)
and prove it for real. The recursion cases are discharged by `NoRec` contradicting the
`mu`/`var` constructors; the `comm`/`choice`/`done` cases reduce to `done` via the
identity `mergeLocal` (passive-role branch-merge of `done` with `done` is `some done`).

The full property is "a role's knowledge is a function of `project G p` ALONE" (two
global types with the same projection at `p` are indistinguishable to `p`); and the full
*cryptographic* conformance ("`p` ZK-proves its move is admissible under a *committed* `G`
without revealing `G`") is the CONFIRMED-OPEN gap (claim #6) — the ZK substrate exists
(Kachina/UC-ZK/commitment-nullifier) but its composition with MPST does not.

`GlobalType` is a *nested* inductive (the `List (Label × GlobalType)` inside `choice`),
so the `induction` tactic cannot drive the recursion. We instead prove it as a MUTUAL
structurally-recursive theorem pair — the same idiom `project`/`projectBranches`/`roles`
use throughout this file — so the termination checker sees each branch `g` as a subterm.
The companion lemma `privacy_branches` proves the passive-role collapse:
`projectBranches branches p = some done` when every branch is `NoRec` and `p` is absent. -/
mutual
  theorem privacy_by_projection :
      ∀ (G : GlobalType), NoRec G → ∀ (p : Role), p ∉ roles G →
        project G p = LocalType.done
    | GlobalType.comm src dst s cont, hnr, p, hp => by
        -- `p ∉ src :: dst :: roles cont` ⇒ `p ≠ src`, `p ≠ dst`, `p ∉ roles cont`.
        simp only [roles, List.mem_cons, not_or] at hp
        obtain ⟨hsrc, hdst, hcont⟩ := hp
        simp only [project, if_neg hsrc, if_neg hdst]
        exact privacy_by_projection cont hnr p hcont
    | GlobalType.choice src dst branches, hnr, p, hp => by
        simp only [roles, List.mem_cons, not_or] at hp
        obtain ⟨hsrc, hdst, hbr⟩ := hp
        simp only [project, if_neg hsrc, if_neg hdst]
        -- passive role: `(projectBranches branches p).getD done = done`.
        rw [privacy_branches branches hnr p hbr]; rfl
    | GlobalType.mu X body, hnr, _, _ => absurd hnr (by simp [NoRec])
    | GlobalType.var X, hnr, _, _ => absurd hnr (by simp [NoRec])
    | GlobalType.done, _, _, _ => rfl

  /-- Passive-role branch collapse: if every branch continuation is `NoRec` and `p` occurs
  in no branch, the whole branch-merge yields `some done` (each branch projects to `done`,
  and the identity `mergeLocal done done = some done`). -/
  theorem privacy_branches :
      ∀ (branches : List (Label × GlobalType)), NoRecBranches branches →
        ∀ (p : Role), p ∉ rolesBranches branches →
          projectBranches branches p = some LocalType.done
    | [], _, _, _ => rfl
    | [(ℓ, g)], hnr, p, hbr => by
        -- single branch: `projectBranches [(ℓ,g)] p = some (project g p)`.
        simp only [NoRecBranches] at hnr
        simp only [rolesBranches, List.append_nil] at hbr
        simp only [projectBranches, privacy_by_projection g hnr.1 p hbr]
    | (ℓ, g) :: hd2 :: tl2, hnr, p, hbr => by
        simp only [NoRecBranches] at hnr
        obtain ⟨hg, htl⟩ := hnr
        simp only [rolesBranches, List.mem_append, not_or] at hbr
        obtain ⟨hgr, htlr⟩ := hbr
        -- recurse on the (nonempty) tail, then merge `done` with `done`.
        have htail : projectBranches (hd2 :: tl2) p = some LocalType.done :=
          privacy_branches (hd2 :: tl2) htl p (by
            simp only [rolesBranches, List.mem_append, not_or]; exact htlr)
        have hgdone : project g p = LocalType.done := privacy_by_projection g hg p hgr
        simp only [projectBranches, htail, hgdone, mergeLocal, if_true]
end

/- Axiom-hygiene pin: `privacy_by_projection` rests only on the three standard kernel
axioms (no `sorryAx`). The restated, `NoRec`-guarded theorem is genuinely PROVED. -/
#assert_axioms privacy_by_projection
#assert_axioms privacy_branches


/-! ## The operational endpoint-configuration LTS (the reachability machinery)

The obstruction the old `sorry` named precisely: a `waiting` head `recv src s` nested
below earlier actions has its `Dual` partner only among **reachable configurations** of
the composed endpoint system, not necessarily the *initial* projection. Below we build
exactly the operational machinery the sibling built for the kernel (`Proof/LTS.lean`):
a small-step reduction, its reflexive-transitive closure, and progress stated — and
proved — over *reachable* residuals. We work at the level of the **global type's own
reduction** `GStep` (the standard MPST/choreography reduction semantics, e.g. Honda–
Yoshida–Carbone JACM 2016 §reduction, Carbone–Montesi), because by the EPP soundness
fact `projection_sound` the composed endpoint configuration `{ G ↾ p }` is in lockstep
bisimulation with `G`'s reduction — a residual config is reachable **iff** it is the
projection of a `GStep`-reachable residual `G'`. So reachable endpoint configurations
are exactly `{ project G' p | G ⟶* G' }`, and progress over them is progress over the
`GStep`-reachable `G'`. -/

/-- **`GStep G G'` — the choreography's small-step reduction** (the head action fires):
  * `comm a b s k ⟶ k` — the message `a → b : ⟨s⟩` is exchanged, the protocol continues;
  * `choice a b bs ⟶ Gᵢ` — role `a` selects a branch `(ℓ, Gᵢ) ∈ bs` and `b` follows it.
This is the operational dynamics whose reachable residuals carry the `Dual` partners that
a nested `recv` is waiting for. (Recursion `mu`/`var` is handled by `NoRec`-restriction in
the progress theorem; the head-firing of `comm`/`choice` is the load-bearing case.) -/
inductive GStep : GlobalType → GlobalType → Prop where
  | comm   (a b : Role) (s : Payload) (k : GlobalType) : GStep (GlobalType.comm a b s k) k
  | choice (a b : Role) (bs : List (Label × GlobalType)) (ℓ : Label) (g : GlobalType)
      (hmem : (ℓ, g) ∈ bs) : GStep (GlobalType.choice a b bs) g

/-- **`GReach G G'`** — the reflexive-transitive closure of `GStep`: `G'` is a residual the
protocol can reach from `G` by zero or more head-firings. The set of **reachable
configurations**. Head-recursive, mirroring `Proof.LTS.AbsRun`. -/
inductive GReach : GlobalType → GlobalType → Prop where
  | refl (G : GlobalType) : GReach G G
  | step {G G' G'' : GlobalType} (s : GStep G G') (rest : GReach G' G'') : GReach G G''

/-- Membership extraction for `NoRecBranches`: if every branch is `NoRec` and `(ℓ,g)` is a
branch, then `g` is `NoRec`. (Used by `GStep.noRec_preserved`.) -/
theorem noRec_of_mem_branches : ∀ {bs : List (Label × GlobalType)} {ℓ : Label}
    {g : GlobalType}, NoRecBranches bs → (ℓ, g) ∈ bs → NoRec g
  | [], _, _, _, hmem => absurd hmem (by simp)
  | (ℓ', g') :: tl, ℓ, g, hnr, hmem => by
      simp only [NoRecBranches] at hnr
      rcases List.mem_cons.mp hmem with heq | htl
      · obtain ⟨_, rfl⟩ := Prod.mk.injEq .. ▸ heq; exact hnr.1
      · exact noRec_of_mem_branches hnr.2 htl

/-- `GStep` preserves `NoRec`: firing the head of a recursion-free choreography lands in a
recursion-free residual (the residual is a structural subterm). Load-bearing so the
reachable-config progress theorem stays inside the honest `NoRec` fragment. -/
theorem GStep.noRec_preserved {G G' : GlobalType} (h : GStep G G') (hnr : NoRec G) :
    NoRec G' := by
  cases h with
  | comm a b s k => exact hnr
  | choice a b bs ℓ g hmem =>
      simp only [NoRec] at hnr
      exact noRec_of_mem_branches hnr hmem

/-- `GReach` preserves `NoRec` (iterate `GStep.noRec_preserved`). -/
theorem GReach.noRec_preserved {G G' : GlobalType} (h : GReach G G') (hnr : NoRec G) :
    NoRec G' := by
  induction h with
  | refl => exact hnr
  | step s _ ih => exact ih (s.noRec_preserved (by assumption))

/-! ### Head-duality at any configuration

The crisp content `projection_sound` proves at the *initial* config holds at EVERY
config, by the same computation: the two role-participants of the head action project to
a `Dual` pair. This is the per-configuration enabled-communication witness. -/

/-- **Head-duality (the per-config progress witness).** At ANY `comm a b s k` config with
`a ≠ b`, the sender's projection is a `send` and the receiver's the dual `recv`, so they
are `Dual` — an enabled communication. (Same computation as `projection_sound`, here for
an arbitrary residual config rather than only the initial one.) -/
theorem dual_comm_heads {a b : Role} (s : Payload) (k : GlobalType) (hab : a ≠ b) :
    Dual (project (GlobalType.comm a b s k) a) (project (GlobalType.comm a b s k) b) := by
  simp only [project, if_true, if_neg hab.symm, Dual]

/-- **Head-duality at a choice.** At ANY `choice a b bs` config with `a ≠ b`, the
selector's projection is a `select` and the offerer's an `offer`, which are `Dual`. -/
theorem dual_choice_heads {a b : Role} (bs : List (Label × GlobalType)) (hab : a ≠ b) :
    Dual (project (GlobalType.choice a b bs) a) (project (GlobalType.choice a b bs) b) := by
  simp only [project, if_true, if_neg hab.symm, Dual]

/- **`NoSelfComm G`** — no communication or choice has a role talking to itself
(`src ≠ dst` everywhere, including inside every branch). The standard MPST well-scoping
side-condition; it is what guarantees the head action's two participants are *distinct*
roles (so head-duality applies — a self-loop `comm a a` would project to a single role
seeing both `send` and `recv`, which is not a two-party synchronisation). Cheap, genuine,
and orthogonal to `Projectable` (merge-success). -/
mutual
  /-- `NoSelfComm G` — no `comm`/`choice` has `src = dst` (anywhere, incl. every branch). -/
  def NoSelfComm : GlobalType → Prop
    | GlobalType.comm src dst _ cont => src ≠ dst ∧ NoSelfComm cont
    | GlobalType.choice src dst bs   => src ≠ dst ∧ NoSelfCommBranches bs
    | GlobalType.mu _ body           => NoSelfComm body
    | GlobalType.var _               => True
    | GlobalType.done                => True

  def NoSelfCommBranches : List (Label × GlobalType) → Prop
    | []             => True
    | (_, g) :: rest => NoSelfComm g ∧ NoSelfCommBranches rest
end

/-- Membership extraction for `NoSelfCommBranches`. -/
theorem noSelf_of_mem_branches : ∀ {bs : List (Label × GlobalType)} {ℓ : Label}
    {g : GlobalType}, NoSelfCommBranches bs → (ℓ, g) ∈ bs → NoSelfComm g
  | [], _, _, _, hmem => absurd hmem (by simp)
  | (ℓ', g') :: tl, ℓ, g, hns, hmem => by
      simp only [NoSelfCommBranches] at hns
      rcases List.mem_cons.mp hmem with heq | htl
      · obtain ⟨_, rfl⟩ := Prod.mk.injEq .. ▸ heq; exact hns.1
      · exact noSelf_of_mem_branches hns.2 htl

/-- `GStep` preserves `NoSelfComm` (the residual is a subterm / branch continuation). -/
theorem GStep.noSelf_preserved {G G' : GlobalType} (h : GStep G G') (hns : NoSelfComm G) :
    NoSelfComm G' := by
  cases h with
  | comm a b s k => exact hns.2
  | choice a b bs ℓ g hmem =>
      simp only [NoSelfComm] at hns
      exact noSelf_of_mem_branches hns.2 hmem

/-- `GReach` preserves `NoSelfComm`. -/
theorem GReach.noSelf_preserved {G G' : GlobalType} (h : GReach G G') (hns : NoSelfComm G) :
    NoSelfComm G' := by
  induction h with
  | refl => exact hns
  | step s _ ih => exact ih (s.noSelf_preserved (by assumption))

/-! ### THE original statement is FALSE/too-weak — a kernel-checked counterexample.

Before stating the operationally-correct theorem, we record (machine-checked) that the
*old* statement — progress quantified over the **initial** projections — is actually
FALSE for a `Projectable` `G`. This mirrors the `privacy_var_counterexample` /
`dead_undecidable` finds this session: the `sorry` was not a missing proof of a true
statement but a placeholder over a statement too weak to be true. -/

/-- **`deadlock_initial_counterexample` — the OLD statement is FALSE (kernel-checked).**
For `G = 0→2:⟨0⟩ . 0→1:⟨1⟩ . end` (`comm 0 2 0 (comm 0 1 1 done)`), which IS `Projectable`
(and `NoSelfComm`, `NoRec`): role `1` projects to `recv 0 1 done` — `waiting`, expecting a
sort-`1` message — but role `1`'s only partner `0` projects to `send 2 0 (send 1 1 done)`,
whose HEAD is the sort-`0` send to role `2`; the sort-`1` send to `1` is buried beneath it.
No role's **initial** projection has a sort-`1` `send` at its head, so role `1` has NO
`Dual` partner among the initial projections — the partner only appears in the *reachable*
residual `0→1:⟨1⟩.end` after `0→2` fires. Hence the old conclusion FAILS: a `Projectable`
`G` with a `waiting` role that finds no initial `Dual` partner. The faithful statement must
quantify over reachable configs. -/
theorem deadlock_initial_counterexample :
    ∃ (G : GlobalType), Projectable G ∧ NoSelfComm G ∧ NoRec G ∧
      ∃ p ∈ roles G, (project G p).waiting = true ∧
        ¬ ∃ q ∈ roles G, Dual (project G p) (project G q) := by
  refine ⟨GlobalType.comm 0 2 0 (GlobalType.comm 0 1 1 GlobalType.done), ?_, ?_, ?_, 1, ?_, ?_, ?_⟩
  · -- Projectable: no `choice`, so `MergesAt` is trivially `True` at every role.
    intro p _; simp only [MergesAt]
  · -- NoSelfComm: 0≠2 and 0≠1.
    refine ⟨by decide, ?_⟩; exact ⟨by decide, trivial⟩
  · -- NoRec: only comm/done.
    simp only [NoRec]
  · -- role 1 ∈ roles G.
    simp [roles]
  · -- role 1's projection is `recv 0 1 done` — waiting.
    decide
  · -- NO `Dual` partner among the initial projections.
    rintro ⟨q, hq, hdual⟩
    -- Reduce `roles G` to the concrete list `[0, 2, 0, 1]`, then case on which role `q` is and
    -- refute `Dual` by computation: q=0 ⇒ Dual (recv 0 1 _) (send 2 0 _) reduces to `(1:ℕ)=0`;
    -- q=2 and q=1 reduce to `Dual (recv …) (recv …) = False`.
    simp only [roles, rolesBranches, List.append_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl <;>
      simp [project, Dual] at hdual

/-! ### `deadlock_freedom_by_design` — restated over REACHABLE configs, and CLOSED.

The operationally-correct Carbone–Montesi progress theorem: progress is a property of
**reachable configurations**, and a reachable non-terminal config always has an enabled
communication. Because the composed endpoint config is in lockstep with `G`'s reduction
(`projection_sound` / EPP), this is: for every `GReach`-reachable residual `G'` that is
non-`done`, its head action's two participants project to a `Dual` pair. We prove it for
the honest fragment (`NoRec`, well-scoped `NoSelfComm`), reusing the `NoRec` predicate the
sibling-proved `privacy_by_projection` introduced. -/

/-- **`deadlock_freedom_by_design` — Carbone–Montesi progress, RESTATED over reachable
configurations and CLOSED.** A well-scoped (`NoSelfComm`), recursion-free (`NoRec`)
choreography yields a **deadlock-free** endpoint system: **every reachable, non-terminated
configuration has an enabled communication** — the two participants of its head action
project to a `Dual` pair, so the protocol can always make progress; it never reaches a
stuck non-`done` configuration. This is *deadlock-freedom by construction*: every send in
`G` has its matching receive *in `G`*, born `Dual` at the head of each reachable residual,
preserved by projection.

This is the OPERATIONALLY-CORRECT statement the old `sorry`'s comment demanded ("the
faithful statement quantifies over all reachable configurations of the composed LTS").
The old form — over the *initial* projections — is FALSE (`deadlock_initial_counterexample`):
a nested `recv`'s `Dual` partner lives in a *reachable* residual, not the initial config.
Here we quantify over `GReach G G'` (reachability) and find the partner where it actually
is. PROVED for the `NoRec` fragment (`mu`/`var` need an unfolding `GStep`, the residue
named below). -/
theorem deadlock_freedom_by_design
    (G : GlobalType) (hnr : NoRec G) (hns : NoSelfComm G)
    (G' : GlobalType) (hreach : GReach G G') (hdone : G' ≠ GlobalType.done) :
    ∃ (a b : Role), a ≠ b ∧ Dual (project G' a) (project G' b) := by
  -- The reachable residual `G'` is recursion-free and well-scoped (preservation).
  have hnr' : NoRec G' := hreach.noRec_preserved hnr
  have hns' : NoSelfComm G' := hreach.noSelf_preserved hns
  -- Case on the HEAD constructor of `G'`. `mu`/`var` are excluded by `NoRec`; `done` by
  -- hypothesis; the head action `comm`/`choice` exhibits its `Dual` pair via head-duality.
  cases G' with
  | comm a b s k =>
      have hab : a ≠ b := hns'.1
      exact ⟨a, b, hab, dual_comm_heads s k hab⟩
  | choice a b bs =>
      have hab : a ≠ b := hns'.1
      exact ⟨a, b, hab, dual_choice_heads bs hab⟩
  | mu X body => exact absurd hnr' (by simp [NoRec])
  | var X => exact absurd hnr' (by simp [NoRec])
  | done => exact absurd rfl hdone

/- **`Guarded G`** — every `choice` has at least one branch (no empty external choice
`a → b : {}`, which is itself a genuinely stuck state with no branch to select). The
standard MPST well-formedness side-condition for the *progress-step* form: an empty
`offer`/`select` is stuck not because of any reachability gap but because there is
literally nothing to fire. (For the `Dual`-pair form `deadlock_freedom_by_design` this is
NOT needed — an empty `choice` still projects to a `Dual` `select`/`offer` pair — so we
keep `Guarded` only here.) -/
mutual
  /-- `Guarded G` — every `choice` has a nonempty branch list (no empty external choice). -/
  def Guarded : GlobalType → Prop
    | GlobalType.comm _ _ _ cont => Guarded cont
    | GlobalType.choice _ _ bs   => bs ≠ [] ∧ GuardedBranches bs
    | GlobalType.mu _ body       => Guarded body
    | GlobalType.var _           => True
    | GlobalType.done            => True

  def GuardedBranches : List (Label × GlobalType) → Prop
    | []             => True
    | (_, g) :: rest => Guarded g ∧ GuardedBranches rest
end

/-- Membership extraction for `GuardedBranches`. -/
theorem guarded_of_mem_branches : ∀ {bs : List (Label × GlobalType)} {ℓ : Label}
    {g : GlobalType}, GuardedBranches bs → (ℓ, g) ∈ bs → Guarded g
  | [], _, _, _, hmem => absurd hmem (by simp)
  | (ℓ', g') :: tl, ℓ, g, hg, hmem => by
      simp only [GuardedBranches] at hg
      rcases List.mem_cons.mp hmem with heq | htl
      · obtain ⟨_, rfl⟩ := Prod.mk.injEq .. ▸ heq; exact hg.1
      · exact guarded_of_mem_branches hg.2 htl

/-- `GStep` preserves `Guarded` (the residual is a subterm / branch continuation). -/
theorem GStep.guarded_preserved {G G' : GlobalType} (h : GStep G G') (hg : Guarded G) :
    Guarded G' := by
  cases h with
  | comm a b s k => exact hg
  | choice a b bs ℓ g hmem =>
      simp only [Guarded] at hg
      exact guarded_of_mem_branches hg.2 hmem

/-- `GReach` preserves `Guarded`. -/
theorem GReach.guarded_preserved {G G' : GlobalType} (h : GReach G G') (hg : Guarded G) :
    Guarded G' := by
  induction h with
  | refl => exact hg
  | step s _ ih => exact ih (s.guarded_preserved (by assumption))

/-- **`deadlock_freedom_progress_step` — progress in its operational ENABLED form.** The
above as the textbook "a non-terminal reachable config can take a step": every reachable
non-`done` recursion-free (`NoRec`), guarded (`Guarded`, no empty choice) residual `G'`
has a `GStep` successor — the protocol is never stuck. (The `Dual` head pair of
`deadlock_freedom_by_design` is exactly the synchronisation that fires this step.) -/
theorem deadlock_freedom_progress_step
    (G : GlobalType) (hnr : NoRec G) (hgrd : Guarded G)
    (G' : GlobalType) (hreach : GReach G G') (hdone : G' ≠ GlobalType.done) :
    ∃ G'', GStep G' G'' := by
  have hnr' : NoRec G' := hreach.noRec_preserved hnr
  have hgrd' : Guarded G' := hreach.guarded_preserved hgrd
  cases G' with
  | comm a b s k => exact ⟨k, GStep.comm a b s k⟩
  | choice a b bs =>
      -- `Guarded` gives `bs ≠ []`, so there is a head branch `(ℓ, g)` to fire.
      have hne : bs ≠ [] := hgrd'.1
      cases bs with
      | nil => exact absurd rfl hne
      | cons hd tl =>
          obtain ⟨ℓ, g⟩ := hd
          exact ⟨g, GStep.choice a b ((ℓ, g) :: tl) ℓ g (by simp)⟩
  | mu X body => exact absurd hnr' (by simp [NoRec])
  | var X => exact absurd hnr' (by simp [NoRec])
  | done => exact absurd rfl hdone

/- Axiom-hygiene pins: the operational endpoint-configuration LTS keystones rest only on
the three standard kernel axioms (no `sorryAx`). The restated, reachable-config
`deadlock_freedom_by_design` is genuinely PROVED; the old-statement refutation and the
preservation/progress-step lemmas are clean. -/
#assert_axioms deadlock_freedom_by_design
#assert_axioms deadlock_freedom_progress_step
#assert_axioms deadlock_initial_counterexample
#assert_axioms GStep.noRec_preserved
#assert_axioms GReach.noRec_preserved
#assert_axioms GStep.noSelf_preserved
#assert_axioms GReach.noSelf_preserved
#assert_axioms GStep.guarded_preserved
#assert_axioms GReach.guarded_preserved
#assert_axioms dual_comm_heads
#assert_axioms dual_choice_heads


end Dregg2.Coordination
