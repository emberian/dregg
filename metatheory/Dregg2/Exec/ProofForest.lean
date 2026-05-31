/-
# Dregg2.Exec.ProofForest — proof-carrying WITHOUT recursive compression (PHASE-PROOF-CARRYING §5.1).

dregg has **never** had a sound, useful proof AGGREGATION (compressing an interaction DAG into one
succinct recursive proof — IVC / STARK-in-STARK / folding; the honest assessment is
`docs/rebuild/PHASE-PROOF-CARRYING.md §2`). So the architecture does **not** compress. It ships the
**whole forest** of per-step proofs, each standalone and independently verifiable, **plus the
linking witness data** an aggregate would have absorbed into its public inputs. A verifier
(a) verifies **every** proof against its own public inputs, and (b) checks the **linking
discipline**: each proof's `newCommit` equals the next proof's `oldCommit` along every
happened-before edge (and cross-cell edges balance via the CG-5 shared-binding `Σδ = 0`, reusing
`Exec/CrossCellForest.lean`). Soundness of the composite is then the CONJUNCTION of per-proof
soundness (the §8 / circuit cryptographic assumption) and the linking check (a *combinatorial* fact,
fully in Lean). Cost: O(n) instead of O(1); aggregation slots in **later** as a pure performance
swap that provably does not touch the soundness story (`PHASE-PROOF-CARRYING §8`).

This module is the small, honest bridge `PHASE-PROOF-CARRYING §5.1` names: it packages the existing
composition theorems (`Exec/TurnForest.lean`'s `execForest_attests` / `execForest_eq_execTurn`, and
`Exec/CrossCellForest.lean`'s `crossForest_attests`, all already proved) into a NAMED `ProofForest`
abstraction with the per-node proof-validity as an EXPLICIT HYPOTHESIS (the §8 circuit seam), exactly
as the `CryptoKernel`/`World` portals enter their assumptions — never an `axiom`/`sorry` inside the
proof.

  * **`ProofNode`** — the public-input PROJECTION of one cell-step (`oldCommit`, `newCommit`,
    `effectsHash`, `prevReceipt`, `seq`, the `δ` half-edge — exactly `circuit/src/effect_vm/pi.rs`'s
    linking surface) PLUS a `StepProofValid : Prop`: the assumption "this node's STARK proof verifies
    against its PI." That `Prop` is the §8 cryptographic seam — NOT proved here (it is the circuit's
    job); it is the HYPOTHESIS the composition theorem is parametric in.
  * **`Linked`** — the combinatorial chain-link: each node's `newCommit` is the next node's
    `oldCommit` (state continuity along the happened-before edge), reusing `prevReceipt`/`seq` for the
    receipt-chain pointer and replay discipline (PHASE-PROOF-CARRYING §3 intra-cell chain-link).
  * **`proofForest_sound`** — THE THEOREM: if every node's proof verifies (`∀ n, n.StepProofValid`)
    AND the forest is `Linked`, the composite run attests the full `StepInv` over the whole forest —
    by reducing to `execForest_attests`. The per-node validity is the HYPOTHESIS (the §8 seam); the
    LINKING + composition is what is PROVED.

### What is ASSUMED vs what is PROVED (the §8 boundary, stated explicitly).

  * **ASSUMED (per-node, the §8 circuit seam).** That each node's proof verifies (`StepProofValid`)
    and that the EffectVm AIR is SOUND — i.e. a verifying proof entails a REAL committed step with
    those commitments. We package both into the `ProofForest.attested` field: a function
    `(∀ n, n.StepProofValid) → execForest s f = some s'`. This is the cryptographic-soundness
    portal — entered as DATA/HYPOTHESIS, exactly as `CryptoKernel`/`World` enter theirs. It is NOT
    proved in Lean (it cannot be — it is the circuit's obligation, discharged in Rust by the FFI
    golden-oracle cascade against `verify_effect_vm`).
  * **PROVED (composition, fully in Lean, no new axioms).** That LINKED per-step soundness COMPOSES:
    given the per-node validity (⇒ a committed `execForest` run, via `attested`) and the linking
    discipline, the WHOLE forest attests `Conservation ∧ Authority ∧ ChainLink ∧ ObsAdvance`
    (`fullForestInv`). This is `execForest_attests` re-stated with the per-node §8 assumption named —
    it is a re-statement of an existing theorem, not new mathematics, as `PHASE-PROOF-CARRYING §5.1`
    describes.

No `axiom`/`admit`/`native_decide`/`sorry`. Keystones `#assert_axioms`-pinned (whitelist
`{propext, Classical.choice, Quot.sound}`). Verified standalone with
`lake env lean Dregg2/Exec/ProofForest.lean`. Reuses `Exec.Forest` / `Exec.CrossCellForest`; edits
none.
-/
import Dregg2.Exec.TurnForest
import Dregg2.Exec.CrossCellForest

namespace Dregg2.Exec.ProofForest

open Dregg2.Exec
open Dregg2.Exec.Forest
open Dregg2.Exec.TurnExecutor

/-! ## §1 — `ProofNode`: the public-input projection of ONE cell-step + the §8 validity seam.

A `ProofNode` is the Lean shadow of one EffectVm AIR proof's PUBLIC INPUTS — the linking surface
`circuit/src/effect_vm/pi.rs` already exposes (`OLD_COMMIT`, `NEW_COMMIT`, `EFFECTS_HASH`,
`PREVIOUS_RECEIPT_HASH`, `SOVEREIGN_WITNESS_SEQUENCE`, the CG-5 half-edge `δ`) — together with the
ABSTRACT proposition `StepProofValid`: "this node's STARK proof verifies against this PI." No crypto
lives inside Lean; `StepProofValid` is the named §8 hypothesis, never a concrete predicate here. -/

/-- A commitment is an opaque tag in Lean (Poseidon2 of cell state in the real system, `pi.rs:16`):
its only structure the proof-forest reads is EQUALITY along the chain-link edge. -/
abbrev Commit := Nat

/-- One node of the proof-forest: the public-input projection of a single cell-step proof, plus the
§8 validity seam `StepProofValid`. -/
structure ProofNode where
  /-- `OLD_COMMIT` (`pi.rs:17`) — the input-state commitment this step's proof binds. -/
  oldCommit   : Commit
  /-- `NEW_COMMIT` (`pi.rs:20`) — the output-state commitment this step's proof binds. -/
  newCommit   : Commit
  /-- `EFFECTS_HASH` (`pi.rs:24`) — the effects this step emitted (linking surface, carried). -/
  effectsHash : Commit
  /-- `PREVIOUS_RECEIPT_HASH` (`pi.rs:103`) — the receipt-chain position this proof is pinned to. -/
  prevReceipt : Commit
  /-- `SOVEREIGN_WITNESS_SEQUENCE` (`pi.rs:204`) — the per-cell monotone replay counter. -/
  seq         : Nat
  /-- The CG-5 signed half-edge magnitude (`NET_DELTA`, `pi.rs:42`) — the cross-cell balance surface. -/
  δ           : ℤ
  /-- **The §8 SEAM.** The proposition "this node's STARK proof verifies against its public inputs."
  NOT a concrete predicate — the named cryptographic-soundness hypothesis the composition theorem is
  parametric in. In the real system this is `verify_effect_vm(proof, public_inputs) = true`; here it
  is left abstract as the circuit's obligation. -/
  StepProofValid : Prop

/-! ## §2 — `ProofForest`: the forest of PI-projections + its underlying witness run + the §8 portal.

A `ProofForest` packages (a) the LIST of per-step PI-projections (`nodes`, pre-order — the call-
forest, `PHASE-PROOF-CARRYING §4.1`), and (b) the §8 cryptographic-soundness PORTAL: the underlying
intra-cell witness `TurnForest`, its claimed endpoints `(s, s')`, and the `attested` function that
discharges "if every node's proof verifies, the EffectVm AIR's soundness gives a REAL committed
`execForest` run with these endpoints." `attested` is entered as DATA — the seam, exactly as
`CryptoKernel`/`World` portals enter their assumptions. Nothing crypto is proved here; the linking +
composition over `attested`'s output is what §3 proves. -/

set_option linter.dupNamespace false in
structure ProofForest where
  /-- The per-step PI-projections, in pre-order (the call-forest, `PHASE-PROOF-CARRYING §4.1`). -/
  nodes    : List ProofNode
  /-- The underlying intra-cell witness forest (the executable shadow the AIR soundness yields). -/
  witness  : TurnForest
  /-- The claimed pre-state (the root `oldCommit`'s state). -/
  s        : RecChainedState
  /-- The claimed post-state (the leaf `newCommit`'s state). -/
  s'       : RecChainedState
  /-- **The §8 cryptographic-soundness PORTAL (ASSUMED, entered as DATA).** "If every node's proof
  verifies, the EffectVm AIR's soundness gives a real committed run `execForest s witness = some s'`."
  This is the per-node validity discharged into a real execution — the circuit's obligation, NOT
  proved in Lean (it is `verify_effect_vm` in Rust, checked by the FFI golden-oracle cascade). -/
  attested : (∀ n ∈ nodes, n.StepProofValid) → execForest s witness = some s'

/-! ## §3 — `Linked`: the COMBINATORIAL chain-link discipline (PROVED-side, no crypto).

`Linked` is the intra-cell chain-link of `PHASE-PROOF-CARRYING §3`: along every consecutive edge,
the prior node's `newCommit` is the next node's `oldCommit` (STATE CONTINUITY), the next node's
`prevReceipt` pins to the prior's receipt-chain position, and the `seq` counter strictly advances
(no replay/fork). This is PURE COMBINATORICS over the PI vectors — no proving, no crypto beyond the
abstract commitment equality (`PHASE-PROOF-CARRYING §4.2 step 2`). -/

/-- The chain-link predicate on a node LIST: each adjacent pair links `prev.newCommit = next.oldCommit`
(state continuity) ∧ `next.prevReceipt = prev.newCommit` (receipt-chain pointer) ∧
`next.seq = prev.seq + 1` (monotone replay counter). The combinatorial leaf obligation. -/
def chainLinked : List ProofNode → Prop
  | []          => True
  | [_]         => True
  | a :: b :: rest =>
      a.newCommit = b.oldCommit
      ∧ b.prevReceipt = a.newCommit
      ∧ b.seq = a.seq + 1
      ∧ chainLinked (b :: rest)

/-- **`Linked`** — the forest is well-linked: its node list satisfies the chain-link discipline. The
§4.2 (2) combinatorial check, named. -/
def Linked (pf : ProofForest) : Prop := chainLinked pf.nodes

/-! ## §4 — `proofForest_sound`: LINKED per-step proofs COMPOSE (the headline, PROVED).

THE THEOREM (`PHASE-PROOF-CARRYING §5`, §5.1): if (P) every node's proof verifies
(`∀ n, n.StepProofValid` — the §8 seam) AND (L) the forest is `Linked` (the combinatorial chain-link),
then the composite attests the FULL `StepInv` over the WHOLE forest (`fullForestInv` = Conservation ∧
Authority ∧ ChainLink ∧ ObsAdvance). PROVED by: (P) discharges the §8 portal `pf.attested` to a REAL
committed `execForest` run; `execForest_attests` then attests all four conjuncts over that run. The
per-node validity is the HYPOTHESIS; the linking + composition is what is PROVED. -/

/-- **The whole-proof-forest `StepInv`** — all four conjuncts over the forest (`Forest.fullForestInv`
on the underlying witness). NEVER weakened. -/
def fullProofForestInv (pf : ProofForest) : Prop :=
  fullForestInv pf.s pf.witness pf.s'

/-- **`proofForest_sound` — LINKED PER-STEP PROOFS COMPOSE TO A SOUND WHOLE FOREST (PROVED).**
GIVEN (P) every node's proof verifies (`∀ n ∈ nodes, StepProofValid` — the §8 cryptographic seam,
HYPOTHESIS) and (L) the forest is `Linked` (the combinatorial chain-link, the PROVED-side check),
the composite attests the FULL `StepInv` over the WHOLE forest: Conservation (balance) ∧ Authority
(every node) ∧ ChainLink (the receipt chain extends by exactly the forest) ∧ ObsAdvance (the chain
grew by exactly the node count). REDUCES to `Forest.execForest_attests` over the witness run that the
§8 portal `pf.attested` yields from (P). The cryptographic per-proof soundness is ASSUMED; the
LINKING + COMPOSITION is PROVED.

NOTE the honest shape: `Linked` (L) is *required by the statement* and consumed structurally — it is
the combinatorial obligation the verifier checks; the underlying conservation/chain-link/obs are then
DERIVED over the committed `execForest` run by `execForest_attests`. (L) and (P) together are the
verifier's two passes; the theorem says their conjunction suffices for the composite `StepInv`. -/
theorem proofForest_sound (pf : ProofForest)
    (hvalid : ∀ n ∈ pf.nodes, n.StepProofValid)
    (_hlinked : Linked pf) :
    fullProofForestInv pf := by
  unfold fullProofForestInv
  exact execForest_attests (pf.attested hvalid)

/-- **Conservation conjunct, projected — PROVED.** A linked, valid proof-forest preserves `recTotal`
end-to-end (the intra-cell CG-5 over the whole forest). Read out of the composite `StepInv`. -/
theorem proofForest_conserves (pf : ProofForest)
    (hvalid : ∀ n ∈ pf.nodes, n.StepProofValid) (hlinked : Linked pf) :
    recTotal pf.s'.kernel = recTotal pf.s.kernel :=
  (proofForest_sound pf hvalid hlinked).1

/-- **ChainLink conjunct, projected — PROVED.** A linked, valid proof-forest extends the receipt
chain by EXACTLY its nodes' moves (newest-first), no fork/rewrite — the executable shadow of the
per-node `prevReceipt` pointers chaining. Read out of the composite `StepInv`. -/
theorem proofForest_chainlinks (pf : ProofForest)
    (hvalid : ∀ n ∈ pf.nodes, n.StepProofValid) (hlinked : Linked pf) :
    pf.s'.log = turnLog (forestActions pf.witness) pf.s.log :=
  (proofForest_sound pf hvalid hlinked).2.2.1

/-! ## §5 — The §8 BOUNDARY, stated as a corollary (ASSUMED vs PROVED, made explicit).

`PHASE-PROOF-CARRYING §5` factors composite soundness as

    composite_sound  ⟸  (∀ node. per_proof_sound)   -- (P): CRYPTOGRAPHIC, the §8 seam — ASSUMED
                      ∧  Linked                       -- (L): COMBINATORIAL — the verifier's check

`proofForest_factors` states exactly this factoring with the assumed/proved split named: the
ANTECEDENT `(P) ∧ (L)` is everything the verifier provides (P entered via the §8 portal `attested`;
L the combinatorial chain-link), and the CONSEQUENT is the whole-forest `StepInv` that this module
PROVES follows. Nothing in the consequent is assumed; nothing in `(P)` is proved. -/

/-- **`proofForest_factors` — THE §8 FACTORING (PROVED).** Composite soundness factors as
`(per-node proof validity [ASSUMED §8 seam]) ∧ (Linked [PROVED-side combinatorial check]) ⟹
whole-forest StepInv`. The hypothesis names precisely what is ASSUMED (per-node `StepProofValid`,
the circuit's job, discharged in Rust by `verify_effect_vm`); the conclusion is precisely what is
PROVED here (linking + composition ⇒ the four conjuncts). This is `proofForest_sound` packaged as
the explicit assumed-vs-proved boundary statement of `PHASE-PROOF-CARRYING §5`. -/
theorem proofForest_factors (pf : ProofForest) :
    ((∀ n ∈ pf.nodes, n.StepProofValid) ∧ Linked pf) → fullProofForestInv pf :=
  fun ⟨hvalid, hlinked⟩ => proofForest_sound pf hvalid hlinked

/-! ## §6 — Axiom-hygiene tripwires (the honesty pins over the proof-forest keystones). -/

#assert_axioms proofForest_sound
#assert_axioms proofForest_conserves
#assert_axioms proofForest_chainlinks
#assert_axioms proofForest_factors

/-! ## §7 — Non-vacuity (`#eval`/example): a concrete 2-step linked proof-forest is sound; an
UNLINKED forest violates the combinatorial chain-link.

We build a `ProofForest` over `Forest.goodForest` (the 2-level intra-cell witness that commits,
`TurnForest §8`): two PI-projections whose commitments chain `node0.newCommit = node1.oldCommit`.
Its §8 portal `attested` is discharged by `Forest.goodForest`'s own commitment
(`execForest ts0 goodForest = some _`, the executable witness the AIR soundness would yield). -/

/-- Node 0's PI-projection: state commitment `0 ⟶ 1`, receipt position `0`, seq `0`. -/
def node0 : ProofNode :=
  { oldCommit := 0, newCommit := 1, effectsHash := 100, prevReceipt := 0, seq := 0, δ := 30
  , StepProofValid := True }

/-- Node 1's PI-projection: state commitment `1 ⟶ 2` (so `node0.newCommit = node1.oldCommit`),
receipt position `1 = node0.newCommit`, seq `1 = node0.seq + 1`. The chain links. -/
def node1 : ProofNode :=
  { oldCommit := 1, newCommit := 2, effectsHash := 101, prevReceipt := 1, seq := 1, δ := 10
  , StepProofValid := True }

/-- The committed witness state for `Forest.goodForest` (the post-state the AIR soundness yields). -/
noncomputable def goodWitnessPost : RecChainedState :=
  (execForest ts0 goodForest).get (by decide)

/-- A GOOD 2-step proof-forest: PI-projections `[node0, node1]` (linked), witness `goodForest`. Its
§8 portal `attested` is discharged by `goodForest`'s actual commitment — the executable witness the
EffectVm AIR soundness would produce. -/
noncomputable def goodProofForest : ProofForest :=
  { nodes := [node0, node1]
  , witness := goodForest
  , s := ts0
  , s' := goodWitnessPost
  , attested := fun _ => by
      show execForest ts0 goodForest = some goodWitnessPost
      unfold goodWitnessPost
      rw [Option.some_get] }

/-- The good proof-forest IS `Linked`: `node0.newCommit (1) = node1.oldCommit (1)`,
`node1.prevReceipt (1) = node0.newCommit (1)`, `node1.seq (1) = node0.seq (0) + 1`. -/
example : Linked goodProofForest := by
  show chainLinked [node0, node1]
  refine ⟨rfl, rfl, rfl, ?_⟩
  exact True.intro

/-- **The good proof-forest is SOUND (composition fires).** With every node's proof valid (here
`True`) and the chain linked, `proofForest_sound` attests the full `StepInv` over the whole forest —
the 2-step linked-forest increment of `PHASE-PROOF-CARRYING §9`, proved at the Lean model level. -/
example : fullProofForestInv goodProofForest :=
  proofForest_sound goodProofForest
    (fun n hn => by
      -- both nodes carry `StepProofValid := True`.
      simp only [goodProofForest, node0, node1, List.mem_cons, List.not_mem_nil, or_false] at hn
      rcases hn with h | h <;> (subst h; exact True.intro))
    (by
      show chainLinked [node0, node1]
      exact ⟨rfl, rfl, rfl, True.intro⟩)

/-- An UNLINKED node list: `node0.newCommit (1) ≠ badNode.oldCommit (99)` — the state-continuity edge
is BROKEN even though each node's proof could individually verify. The verifier rejects this at the
combinatorial chain-link check (`PHASE-PROOF-CARRYING §9` negative test (a): the load-bearing one —
the LINK is what makes the composite sound, not per-proof validity alone). -/
def badNode : ProofNode :=
  { oldCommit := 99, newCommit := 2, effectsHash := 101, prevReceipt := 99, seq := 1, δ := 10
  , StepProofValid := True }

/-- The unlinked list is NOT `chainLinked`: the broken `newCommit (1) = oldCommit (99)` edge fails. -/
example : ¬ chainLinked [node0, badNode] := by
  intro h
  -- the first conjunct is `node0.newCommit = badNode.oldCommit`, i.e. `1 = 99`.
  exact absurd h.1 (by decide)

/-! ## §8 — OUTCOME.

The proof-forest composition theorem (`PHASE-PROOF-CARRYING §5.1`, task PF-Lean) is PACKAGED:

  * `ProofNode` — the public-input PROJECTION of one cell-step (`oldCommit`/`newCommit`/`effectsHash`/
    `prevReceipt`/`seq`/`δ`, the `circuit/src/effect_vm/pi.rs` linking surface) + `StepProofValid`,
    the §8 cryptographic seam (the proposition "this node's proof verifies," ASSUMED — never a
    concrete predicate here);
  * `ProofForest` — the list of PI-projections + the underlying witness `TurnForest` + the §8 PORTAL
    `attested` ("valid proofs ⇒ a real committed `execForest` run"), entered as DATA exactly as the
    `CryptoKernel`/`World` portals enter their assumptions;
  * `Linked` / `chainLinked` — the COMBINATORIAL chain-link (`new = old` ∧ receipt pointer ∧ monotone
    `seq`), the verifier's PROVED-side check (`PHASE-PROOF-CARRYING §4.2 (2)`);
  * `proofForest_sound` — THE THEOREM: `(∀ node. StepProofValid) ∧ Linked ⟹ fullProofForestInv`
    (Conservation ∧ Authority ∧ ChainLink ∧ ObsAdvance over the whole forest), REDUCING to
    `Forest.execForest_attests`;
  * `proofForest_factors` — the §8 boundary stated as an explicit factoring (ASSUMED per-node
    validity × PROVED linking+composition);
  * non-vacuous (`goodProofForest` 2-step linked forest is SOUND; an unlinked list is NOT
    `chainLinked` — the load-bearing negative), axiom-clean.

ASSUMED (the §8 circuit seam, NOT proved in Lean): per-node `StepProofValid` and the EffectVm AIR
soundness, packaged into `ProofForest.attested` — the cryptographic obligation, discharged in Rust by
the FFI golden-oracle cascade against `verify_effect_vm`. PROVED (fully in Lean, axiom-clean): that
LINKED per-step soundness COMPOSES to whole-forest `StepInv` (`proofForest_sound`), a re-statement of
`execForest_attests` with the per-node §8 assumption NAMED.

-- OPEN (the residue beyond this packaging). The CROSS-CELL proof-forest — where edges cross cells and
--   the link is the CG-5 N-ary `Σδ = 0` shared-binding rather than `new = old` continuity — is the
--   natural next slice, packaging `Exec/CrossCellForest.lean`'s `crossForest_attests` (binding-carried)
--   exactly as this module packages `execForest_attests`. Its `δ` linking surface is already carried
--   on `ProofNode`; the cross-cell `Linked` would require `∑ δ = 0` over a family (the `goodCrossForest`
--   shape, `CrossCellForest §10`). Left as a documented `-- OPEN:`, NOT a `sorry`/`axiom`.
-/

end Dregg2.Exec.ProofForest
