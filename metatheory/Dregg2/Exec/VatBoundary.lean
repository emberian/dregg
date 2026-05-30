/-
# Dregg2.Exec.VatBoundary — the vat-boundary authority law ON the living cell.

This wires the three layers together — the living coinductive cell (`Exec/Cell.lean`), the
keys-as-caps token layer (`Authority/Caveat.lean`), and the l4v integrity lift
(`Authority/Positional.lean`'s `Integrity`) — into **the vat-boundary law on a real, executable,
step-complete cell** (`dregg2 §3`, `cand-A §11`, `cand-C §4`):

  * **intra-vat** (the turn stays within one trust-root): admissible by the **trivial witness** — the
    cell's own positional `authorizedB` (caps-as-caps, mediator-enforced); `Integrity.intra`.
  * **cross-vat** (the turn crosses a boundary): admissible **iff a presented token discharges the
    request** (keys-as-caps); the token verification IS the discharging witness; `Integrity.cross`.

The crypto substitution `discoveries §3` describes — *replace the positional `∃ cap ∈ caps` with the
decidable `Verify P w = true`* — is here literal: the cross case's witness is a `Caveat.Token`, and
`Discharged` is `Token.admits = true`. So the macaroon/biscuit/caveat framework now gates a genuine
turn on a genuine cell, and the vat-boundary law is a theorem about that gate.
-/
import Dregg2.Exec.Cell
import Dregg2.Authority.Caveat
import Dregg2.Authority.Positional

namespace Dregg2.Exec

open Dregg2.Authority Dregg2.Laws

/-- The request binding-site a cross-vat caveat is evaluated against (the `AuthRequest` facts): the
turn's actor and the chain height (a logical clock). -/
structure Req where
  actor  : CellId
  height : Nat
  deriving DecidableEq, Repr, Inhabited

/-- The request a turn `t` raises from state `s` (height = the pre-state chain length). -/
def reqOf (s : ChainedState) (t : Turn) : Req := { actor := t.actor, height := s.log.length }

/-- The request recoverable from a *committed post-state* `s'` (the chain records the turn at its
head, so the request is a function of the post-state alone — which is what `Integrity`'s `p : KO →
KO → P` needs). -/
def reqFromPost (s' : ChainedState) : Req :=
  match s'.log with
  | t :: _ => { actor := t.actor, height := s'.log.length - 1 }
  | []     => default

/-- **`reqFromPost_commit` (PROVED)** — on a committed step the post-state's recovered request equals
the turn's request: `reqFromPost s' = reqOf s t` (because `cexec` appends `t` to the chain head).
This is what lets the cross-vat witness, checked against `reqOf s t`, discharge the state-relation
predicate `p s s' = reqFromPost s'`. -/
theorem reqFromPost_commit {s s' : ChainedState} {t : Turn} (h : cexec s t = some s') :
    reqFromPost s' = reqOf s t := by
  have hchain : s'.log = t :: s.log := (cexec_attests h).2.2.1
  unfold reqFromPost reqOf
  rw [hchain]; simp

/-- **A crossing turn**: the base turn, whether it crosses a vat boundary, and (if so) the presented
keys-as-caps `Token` + its `discharges`. Intra-vat turns carry the token field but it is unused
(caps-as-caps needs no witness). -/
structure VatTurn where
  turn       : Turn
  crossing   : Bool
  token      : Token Req Unit
  discharges : Discharges Unit

/-- **The vat-boundary admissibility decision.** Intra-vat ⇒ the cell's positional `authorizedB`
(the mediator's caps-as-caps guarantee); cross-vat ⇒ the presented token must discharge the request
(keys-as-caps). Fail-closed either way. -/
def vatAdmits (s : ChainedState) (vt : VatTurn) : Bool :=
  match vt.crossing with
  | true  => vt.token.admits (reqOf s vt.turn) vt.discharges
  | false => authorizedB s.kernel.caps vt.turn

variable (owner : Label) (subjects : List Label)

/-- The integrity change-predicate for the living cell: a change `s → s'` raises the request
recovered from the committed post-state. (`Integrity`'s `p : KO → KO → P`.) -/
def cellChangeReq : ChainedState → ChainedState → Req := fun _ s' => reqFromPost s'

/-! ## The vat-boundary law on the living cell (the keystone, PROVED). -/

/-- **`vat_boundary_law` (PROVED) — the vat-boundary law, realized on the executable living cell.**
Every admissible committed turn respects `Authority.Integrity`:
  * a **cross-vat** turn is admitted by `Integrity.cross` with the **presented token as the
    discharging witness** (`reqFromPost_commit` aligns the checked request with `p s s'`);
  * an **intra-vat** turn is admitted by `Integrity.intra` (the owning vat may change its own state),
    given the cell's trust-root owns the actor (`owner ∈ subjects`).
This is the keys-as-caps cross-vat case of `dregg2 §3` made literal: the caveat chain gates a real
turn on a real cell, and admissibility ⇔ `Verify P w = true`. -/
theorem vat_boundary_law (s s' : ChainedState) (vt : VatTurn)
    (hown : owner ∈ subjects)
    (hcommit : cexec s vt.turn = some s')
    (hadm : vatAdmits s vt = true) :
    Integrity (P := Req) (W := Token Req Unit × Discharges Unit)
      owner subjects (cellChangeReq) s s' := by
  cases hcr : vt.crossing with
  | true =>
      -- cross-vat: the token IS the discharging witness.
      refine Integrity.cross (vt.token, vt.discharges) ?_
      show Verifiable.Verify (cellChangeReq s s') (vt.token, vt.discharges) = true
      show vt.token.admits (cellChangeReq s s') vt.discharges = true
      unfold cellChangeReq
      rw [reqFromPost_commit hcommit]
      simp only [vatAdmits, hcr] at hadm
      exact hadm
  | false =>
      -- intra-vat: the owning vat may change its own state (trivial witness).
      exact Integrity.intra hown

/-- **`vat_boundary_intra` (PROVED)** — the intra-vat half, standalone: an in-trust-root turn needs
no witness (caps-as-caps); the owning vat's change is admissible by `troa_lrefl`/`Integrity.intra`. -/
theorem vat_boundary_intra (s s' : ChainedState) (hown : owner ∈ subjects) :
    Integrity (P := Req) (W := Token Req Unit × Discharges Unit)
      owner subjects (cellChangeReq) s s' :=
  Integrity.intra hown

/-- **`vat_boundary_cross` (PROVED)** — the cross-vat half, standalone: admissibility across the
boundary is *exactly* token-discharge of the request, with the token as the witness. The decidable
`Verify` has replaced the positional `∃ cap ∈ caps`. -/
theorem vat_boundary_cross (s s' : ChainedState) (t : Turn)
    (tok : Token Req Unit) (d : Discharges Unit)
    (hcommit : cexec s t = some s')
    (hadm : tok.admits (reqOf s t) d = true) :
    Integrity (P := Req) (W := Token Req Unit × Discharges Unit)
      owner subjects (cellChangeReq) s s' := by
  refine Integrity.cross (tok, d) ?_
  show tok.admits (cellChangeReq s s') d = true
  unfold cellChangeReq; rw [reqFromPost_commit hcommit]; exact hadm

/-! ## It runs (`#eval`) — a cross-vat turn gated by a presented token. -/

/-- A cell at chain-length 0; the cross-vat turn presents a biscuit caveated "actor = 0". -/
def actorIs0 : Token Req Unit :=
  { kind := .biscuit, caveats := [.local (fun r => decide (r.actor = 0))] }

/-- A crossing turn `t1` (actor 0) presenting the `actorIs0` biscuit. -/
def crossT1 : VatTurn := { turn := t1, crossing := true, token := actorIs0, discharges := fun _ => false }

/-- A crossing turn by actor 2, presenting the same biscuit — the caveat rejects it. -/
def crossBad : VatTurn := { turn := tBad, crossing := true, token := actorIs0, discharges := fun _ => false }

#eval vatAdmits cell0 crossT1     -- true  (actor 0 satisfies "actor = 0"; token discharges)
#eval vatAdmits cell0 crossBad    -- false (actor 2 fails the caveat — cross-vat denied)
#eval vatAdmits cell0 { turn := t1, crossing := false, token := actorIs0, discharges := fun _ => false }
                                  -- true  (intra-vat: actor 0 owns src 0 by authorizedB)

end Dregg2.Exec
