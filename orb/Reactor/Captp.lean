import Reactor.Serve
import Reactor.Bridge
import Captp.Session

/-!
# Reactor.Netlayer — the real Captp import/export table on the deployed serve path

`Captp` is the capability seam to the wider fabric: objects are named on the
wire by descriptors, a session's import/export/answer tables assign the
positions, and every table entry is epoch-tagged so a session reset invalidates
previously captured references (`Captp.Session`). Until now the library was
proven in isolation; nothing on the running path held a session.

This file threads the REAL `Captp.Session` down the reactor request path,
anchored to the `Reactor.serve` test view. `Arena.Orb.main` runs `serveFull`
over `Reactor.Deploy.deployConfig`; on the plainH1 dispatch path the Bridge
congruence (`Bridge.deployed_routes`) identifies `serve`'s routing with the
deployed submissions, so the captp step's routing lands on the deployed path too
(`grant_serves_routed_deployed`):

  * `grantStep` — serve the request through the deployed `Reactor.serve` and, in
    the same step, hand a capability-scoped reference across the netlayer seam:
    the request's object identity is exported into the real session's export
    table (`Captp.Session.exportObject`), producing a wire descriptor
    (`Descriptor.Export pos`) stamped with the session's current epoch. The pair
    is a `Grant` — exactly what crosses to the peer.
  * `acceptPeer` — the inbound half: bind a peer-offered object into the real
    import table (`Captp.Session.importObject`), again with an epoch stamp.
  * `pipeline` / `settle` — promise pipelining for a dispatched request: allocate
    an answer position (`allocateAnswer`) with the served request's identity, and
    deliver its resolution through the real one-shot gate (`tryResolve`).

The wiring is a pure side-channel on the response path: `grantStep_transparent`
and `respWindow_eq_map_serve` show the served bytes are exactly `Reactor.serve`'s
(never rewritten), and `grant_serves_routed` re-exposes the deployed routing fact
(`serve_routes`) through the captp step.

**Seam theorems.**

  * `captp_epoch_seam` (headline) — a descriptor the reactor resolves is valid
    only within its epoch: any stamped reference that resolves in the reactor's
    post-grant session is REJECTED after any future run of session operations
    that bumped the epoch and rebound the descriptor's position — the real
    `Captp.Session.bump_invalidates` composed with the reactor's session state,
    with well-formedness discharged (not assumed) via `exportObject_wf` /
    `grantRun_wf` from the deployed cold start (`init_wf`).
  * `captp_epoch_seam_grant` — the same, instantiated at the reactor's OWN grant:
    the reference `grantStep` handed across the seam dies with its epoch.
  * `reset_rebind_rejects_stale` — the concrete replay: a peer-imported grant,
    after a session reset (`bumpEpoch`) and the peer rebinding the SAME position
    to a new object, no longer resolves under its pre-reset stamp (the real
    `bump_then_reimport_invalidates`, on the reactor's accept path).
  * `pipeline_one_shot` / `settle_once` — a promise the reactor pipelines for a
    served request settles EXACTLY once: the first delivery succeeds, a second
    delivery on the same position fails (the real `tryResolve_once`, driven).
-/

namespace Reactor
namespace Netlayer

open Proto (Bytes)

/-- The object identity a served request denotes across the netlayer seam: a
little-endian-style fold of its bytes into the abstract `Captp.Obj` atom (the
content-hash altitude of `Captp.Basic`). -/
def objOf (input : Bytes) : Captp.Obj :=
  input.foldl (fun a b => a * 256 + b.toNat) 0

/-- A capability reference handed across the netlayer seam: the wire descriptor
plus the epoch stamp captured when the reactor granted it. Resolution later is
`resolveStamped` — valid only while the stamp matches the live entry's epoch. -/
structure Grant where
  desc  : Captp.Descriptor
  stamp : Nat
deriving Repr

/-- The netlayer state threaded down the reactor path: the REAL `Captp.Session`
(import/export/answer tables, epoch), plus the grants handed out so far (newest
first). -/
structure NetState where
  session : Captp.Session
  granted : List Grant

/-- Cold start: the real initial session (empty tables, epoch 1), no grants. -/
def NetState.init : NetState :=
  { session := Captp.Session.init, granted := [] }

/-- The grant a request produces in a given state: the export position the REAL
export table allocates for the request's object, stamped with the session's
current epoch. -/
def grantOf (st : NetState) (input : Bytes) : Grant :=
  { desc  := .Export (st.session.exportObject (objOf input)).1
  , stamp := st.session.epoch }

/-- The session after the grant: the REAL `exportObject` update. -/
def sessionAfter (st : NetState) (input : Bytes) : Captp.Session :=
  (st.session.exportObject (objOf input)).2

/-- **The captp-wired reactor step.** Serve the request through the
`Reactor.serve` test view and, in the same step, export a capability reference
for the request into the REAL Captp export table — the reference the reactor
hands across the netlayer seam. (`main` runs `serveFull` over `deployConfig`; the
served-byte routing lifts to that deployed path via the Bridge congruence —
`grant_serves_routed_deployed`.) -/
def grantStep (st : NetState) (input : Bytes) : Bytes × Grant × NetState :=
  ( Reactor.serve input
  , grantOf st input
  , { session := sessionAfter st input
    , granted := grantOf st input :: st.granted } )

/-- Thread the netlayer state over a window of requests, left to right. -/
def grantRun (st : NetState) : List Bytes → NetState
  | [] => st
  | input :: rest => grantRun (grantStep st input).2.2 rest

/-- The served responses over a window — each is exactly the deployed reactor's. -/
def respWindow (st : NetState) : List Bytes → List Bytes
  | [] => []
  | input :: rest =>
      (grantStep st input).1 :: respWindow (grantStep st input).2.2 rest

/-! ## Transparency — the captp wiring never touches the served bytes -/

/-- The bytes `grantStep` returns are exactly the deployed `Reactor.serve`'s. -/
theorem grantStep_transparent (st : NetState) (input : Bytes) :
    (grantStep st input).1 = Reactor.serve input := rfl

/-- Over a window, the served responses are exactly `serve` mapped over the
requests — granting capabilities is a pure side-channel on the deployed path. -/
theorem respWindow_eq_map_serve (st : NetState) (inputs : List Bytes) :
    respWindow st inputs = inputs.map Reactor.serve := by
  induction inputs generalizing st with
  | nil => rfl
  | cons input rest ih =>
    show (grantStep st input).1 :: respWindow (grantStep st input).2.2 rest
        = Reactor.serve input :: rest.map Reactor.serve
    rw [ih (grantStep st input).2.2]
    rfl

/-- The deployed routing fact, through the captp step: when the reactor
dispatches `req` (and emitted no response of its own), the captp-wired step
serves exactly `serialize (App.handle demoAppConfig req)` — the same real
route table `main`'s serve answers with. -/
theorem grant_serves_routed (st : NetState) (input : Bytes) (req : Proto.Request)
    (rest : List RingSubmission)
    (hsends : sendsOf (reactorSubs input) = [])
    (hsub : reactorSubs input = .dispatch req :: rest) :
    (grantStep st input).1 = serialize (App.handle demoAppConfig req) :=
  serve_routes input req rest hsends hsub

/-- **Deployed routing through the captp step.** On the DEPLOYED submissions the
orb acts on — `Reactor.Deploy.deploySubs input`, what `serveFull`/`main` runs —
when the reactor dispatches `req` with no FSM send bytes, the captp-wired step's
served bytes are exactly `serialize (App.handle demoAppConfig req)`. The captp
session lane is a transparent side-channel (`grantStep_transparent`); the routing
fact is landed on the deployed path by the Bridge congruence
(`Bridge.deployed_routes`), whose content is the same `serve_routes` seam. -/
theorem grant_serves_routed_deployed (st : NetState) (input : Bytes)
    (req : Proto.Request) (rest : List RingSubmission)
    (hsends : sendsOf (Reactor.Deploy.deploySubs input) = [])
    (hsub : Reactor.Deploy.deploySubs input = .dispatch req :: rest) :
    (grantStep st input).1 = serialize (App.handle demoAppConfig req) := by
  rw [grantStep_transparent]
  exact Reactor.Bridge.deployed_routes input req rest hsends hsub

/-! ## Well-formedness is preserved along the deployed path

`bump_invalidates` (the epoch guard) needs `Session.WF`. The reactor does not
assume it: the cold start is well-formed (`Captp.Session.WF.init`) and every
step of the wiring preserves it. -/

/-- Exporting an object preserves session well-formedness: the fresh entry
carries the current epoch; every other table is untouched. -/
theorem exportObject_wf {s : Captp.Session} (h : s.WF) (o : Captp.Obj) :
    (s.exportObject o).2.WF where
  epoch_pos := h.epoch_pos
  exp_epoch := by
    intro p e hp
    simp only [Captp.Session.exportObject] at hp
    by_cases hpe : p = s.nextExport
    · subst hpe
      rw [Captp.upd_self] at hp
      cases hp
      exact ⟨h.epoch_pos, Nat.le_refl _⟩
    · rw [Captp.upd_ne _ _ hpe] at hp
      exact h.exp_epoch p e hp
  imp_epoch := fun p e hp => h.imp_epoch p e hp
  ans_epoch := fun p e hp => h.ans_epoch p e hp
  ans_bound := fun p e hp => h.ans_bound p e hp

/-- Importing a peer object preserves session well-formedness. -/
theorem importObject_wf {s : Captp.Session} (h : s.WF) (pos : Captp.Position)
    (o : Captp.Obj) : (s.importObject pos o).WF where
  epoch_pos := h.epoch_pos
  exp_epoch := fun p e hp => h.exp_epoch p e hp
  imp_epoch := by
    intro p e hp
    simp only [Captp.Session.importObject] at hp
    by_cases hpe : p = pos
    · subst hpe
      rw [Captp.upd_self] at hp
      cases hp
      exact ⟨h.epoch_pos, Nat.le_refl _⟩
    · rw [Captp.upd_ne _ _ hpe] at hp
      exact h.imp_epoch p e hp
  ans_epoch := fun p e hp => h.ans_epoch p e hp
  ans_bound := fun p e hp => h.ans_bound p e hp

/-- The deployed cold start is well-formed. -/
theorem init_wf : NetState.init.session.WF := Captp.Session.WF.init

/-- One captp-wired step preserves well-formedness. -/
theorem grantStep_wf {st : NetState} (h : st.session.WF) (input : Bytes) :
    (grantStep st input).2.2.session.WF :=
  exportObject_wf h (objOf input)

/-- Well-formedness holds after any window of served requests — so the epoch
guard's precondition is discharged along the whole deployed path, from
`NetState.init` on. -/
theorem grantRun_wf {st : NetState} (h : st.session.WF) (inputs : List Bytes) :
    (grantRun st inputs).session.WF := by
  induction inputs generalizing st with
  | nil => exact h
  | cons input rest ih => exact ih (grantStep_wf h input)

/-! ## The grant round-trips within its epoch -/

/-- The reference the reactor hands out resolves — stamped — to the served
request's object, in the reactor's own post-grant session (the real
`export_stamped_resolves` round-trip). -/
theorem grant_resolves (st : NetState) (input : Bytes) :
    (sessionAfter st input).resolveStamped
        (grantOf st input).desc (grantOf st input).stamp
      = some (objOf input) :=
  Captp.Session.export_stamped_resolves st.session (objOf input)

/-! ## Seam — descriptors are valid only within their epoch -/

/-- **`captp_epoch_seam` (headline).** A descriptor the reactor resolves is
valid ONLY within its epoch: take any stamped reference that resolves in the
reactor's post-grant session (a reference the reactor could hand across the
netlayer seam), and any future run of session operations. If that run bumped
the epoch and the descriptor's position is (re)bound at the new current epoch,
the old stamp is REJECTED — resolution returns `none`. This is the real
`Captp.Session.bump_invalidates` composed with the reactor's session state;
its `WF` precondition is discharged by the reactor's own preservation chain
(`init_wf` → `grantRun_wf` → `exportObject_wf`), not assumed out of thin air. -/
theorem captp_epoch_seam {st : NetState} (hwf : st.session.WF) (input : Bytes)
    {d : Captp.Descriptor} {e : Nat} {o : Captp.Obj}
    (hcap : (sessionAfter st input).resolveStamped d e = some o)
    (ops : List Captp.Session.Op)
    (hcur : ((sessionAfter st input).run ops).descEpoch d
        = some (((sessionAfter st input).run ops).epoch))
    (hbump : (sessionAfter st input).epoch < ((sessionAfter st input).run ops).epoch) :
    ((sessionAfter st input).run ops).resolveStamped d e = none :=
  Captp.Session.bump_invalidates (exportObject_wf hwf (objOf input)) hcap ops hcur hbump

/-- The epoch seam at the reactor's OWN grant: the reference `grantStep` handed
across the seam (which provably resolved at grant time, `grant_resolves`) is
rejected after any epoch-advancing run that rebound its position. -/
theorem captp_epoch_seam_grant {st : NetState} (hwf : st.session.WF) (input : Bytes)
    (ops : List Captp.Session.Op)
    (hcur : ((sessionAfter st input).run ops).descEpoch (grantOf st input).desc
        = some (((sessionAfter st input).run ops).epoch))
    (hbump : (sessionAfter st input).epoch < ((sessionAfter st input).run ops).epoch) :
    ((sessionAfter st input).run ops).resolveStamped
        (grantOf st input).desc (grantOf st input).stamp = none :=
  captp_epoch_seam hwf input (grant_resolves st input) ops hcur hbump

/-! ## The accept path and the concrete reset replay -/

/-- The inbound half of the seam: bind a peer-offered object at a peer-chosen
import position in the REAL import table, returning the stamped reference the
reactor holds for it. -/
def acceptPeer (st : NetState) (pos : Captp.Position) (o : Captp.Obj) :
    Grant × NetState :=
  ( { desc := .ImportObject pos, stamp := st.session.epoch }
  , { session := st.session.importObject pos o
    , granted := { desc := Captp.Descriptor.ImportObject pos
                 , stamp := st.session.epoch } :: st.granted } )

/-- An accepted peer reference resolves — stamped — to the peer's object (the
real `import_resolves` round-trip). -/
theorem accept_resolves (st : NetState) (pos : Captp.Position) (o : Captp.Obj) :
    (acceptPeer st pos o).2.session.resolveStamped
        (acceptPeer st pos o).1.desc (acceptPeer st pos o).1.stamp = some o :=
  (Captp.Session.import_resolves st.session pos o).2

/-- **Concrete epoch-seam replay on the accept path.** After a session reset
(`bumpEpoch`, a reconnect) and the peer rebinding the SAME import position to a
NEW object, the reference accepted before the reset no longer resolves under
its pre-reset stamp — the ABA defense, on the reactor's state (the real
`bump_then_reimport_invalidates`). -/
theorem reset_rebind_rejects_stale (st : NetState) (hwf : st.session.WF)
    (pos : Captp.Position) (o o' : Captp.Obj) :
    (((acceptPeer st pos o).2.session.bumpEpoch).importObject pos o').resolveStamped
        (acceptPeer st pos o).1.desc (acceptPeer st pos o).1.stamp = none :=
  Captp.Session.bump_then_reimport_invalidates
    (importObject_wf hwf pos o) (accept_resolves st pos o)

/-! ## Promise pipelining — one-shot on the reactor path -/

/-- Serve a request through the `Reactor.serve` test view and allocate an answer
position (a promise) for it in the REAL answer table — the pipelining vehicle
for a dispatched request whose result arrives later. -/
def pipeline (st : NetState) (input : Bytes) : Bytes × Captp.Position × NetState :=
  ( Reactor.serve input
  , (st.session.allocateAnswer (objOf input)).1
  , { st with session := (st.session.allocateAnswer (objOf input)).2 } )

/-- Deliver a promise's resolution through the REAL one-shot gate
(`Captp.Session.tryResolve`); `none` = the delivery was refused. -/
def settle (st : NetState) (pos : Captp.Position) : Option NetState :=
  match st.session.tryResolve pos with
  | some s => some { st with session := s }
  | none => none

/-- Pipelining never touches the served bytes either. -/
theorem pipeline_transparent (st : NetState) (input : Bytes) :
    (pipeline st input).1 = Reactor.serve input := rfl

/-- **A delivered promise never settles twice (step form).** If a delivery
succeeded on the reactor path, a second delivery at the same position fails —
the real `tryResolve_once` linear discipline, lifted to the netlayer state. -/
theorem settle_once {st st' : NetState} {pos : Captp.Position}
    (h : settle st pos = some st') : settle st' pos = none := by
  unfold settle at h
  cases hs : st.session.tryResolve pos with
  | none => rw [hs] at h; exact absurd h (by simp)
  | some s =>
    rw [hs] at h
    have hsess : st'.session = s := by cases h; rfl
    unfold settle
    rw [hsess, Captp.Session.tryResolve_once hs]

/-- **`pipeline_one_shot`.** A promise the reactor pipelines for a served
request settles EXACTLY once: the first delivery succeeds, and the second
delivery on the same position is refused. Composes the real `tryResolve_success`
(the fresh answer is live and unresolved) with `tryResolve_once`. -/
theorem pipeline_one_shot (st : NetState) (input : Bytes) :
    ∃ st', settle (pipeline st input).2.2 (pipeline st input).2.1 = some st'
      ∧ settle st' (pipeline st input).2.1 = none := by
  have halloc : (pipeline st input).2.2.session.answers (pipeline st input).2.1
      = some { promise := objOf input, resolved := false, epoch := st.session.epoch } :=
    Captp.upd_self _ _ _
  have hres := Captp.Session.tryResolve_success halloc rfl
  have hset : settle (pipeline st input).2.2 (pipeline st input).2.1
      = some { (pipeline st input).2.2 with
                session := { (pipeline st input).2.2.session with
                  answers := Captp.upd (pipeline st input).2.2.session.answers
                    (pipeline st input).2.1
                    (some { promise := objOf input, resolved := true
                          , epoch := st.session.epoch }) } } := by
    unfold settle
    rw [hres]
  exact ⟨_, hset, settle_once hset⟩

/-! ## Cold-start sanity -/

/-- The very first grant on the deployed cold start: export position 0, epoch
stamp 1 — and it resolves to the request's object. -/
example (input : Bytes) :
    grantOf NetState.init input = { desc := .Export 0, stamp := 1 } := rfl

example :
    (sessionAfter NetState.init (str "GET /health HTTP/1.1\r\n\r\n")).resolveStamped
        (Captp.Descriptor.Export 0) 1
      = some (objOf (str "GET /health HTTP/1.1\r\n\r\n")) :=
  grant_resolves NetState.init (str "GET /health HTTP/1.1\r\n\r\n")

/-- A stamped grant from epoch 1 dies at the sentinel test: stamp 0 (the
reserved no-epoch) never resolves in a well-formed session. -/
example (input : Bytes) (d : Captp.Descriptor) :
    (sessionAfter NetState.init input).resolveStamped d 0 = none :=
  Captp.Session.resolveStamped_zero (exportObject_wf init_wf (objOf input)) d

end Netlayer
end Reactor
