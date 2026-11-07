/-
# EmitWrapMainJson — write the Lean-assembled `wrap_main` rungs as prover-ready JSON.

Clone of `EmitStepMainJson` for the WRAP side. Everything it writes is over **Fq** and is proved by
`metatheory/fixtures/pickles-wrapmain-harness` on **Pallas**, not Vesta.

⚠ THE SHAPE COMES THROUGH `DREGG_WM` IN THE ENVIRONMENT, NOT `argv`. `lean --run` does not forward
trailing args through `lake env`, and a silently-ignored argument that emits the default shape under
a scale-rung filename is exactly the measurement that lies.

    cd metatheory
    lake build Dregg2.Circuit.Emit.KimchiWrapMain
    DREGG_WM=wrap  lake env lean --run Dregg2/Circuit/Emit/EmitWrapMainJson.lean
    DREGG_WM=smoke lake env lean --run Dregg2/Circuit/Emit/EmitWrapMainJson.lean
    DREGG_WM=wrap DREGG_WM_OUT=/tmp/mine lake env lean --run …    # a lane's OWN directory

Files land in `$DREGG_WM_OUT/wrapmain_<tag>_<rung>{,_unwired}.json`, default
`/tmp/pickles-wrapmain/`. ⚑ `DREGG_WM_OUT` is the step side's `DREGG_SM_OUT` and exists for the same
reason: two revisions emitted for a byte-diff must not write to one path.

Then:

    cargo run --release --manifest-path metatheory/fixtures/pickles-wrapmain-harness/Cargo.toml \
      -- /tmp/pickles-wrapmain wrap
-/
import Dregg2.Circuit.Emit.KimchiWrapMainCore

open Dregg2.Circuit.Emit.KimchiWrapMain
open Dregg2.Circuit.Emit.KimchiPlacement
open Dregg2.Circuit.Emit.KimchiCircuitJson (renderCircuit)

/-- Pin a pure `let` in place before an `IO.monoMsNow`, so a phase split cannot report `0 ms` for
the phase that actually ran. -/
def force (n : Nat) (what : String) : IO Nat := do
  IO.println s!"    [{what}] {n}"
  pure n

/-- Write ATOMICALLY: stage beside the target, then rename into place. The step driver's own
`writeAtomic` and its note apply verbatim here — a reader of the emit directory cannot tell a
complete artifact from one whose writer died mid-`String`, because both are a file with the right
name, and `rename(2)` within one directory is the only thing that makes the real name appear
carrying complete bytes. ⚑ This matters most to the byte-diff gate, whose whole job is to compare
these files against another revision's while an emitter may still be running. -/
def writeAtomic (path contents : String) : IO Unit := do
  let staged := path ++ ".partial"
  IO.FS.writeFile staged contents
  IO.FS.rename staged path

/-- The thirty tracked smoke fixtures' directory, relative to `metatheory/` — the cwd every
documented invocation of this driver uses. -/
def TRACKED_SMOKE_DIR : String := "fixtures/pickles-wrapmain-harness/fixtures"

/-- ⚑⚑ **"INSTALL WHAT YOU EMIT", AS A RED INSTEAD OF AS A COMMENT** — the wrap side's twin of
`pickles_kimchi_marshal::installed_gate`, and it exists because this route had **no refusal at
all**.

`scripts/check-emitter-routing.sh` said so in as many words: *"the thirty tracked
`wrapmain_smoke_*.json` are copied in BY HAND (no route to grade)"*. The `/tmp → fixtures/` hop is a
manual `cp` no script performs, so nothing anywhere compared the tracked bytes against what the Lean
currently emits, and the only stated grade was "the harness proves each rung" — which grades whatever
JSON is on disk, not whether that JSON is this assembly.

⚠ **AND IT HAD STOPPED BEING TRUE.** Measured 2026-08-09: the tracked thirty were last written at
`93bca7b7a` (08-08 07:28) and three later commits moved the wrap assembly under them — the last,
`0047cb876`, rewired `runIpa` onto §19d's fold. The harness had been proving a two-day-old circuit
and reporting green, because a stale fixture is a perfectly provable circuit; it is just not the one
the Lean says.

**The gate is here rather than in a script for the reason `installed_gate` is inside the marshaller:
it fires in the same process that produced the bytes, so re-emitting and not installing is the one
thing it cannot miss.** A gate that lives anywhere else can be skipped by not running it.

`DREGG_WM_INSTALL=1` performs the copy instead of refusing — one command that emits AND installs,
so "re-emit and install" stops being two steps with a human between them. There is deliberately **no
switch that disables the comparison**: a tracked file that is missing or unreadable counts as drift,
so a run from the wrong cwd reds rather than passing vacuously.

Returns the number of tracked files that differ. -/
def installedGate (dir tag : String) (rungs : List Rung) : IO Nat := do
  if tag != "smoke" then
    IO.println s!"[install] tag={tag}: the thirty tracked fixtures are the SMOKE shape's — \
      nothing tracked to grade at this tag."
    return 0
  let tracked := (← IO.getEnv "DREGG_WM_TRACKED").getD TRACKED_SMOKE_DIR
  let doInstall := ((← IO.getEnv "DREGG_WM_INSTALL").getD "") == "1"
  let names := rungs.flatMap (fun k =>
    [s!"wrapmain_{tag}_{k.tag}.json", s!"wrapmain_{tag}_{k.tag}_unwired.json"])
  let mut drift := 0
  for n in names do
    let emitted ← IO.FS.readFile s!"{dir}/{n}"
    let path := s!"{tracked}/{n}"
    if ← System.FilePath.pathExists path then
      let s ← IO.FS.readFile path
      if s == emitted then
        IO.println s!"[install] {n}: byte-identical to the tracked fixture ({s.length} bytes)"
      else if doInstall then
        writeAtomic path emitted
        IO.println s!"[install] * {n}: INSTALLED — {s.length} tracked bytes replaced by \
          {emitted.length} emitted ones"
      else
        drift := drift + 1
        IO.println s!"[install] ⚑ {n}: THE TRACKED FIXTURE IS NOT WHAT THIS RUN EMITS \
          (tracked {s.length} bytes, emitted {emitted.length})"
    else if doInstall then
      writeAtomic path emitted
      IO.println s!"[install] * {n}: INSTALLED (was absent) — {emitted.length} bytes"
    else
      drift := drift + 1
      IO.println s!"[install] ⚑ {n}: MISSING at {path} — nothing consumes what was emitted"
  if drift != 0 && !doInstall then
    throw (IO.userError s!"⚑ THE TRACKED SMOKE FIXTURES ARE STALE: {drift} of {names.length} \
      differ from what this run emits. `pickles-wrapmain-harness` proves whatever JSON is on disk, \
      so a stale fixture is a green run about a circuit the Lean no longer describes. Re-run with \
      DREGG_WM_INSTALL=1 to install them, and carry the consequence chain: every rung's witness \
      moves, the five-polarity sweep must be re-run, and any count graded against these fixtures \
      (`the_forty_agree_at_every_slot`'s smoke conjunct among them) is about the old shape.")
  if doInstall then
    IO.println s!"[install] {names.length} tracked fixtures INSTALLED from this emission"
  else
    IO.println s!"[install] {names.length} tracked fixtures are byte-identical to this emission"
  pure drift

def emitRung (dir tag : String) (t : WrapData) (k : Rung) : IO (Nat × Nat) := do
  let t0 ← IO.monoMsNow
  let rowsW := rungRows t k true
  let rowsU := rungRows t k false
  let p := rungPub t.sh k
  let _ ← force rowsW.length s!"{k.tag} rows"
  let gs := wrapGates rowsW
  let gu := wrapGates rowsU
  let placed := placedOf t.sh k p gs
  let placedU := placedOf t.sh k p gu
  let t1 ← IO.monoMsNow
  -- ⚑ ONE witness, used for BOTH circuits. That is what makes the UNWIRED emission a CONTROL: the
  -- rows, the gate types, the coefficients and every witness cell are byte-identical, and the ONLY
  -- difference is the copy-permutation. Computing a second witness from the unwired rows would
  -- leave the probe cells empty there and the "control" would be a different circuit.
  -- ⚑ RUNG-LOCAL: `wrapWitnessAt t k` gives rung `k` the environment its OWN rows define. Asking
  -- for the closing rung's here would compute §15's ladders for every rung below `w6_xhat`.
  let wit := wrapWitnessAt t k p rowsW
  let probes := rungProbeRows t k
  let pub := if p == 0 then [] else wrapPublicAt t k
  let ds := if p == 0 then [] else wrapSlotsAt t.sh k
  let us := if p == 0 then [] else wrapInertOk t.sh k
  let jw := renderCircuit { name := s!"wrapmain_{tag}_{k.tag}", pubSize := p
                          , numRows := p + rowsW.length, gates := placed, witness := wit
                          , publicInput := some pub, slots := some (ds, us)
                          , probeRows := some probes }
  let ju := renderCircuit { name := s!"wrapmain_{tag}_{k.tag}_UNWIRED", pubSize := p
                          , numRows := p + rowsU.length, gates := placedU, witness := wit
                          , publicInput := some pub, slots := some (ds, us)
                          , probeRows := some probes }
  -- ⚠ A REFUSAL IS LOUD, AND IT LANDS BEFORE THE WRITE. `placeChecked` returning `.error` yields
  -- the empty placement, which would otherwise ship as a zero-gate circuit the harness "proves".
  -- ⚑ Both refusals used to fire AFTER `writeAtomic`, which is not fail-closed at all: the artifact
  -- the refusal is about was already on disk under its real name, and a reader of the emit
  -- directory cannot tell it from a good one.
  if placed.length != p + rowsW.length || placedU.length != p + rowsU.length then
    throw (IO.userError s!"placeChecked REFUSED at {k.tag}: {repr (refusalOf t.sh k p gs)}")
  -- ⚑ **THE SLOT MAP'S OWN OBLIGATIONS, DISCHARGED AT EVERY EMISSION.** A slot map is the artefact
  -- whose failure is silent — a duplicate, an out-of-range index or a length that has drifted from
  -- `exposedVarsAt` all place, prove and commit to a DIFFERENT statement. None of the three can
  -- reach a written file.
  if p != 0 then
    let sl := wrapSlotsAt t.sh k
    if sl.length != (exposedVarsAt t k).length then
      throw (IO.userError s!"⚑ SLOT MAP LENGTH at {k.tag}: {sl.length} slots for \
        {(exposedVarsAt t k).length} exposed variables. The zip would DROP words silently.")
    if sl.any (fun i => WRAP_PRIMARY_LEN ≤ i) then
      throw (IO.userError s!"⚑ SLOT MAP RANGE at {k.tag}: {sl} leaves Mina's own \
        PRIMARY_LEN {WRAP_PRIMARY_LEN}.")
    if sl.dedup.length != sl.length then
      throw (IO.userError s!"⚑ SLOT MAP COLLISION at {k.tag}: {sl} names one slot twice, so two \
        derived words would be tied to ONE public cell.")
    -- ⚑ …and the emission's unread set IS the rung's declaration, both directions. `wrapInertOk`
    -- alone only bounds it above; this is the equality, at the emitted shape, where the kernel pins
    -- reach only the smoke one.
    let measured := inertSlotsAt t.sh k gs
    if measured != wrapInertOk t.sh k then
      throw (IO.userError s!"⚑ THE UNREAD SET IS NOT THE DECLARATION at {k.tag}: the gates leave \
        {measured} unread, the rung declares {wrapInertOk t.sh k}. A slot in the first and not the \
        second is a public fixture; one in the second and not the first is a slot this rung derives \
        and does not admit to. Refusing rather than emitting it.")
  -- ⚑ **THE §17b CAPS' OBLIGATION, DISCHARGED AT EVERY EMISSION.** `baseWh`, `baseFin` and
  -- `baseComb` are stacked on shape-determined CAPS rather than on the regions' actual sizes,
  -- because W-FINALIZE's size is `finStride`/`finSpSize` — computed by RUNNING the program builder,
  -- which no kernel reduction of `combSlot` can afford. A cap is only honest if an emission that
  -- exceeds it STOPS, and this is where. `regionEscape` reads the emitted GATES, so it is an
  -- independent source against the caps' arithmetic, and it checks both ends: a rung reaching DOWN
  -- into the block below is the aliasing the layout exists to refuse.
  match regionEscape t.sh t.sp k gs with
  | some i =>
    throw (IO.userError s!"⚑ REGION CAP ESCAPED at {k.tag}: a gate references external {i}, which \
      is neither below the three blocks ({baseWh t.sh t.sp}) nor inside ANY block {k.tag} declares \
      ({repr (rungRegions t.sh t.sp k)}, as (base, cap) pairs). Two sub-circuits' variable regions \
      would alias — `placeChecked` would see one variable where two were meant and merge two σ \
      classes that were never meant to meet. Refusing rather than emitting it; see §17b.")
  | none => pure ()
  writeAtomic s!"{dir}/wrapmain_{tag}_{k.tag}.json" jw
  writeAtomic s!"{dir}/wrapmain_{tag}_{k.tag}_unwired.json" ju
  let t2 ← IO.monoMsNow
  IO.println s!"  {k.tag}: {rowsW.length} rows, pub {p} \
    (derived {(wrapSlotsAt t.sh k).length} at slots {wrapSlotsAt t.sh k}; \
     unread {(wrapInertOk t.sh k).length}), {probes.length} probes  \
    (place {t1 - t0} ms, witness+render {t2 - t1} ms)"
  pure (rowsW.length, probes.length)

/-- An eight-field comma spec:
`maxPrevs,ipaRounds,wComms,tComms,emsRows,branches,pubWords,xhatTerms`. ⚠ The first field is
`Max_proofs_verified`, NOT `actual_proofs_verified` — see `WrapShape.maxPrevs`.

⚑ **`xhatXY` IS DERIVED HERE, NOT PARSED**, and that is the only honest option: the pair is two
Fq coordinates and a comma spec of naturals has no independent source for them. So a
`DREGG_WM`-supplied shape gets `xhatOutOf` its own selection by construction and `main`'s memo
refusal cannot fire on this path — it is live for the COMMITTED shapes, which are the shapes anything
actually emits, and where the pair is written down and could disagree.

⚠ ⚑ **THE EIGHTH FIELD IS STILL A COUNT, AND IT STILL MEANS MINA'S ENTRY SPACE.** `WrapShape` now
carries the SELECTION, and a comma spec of naturals cannot carry `XHAT_OWN_SEL`; so this path builds
`xhatSel h` and nothing else. A shape verifying dregg's own step proof is not reachable through
`DREGG_WM` and is not meant to be — it is `KimchiStepWrapChain.shapeChain`, which names its entries.
Saying the spec covered both would be describing a branch that cannot be taken. -/
def parseShape (spec : String) : Option WrapShape :=
  match (spec.splitOn ",").map String.toNat? with
  | [some a, some b, some c, some d, some e, some f, some g, some h] =>
      some { maxPrevs := a, ipaRounds := b, wComms := c, tComms := d, emsRows := e
           , branches := f, pubWords := g, xhatEntries := xhatSel h
           , xhatXY := xhatOutOf (xhatSel h) }
  | _ => none

def main : IO Unit := do
  -- ⚑ **`DREGG_WM_OUT` LETS A LANE OWN ITS OWN DIRECTORY**, exactly as `DREGG_SM_OUT` does on the
  -- step side. This was a HARDCODED path until 2026-08-03, and the omission was not cosmetic: a
  -- before/after byte-diff of the emitted circuit was written as
  --     DREGG_SM=wrap DREGG_SM_OUT=/tmp/emit-before-wrap  lean --run …EmitWrapMainJson.lean
  -- which is wrong TWICE over — this driver reads `DREGG_WM`, not `DREGG_SM`, so the shape selector
  -- was ignored; and it had no output override at all, so BOTH revisions wrote to this one path and
  -- the `diff` compared a directory against itself. ⚠ That is a gate that cannot go red.
  let dir := (← IO.getEnv "DREGG_WM_OUT").getD "/tmp/pickles-wrapmain"
  IO.FS.createDirAll dir
  let sm ← IO.getEnv "DREGG_WM"
  let (tag, s) : String × WrapShape :=
    match sm with
    | none => ("wrap", shapeWrap)
    | some "wrap" => ("wrap", shapeWrap)
    | some "smoke" => ("smoke", shapeSmoke)
    | some spec =>
      match parseShape spec with
      | some sh => ("custom", sh)
      | none => ("wrap", shapeWrap)
  -- ⚑ FAIL-CLOSED SHAPE GUARDS. A shape whose schedule cannot carry its own census would emit a
  -- circuit that is not the one the header describes.
  if s.pubWords > WRAP_PRIMARY_LEN then
    throw (IO.userError s!"pubWords {s.pubWords} exceeds Mina's own PRIMARY_LEN {WRAP_PRIMARY_LEN}")
  if s.emsRows == 0 || s.branches == 0 then
    throw (IO.userError "degenerate shape: emsRows/branches must be positive")
  -- ⚑ A shape whose x_hat MSM has no `Add_with_correction` entry has no correction reduce and no
  -- `~init`, so the fold would start from a variable nothing defines. Refuse rather than emit it.
  if (xhLadders s).isEmpty then
    throw (IO.userError s!"degenerate shape: xhatEntries {s.xhatEntries} selects no ladder entry")
  -- ⚑ **THE SELECTION'S OWN OBLIGATIONS.** An index past the entry space reads a `getD` default —
  -- `(0,0)`, kimchi's flattening of infinity, off `y² = x³ + 5` — as a BASE, and a repeated index
  -- gives one entry two ladders over one variable block. Both place, both prove nothing.
  if s.xhatEntries.any (fun i => i ≥ XHAT_TERMS_FULL) then
    throw (IO.userError s!"⚑ xhatEntries LEAVES THE ENTRY SPACE: {s.xhatEntries} names an index \
      ≥ {XHAT_TERMS_FULL}, `wrap_verifier.ml:542-548`'s own expansion of the packed \
      `Types.Step.Statement`. Its base would be the `getD` default.")
  if s.xhatEntries.dedup.length != s.xhatEntries.length then
    throw (IO.userError s!"⚑ xhatEntries NAMES AN ENTRY TWICE: {s.xhatEntries}.")
  -- ⚑ …and the step proof it is about publishes exactly that many words. Until 2026-08-06 there
  -- were TWO entry spaces here — Mina's 67 and a disjoint twelve for a step rule that published
  -- unconstrained `Fp` elements — and this guard refused a selection that straddled them. There is
  -- one space now, so the straddle check is replaced by the fact that made it unnecessary.
  if Dregg2.Circuit.Emit.KimchiStepWrapChainFixture.STEP_PUBLIC != XHAT_TERMS_FULL then
    throw (IO.userError s!"⚑ THE STEP PROOF DOES NOT PUBLISH A PACKED STATEMENT: \
      STEP_PUBLIC is {Dregg2.Circuit.Emit.KimchiStepWrapChainFixture.STEP_PUBLIC} against \
      {XHAT_TERMS_FULL} entries. `xhatScalar` would read `getD` defaults into the MSM.")
  -- ⚑ **THE MEMO'S OBLIGATION, DISCHARGED AT EVERY EMISSION.** `WrapShape.xhatXY` carries the pair
  -- `wrap_verifier.ml:617` absorbs so that a dozen kernel theorems do not each re-reduce the MSM.
  -- That is only sound if the pair IS the MSM's output, and this is where any shape — committed or
  -- `DREGG_WM`-supplied — is refused when it is not. The smoke shape's copy is additionally closed
  -- by `rfl` in the kernel (`xhat_smoke_shape_absorbs_the_msm_output`); this covers the wrap shape,
  -- which is 1805 five-bit chunks and out of the kernel's reach without `native_decide`.
  if s.xhatXY != xhatOutOf s.xhatEntries then
    throw (IO.userError s!"⚑ xhatXY IS NOT THE MSM'S OUTPUT: shape carries {s.xhatXY} but \
      `xhatOutOf {s.xhatEntries}` is {xhatOutOf s.xhatEntries}. The transcript would absorb a value \
      no row computes — refusing rather than emitting it.")
  -- ⚑ **THE §15c‴ MEMO'S OBLIGATION, DISCHARGED AT EVERY EMISSION.** `FIN_DEFERRED_CIP/_B/_XI`
  -- are the three deferred words the finalizing block carries, and `xhatScalar` reads them, so a
  -- wrong triple would put a scalar into the x_hat MSM that no row of W-FINSPONGE computes and make
  -- `Boolean.Assert.any [finalized; not should_finalize]` unsatisfiable in the rung that emits it.
  -- ⚑ `fin_deferred_words_are_the_derivation` (`…Pins12`) closes this at the SMOKE shape by
  -- `native_decide`; ⚠ it is not, and was never, a kernel `rfl` at both shapes, whatever this
  -- comment said until 2026-08-05 — for a day the theorem it cited did not exist at all and THIS
  -- refusal was the only discharge there was. It still is the only one at the WRAP shape and at any
  -- `DREGG_WM`-supplied one, which is why it is here and not a comment, and it costs one evaluation
  -- of a program the emission runs anyway.
  let fd := finSpDerivedWords (mkWrap s)
  if (FIN_DEFERRED_CIP, FIN_DEFERRED_B, FIN_DEFERRED_XI) != fd then
    throw (IO.userError s!"⚑ FIN_DEFERRED_* IS NOT THE DERIVATION: the memo carries \
      {(FIN_DEFERRED_CIP, FIN_DEFERRED_B, FIN_DEFERRED_XI)} but `finSpDerivedWords` says {fd}. \
      W-FINSPONGE would emit a `Boolean.all` no witness satisfies — refusing rather than emitting \
      it. Re-run `lake env lean --run Dregg2/Circuit/Emit/EmitWrapFinDeferred.lean`.")
  -- ⚑ **THE `nKeySpVars` HOIST'S OBLIGATION, DISCHARGED AT EVERY EMISSION.** `nKeySpVars` is the
  -- closed form `KEY_SP_VARS` since 2026-08-05, because it read `(keySponge …).next` and `baseXh`
  -- — hence every base address above `w5_key` — rebuilt that 28-permutation sponge on every cell
  -- reference: 57.7 ms per `combSlot`, measured, and 33 m 52 s for `w12_close`. The general `rfl`
  -- does not elaborate (`whnf` forces the lanes; still running at 400M heartbeats), and the kernel
  -- pins in §14b reach only the SMOKE shape. This is the leg that covers `shapeWrap` and any
  -- `DREGG_WM`-supplied shape: run the trajectory ONCE — 19 ms against an emission measured in
  -- minutes — and REFUSE when the closed form is not what the sponge allocates. A hoist whose
  -- equality is checked nowhere at the shape being emitted is a rewrite nobody can audit.
  let t := mkWrap s
  let spAlloc := (keySponge s t.sp KEY_REAL_BRANCH).next
  if nKeySpVars s t.sp != spAlloc then
    throw (IO.userError s!"⚑ nKeySpVars IS NOT THE INDEX SPONGE'S ALLOCATION: the closed form says \
      {nKeySpVars s t.sp} and `keySponge` allocates {spAlloc}. `baseXh` and every base \
      above it would name cells the key sponge also owns — two sub-circuits aliasing in a base \
      address, which is the class §17b exists to refuse. Refusing rather than emitting it.")
  IO.println s!"emitting wrap_main tag={tag} shape={repr s}"
  IO.println s!"  index sponge allocates {spAlloc} cells = nKeySpVars (the hoist, checked here)"
  IO.println s!"  items={nItems s} squeezes={nSqueezes s} chals={nChals s} \
    PRIMARY_LEN(mina)={WRAP_PRIMARY_LEN} pubWords(base)={s.pubWords}"
  IO.println s!"  public layout: MINA'S — 40 slots, base at {wrapSlots s}, \
    +12 at w9_prev, +11 at w11_wraphack; pinned {WRAP_PINNED_SLOTS}"
  IO.println s!"  ⚠ ZERO and UNREAD at {WRAP_UNPINNED_SLOTS}: slots 30-39 are what a real devnet \
    wrap proof carries; slots 0-4 and 9 are `expand_deferred`'s outputs, which W-FINALIZE derives \
    and this ladder does not"
  IO.println s!"  x_hat MSM: {xhN s} entries, {xhTotalChunks s} five-bit chunks, \
    {(xhLadders s).length} ladders, widths={(xhSel s).map xhatBits}"
  IO.println s!"  x_hat (DERIVED, absorbed at wrap_verifier.ml:617) = {xhatOutOf s.xhatEntries}"
  let _ ← force t.sp.evs.length "sponge events"
  let all := [Rung.transcript, Rung.challenges, Rung.branch, Rung.bind, Rung.key, Rung.xhat,
              Rung.split, Rung.ftcomm, Rung.prev, Rung.wraphack, Rung.close, Rung.finalize,
              Rung.finsponge, Rung.combine, Rung.bullet]
  -- ⚑ `DREGG_WM_RUNGS` — a comma list that RESTRICTS the emission to those rungs, the exact twin of
  -- the harness's own filter and additive in the same way: unset, the behaviour is what it was.
  -- It exists because `w12_close` and `w11_bullet` are measured in tens of minutes each, and a lane
  -- that changed ONE block's inputs should not have to pay for the other thirteen to re-prove its
  -- own — which is how a verification does not get run at all.
  -- ⚠ ⚑ **THE REFUSALS ABOVE ARE NOT UNDER THE FILTER**, and that is the whole reason this is a
  -- filter here rather than a second driver: a cheaper emitter that skipped the `xhatXY` and
  -- `FIN_DEFERRED_*` memo checks would be a way to write an artifact the real one refuses.
  let rungs ← match (← IO.getEnv "DREGG_WM_RUNGS") with
    | none => pure all
    | some f =>
        let want := (f.splitOn ",").map (fun s => s.trimAscii.copy) |>.filter (· != "")
        let sel := all.filter (fun k => want.contains k.tag)
        if sel.isEmpty then
          throw (IO.userError s!"⚑ DREGG_WM_RUNGS={f} selected NO rung out of \
            {all.map Rung.tag} — refusing to report a green emission that emitted nothing.")
        else pure sel
  for k in rungs do
    let _ ← emitRung dir tag t k
    pure ()
  IO.println s!"wrote {dir}/wrapmain_{tag}_*.json"
  -- ⚑ …and the tracked twins are graded against what was just written. This is the LAST thing the
  -- driver does, deliberately: the bytes are on disk before the refusal, so a lane doing a
  -- before/after byte-diff still gets its artifacts and the nonzero exit is the honest signal.
  let _ ← installedGate dir tag rungs
