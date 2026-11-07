/-
# Dregg2.Circuit.Emit.EmitStepMainJson — the `--run` emit driver for the `verify_one` assembly

Thin executable: writes each RUNG of the Lean-assembled `step_verifier.verify_one` circuit — and its
UNWIRED control — to `/tmp/pickles-stepmain/*.json`, which `pickles-stepmain-harness` proves +
verifies. Carries the `main` (kept OUT of `KimchiStepMain` so that module roots cleanly into
`PicklesSynthesis`).

    lake env lean --run Dregg2/Circuit/Emit/EmitStepMainJson.lean              # the committed shape
    DREGG_SM=smoke  lake env lean --run …                                      # the CI fixture shape
    DREGG_SM=A,C,E,M,I,B,D,V,P,W lake env lean --run …                         # an arbitrary shape
    DREGG_SM_RUNGS=r8_finalize lake env lean --run …                           # ONE rung
    DREGG_SM_RUNGS=all lake env lean --run …                                   # the nine (default)

⚑ **`DREGG_SM_RUNGS` is why a conformance re-grade is minutes and not a working day** (2026-08-03).
It used to matter twice over: `rungRows` bound all nine sub-lists BEFORE it matched on `k`, so every
rung evaluated the whole chain, and `emitRung` walks it twice more (wired, unwired). Nine rungs
therefore cost 9 × 2 FULL traversals, and the three gates that consume this driver
(`stepmain-shape-diff`, `curve-gate-oracle`, `stepmain-region-conformance`) grade `r8_finalize`
ALONE. Measured on the `step` shape from artifact mtimes: consecutive rungs landed 68–69 min apart
and the gap did NOT grow with the rung, though the rungs go 803 → 10 823 rows — the uniformity IS
the evidence that the work was shared and re-done.

⚑ **THAT HALF IS FIXED** (`KimchiStepMainCore.rungRows` is `rungOwn`/`rungsUpto` + a `foldl` over the
rungs at or below `k`, pinned by `rungRows_is_a_ladder`, by `rfl`), so a rung now pays only for its
own prefix and the nine-rung sweep costs about what `r9_opening` costs alone. The wired/unwired pair
is unchanged and is still the other factor of two (`DREGG_SM_WIRED_ONLY`). The full set stays the
default because §15's row-length pins want every rung.

The ten-field spec is `absorbs,chals,emsRows,msmTerms,ipaRounds,ipaBlocks,bRounds,cipEvals,tComms,
pubWords`. ⚑ `msmChunks` is GONE (2026-08-03): the MSM chunk count is per statement WORD
(`msmChunksAt`, §1b), so there is nothing shape-wide left to pass. ⚑ `tComms` is new since the R1 interleaving: `absorbs` is DERIVED from the
transcript schedule now (`absorbBlocksOf`), so sizing `t_comm` off `absorbs` would be circular.
The shape comes through the ENVIRONMENT, not `argv`: `lean --run` does not forward
trailing arguments through `lake env`, and a silently-ignored argument emitting the DEFAULT shape
under a scale-rung filename is exactly the measurement that lies.

Each rung reports its wall-clock split — chain evaluation, row scheduling, placement (`place`),
witness composition (`WitnessBuilder.compose`), render+write — because that split, not the prover,
is what governs whether the assembly reaches full `verify_one` scale.

House Law #1: the CIRCUIT is Lean-authored; `proof-systems` (the harness) is the Rust PROVER.

⚑ IMPORTS `…KimchiStepMainCore`, NOT THE UMBRELLA (2026-08-02, with the split). Every name this
driver uses — `mkStep`, `rungRows`, `stepGates`, `placedOf`, `stepWitness`, `rungProbeRows`,
`stepPublic`, `stepCircuit`, `Rung`, `shapeStep`/`shapeSmoke` — is §1–§11, i.e. Core, which
elaborates in ~11 s. The umbrella additionally pulls the thirteen PIN modules (837 `#guard`s,
~15 min of interpretation), and EMITTING a circuit does not depend on any of them. So the emit →
prove loop no longer waits on the pins. ⚠ This does NOT unroot a guard: `Dregg2.PicklesSynthesis`
(a `defaultTargets` root) imports the umbrella, so every pin module still runs in `lake build`.
-/
import Dregg2.Circuit.Emit.KimchiStepMainCore

open Dregg2.Circuit.Emit.KimchiStepMain
open Dregg2.Circuit.Emit.KimchiPlacement (PGate PlacedGate)
open Dregg2.Circuit.Emit.KimchiCircuitJson (renderCircuit)

/-- Force a `Nat` before the next clock read. `let x := e` for pure `e` is FLOATABLE — the compiler
happily sinks the work past an `IO.monoMsNow`, which is how a phase split silently reports `0 ms`
for the phase that actually ran. An `IO` action that inspects the value pins it in place. -/
def force (n : Nat) (what : String) : IO Nat := do
  if n == 0 then throw (IO.userError s!"emit: phase '{what}' produced nothing — degenerate shape")
  pure n

/-- Write ATOMICALLY: stage beside the target, then rename into place.

⚑ A reader of `/tmp/pickles-stepmain` cannot tell a fully-written artifact from one whose writer
died mid-`String` — both are a file with the right name. `rename(2)` within one directory is atomic,
so the real name only ever appears carrying complete bytes. Measured 2026-08-03: the directory held
a nine-rung `smoke` set beside a four-rung `step` set with no stamp and no way to tell which run
either came from. -/
def writeAtomic (path contents : String) : IO Unit := do
  let staged := path ++ ".partial"
  IO.FS.writeFile staged contents
  IO.FS.rename staged path

/-- The tracked step fixtures' directory, relative to `metatheory/` — the cwd every documented
invocation of this driver uses. -/
def TRACKED_STEP_DIR : String := "fixtures/pickles-stepmain-harness/fixtures"

/-- ⚑ **THE TRACKED `(tag, rung)` PAIRS, DECLARED RATHER THAN DISCOVERED.** Five, each with its
`_unwired` twin — ten files. Unlike the wrap side (where all fifteen rungs are tracked), the step
harness carries a SELECTION, so the gate cannot infer "tracked" from "emitted": a rung this run
emitted that is absent here is not drift, and a rung that IS here and was emitted must match. Listing
them makes "which artifacts does this repo actually consume" answerable without a `ls`, and makes a
tracked file that has quietly disappeared a RED instead of a silently smaller grade. -/
def TRACKED : List (String × String) :=
  [ ("smoke", "r1_transcript"), ("smoke", "r6_ft_eval0"), ("smoke", "r7_absorption")
  , ("smoke", "r8_finalize"),   ("step",  "r8_finalize") ]

/-- ⚑⚑ **"INSTALL WHAT YOU EMIT", AS A RED INSTEAD OF AS A COMMENT** — the STEP side's twin of
`EmitWrapMainJson.installedGate` and of `pickles_kimchi_marshal::installed_gate`, and it exists
because this route had **no refusal at all**.

`scripts/check-emitter-routing.sh:176` said so in as many words: the tracked
`stepmain_step_r8_finalize.json` is *"copied in BY HAND (no route to grade)"*, guarded only by
`pickles_kimchi_marshal`'s name/width refusal — which checks that the file is A step circuit of the
right arity, never that it is THIS assembly's. A stale step fixture is a perfectly provable circuit;
it is just not the one the Lean says, and every downstream number (the step proof,
`KimchiStepWrapChainFixture`, `WRAP_PUBLIC_INPUT_MEASURED`, slot 12 of the forty) is then about a
circuit that no longer exists in the tree.

**The gate is here rather than in a script for the reason the other two are inside their emitters:
it fires in the same process that produced the bytes, so re-emitting and not installing is the one
thing it cannot miss.**

`DREGG_SM_INSTALL=1` performs the copy instead of refusing. There is deliberately no switch that
disables the comparison, and a tracked file that is missing or unreadable counts as drift.

⚠ **A `DREGG_SM_WIRED_ONLY=1` RUN MAY NOT INSTALL.** It did not emit the `_unwired` twins, so
installing would leave a fresh wired artifact beside a stale control — the mixed-run directory
`emitRung` already refuses to create in `$DREGG_SM_OUT`, recreated in the tracked tree where it
would be worse. The tamper control is what makes "the tamper is REJECTED here and ACCEPTED on the
unwired twin" a real claim.

Returns the number of tracked files that differ. -/
def installedGate (dir tag : String) (rungs : List Rung) (wiredOnly : Bool) : IO Nat := do
  let tracked := (← IO.getEnv "DREGG_SM_TRACKED").getD TRACKED_STEP_DIR
  let doInstall := ((← IO.getEnv "DREGG_SM_INSTALL").getD "") == "1"
  if doInstall && wiredOnly then
    throw (IO.userError "⚑ DREGG_SM_INSTALL=1 with DREGG_SM_WIRED_ONLY=1: this run did not emit \
the `_unwired` controls, so installing would leave fresh wired artifacts beside stale ones. \
Re-run without DREGG_SM_WIRED_ONLY.")
  let names := (rungs.filter (fun k => TRACKED.contains (tag, k.tag))).flatMap (fun k =>
    if wiredOnly then [s!"stepmain_{tag}_{k.tag}.json"]
    else [s!"stepmain_{tag}_{k.tag}.json", s!"stepmain_{tag}_{k.tag}_unwired.json"])
  if names.isEmpty then
    IO.println s!"[install] tag={tag}: this run emitted no TRACKED (tag, rung) pair — \
nothing to grade. Tracked: {TRACKED.map (fun p => s!"{p.1}/{p.2}")}"
    return 0
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
    throw (IO.userError s!"⚑ THE TRACKED STEP FIXTURES ARE STALE: {drift} of {names.length} \
differ from what this run emits. `pickles-stepmain-harness` and the three conformance gates prove \
whatever JSON is on disk, and `pickles_kimchi_marshal` proves the STEP PROOF over it, so a stale \
fixture is a green run about a circuit the Lean no longer describes. Re-run with \
DREGG_SM_INSTALL=1 to install, and carry the consequence chain: the step proof re-proves, \
`KimchiStepWrapChainFixture` and `KimchiStepWrapChainKey` re-install, \
`MinaWrapDeferredWords.WRAP_PUBLIC_INPUT_MEASURED` re-bakes, and every count graded against it \
(`the_forty_agree_at_every_slot` among them) is about the old shape until re-measured.")
  if doInstall then
    IO.println s!"[install] {names.length} tracked fixtures INSTALLED from this emission"
  else
    IO.println s!"[install] {names.length} tracked fixtures are byte-identical to this emission"
  pure drift

/-- The tracked name of the step assembly's OWN sixteen bulletproof prechallenges. -/
def OWN_PRECHAL_NAME : String := "stepmain_step_own_prechallenges.json"

/-- ⚑⚑ **THE ASSEMBLY'S OWN SIXTEEN, EMITTED SO THE WIRE CAN CARRY THEM — cells 60–75 of slot 12.**

`messages_for_next_step_proof.old_bulletproof_challenges` is `Vec<[Fp; 16]>` and is **never a
published statement word**: `MessagesForNextStepProof::to_fields` puts it in a Poseidon PREIMAGE and
only the digest reaches the forty (`prepared_statement.rs:123`). So there is nothing for the
marshaller to read out of the sixty-seven, and until now `prove_step` CHOSE the vector — a
`k·0x9E3779B97F4A7C15 | 1` ladder — while segment D absorbed `liftOf … (uChal k)`. Two vectors where
`step_verifier.ml:1114-1147` has one, and every per-slot instrument agreed with itself.

This file is the extraction. `raw` is `chalOf s d (uChal k)`, the 128-bit prechallenge the transcript
squeezes; `lift` is `liftOf s d (uChal k)`, its `to_field_checked` image, which IS segment D's
preimage cells 60–75. The marshaller reads `raw` into `step_pre`, endo-expands it with **Vesta's**
`endo_r` (`marshal::expand_step_prechallenge`) and REFUSES unless the result is `lift` — so the two
implementations of one lift are compared on every run instead of assumed equal.

⚠ **`raw` is emitted as well as `lift` because the wire carries the PRECHALLENGE, not its image.**
A `[u64; 2]` is what `PicklesBulletproofChallengeStableV1` holds; publishing the lift would hand Mina
a vector whose endo-expansion is a second lift of an already-lifted value.

⚑ **THIS DOES NOT DEPEND ON `G`, WHICH IS WHY THE FLAG DAY TERMINATES IN ONE PASS.** `chalOf` reads
the pass-2 transcript, whose only free input is `mkStepWith`'s `cipV` — computed in PASS 1 from
`sp0`/`ft0`/`defc0` and from nothing in `runBp`. So the sixteen are settled before `gXY` exists, the
accumulator over them is a constant, and segment D absorbing that constant cannot move them back. -/
def ownPrechallengesJson (t : StepData) : String :=
  let s := t.sh
  let d := t.sp
  let raw := (List.range s.bRounds).map (fun k => chalOf s d (s.uChal k))
  let lift := (List.range s.bRounds).map (fun k => liftOf s d (s.uChal k))
  let arr (xs : List Nat) : String :=
    "[" ++ String.intercalate ", " (xs.map (fun v => s!"\"{v}\"")) ++ "]"
  "{\n" ++
  s!"  \"shape\": \"step\",\n" ++
  s!"  \"b_rounds\": {s.bRounds},\n" ++
  s!"  \"chal_bits\": {s.chalBits},\n" ++
  s!"  \"raw\": {arr raw},\n" ++
  s!"  \"lift\": {arr lift}\n" ++
  "}\n"

/-- The install gate for [`ownPrechallengesJson`], the same shape as `installedGate`: emit into
`$DREGG_SM_OUT`, compare against the tracked copy, and REFUSE rather than let the marshaller prove a
step proof whose recursion challenges are not this assembly's. Returns 1 on drift. -/
def ownPrechallengesGate (dir : String) (t : StepData) : IO Nat := do
  let tracked := (← IO.getEnv "DREGG_SM_TRACKED").getD TRACKED_STEP_DIR
  let doInstall := ((← IO.getEnv "DREGG_SM_INSTALL").getD "") == "1"
  let emitted := ownPrechallengesJson t
  writeAtomic s!"{dir}/{OWN_PRECHAL_NAME}" emitted
  let path := s!"{tracked}/{OWN_PRECHAL_NAME}"
  if ← System.FilePath.pathExists path then
    let s ← IO.FS.readFile path
    if s == emitted then
      IO.println s!"[install] {OWN_PRECHAL_NAME}: byte-identical to the tracked vector"
      return 0
    if doInstall then
      writeAtomic path emitted
      IO.println s!"[install] * {OWN_PRECHAL_NAME}: INSTALLED — the sixteen MOVED, so \
`pickles_kimchi_marshal` must re-prove and the accumulator over them re-install"
      return 0
    IO.println s!"[install] ⚑ {OWN_PRECHAL_NAME}: THE TRACKED SIXTEEN ARE NOT THIS ASSEMBLY'S"
    return 1
  if doInstall then
    writeAtomic path emitted
    IO.println s!"[install] * {OWN_PRECHAL_NAME}: INSTALLED (was absent)"
    return 0
  IO.println s!"[install] ⚑ {OWN_PRECHAL_NAME}: MISSING at {path}"
  return 1

/-- The nine rungs in schedule order. ⚑ This is the FULL-SET path and it stays the DEFAULT: §15's
row-length pins and the shape-diff sweeps legitimately want every rung. -/
def allRungs : List Rung :=
  [Rung.transcript, Rung.challenges, Rung.msm, Rung.ipa, Rung.full,
   Rung.ftEval0, Rung.absorb, Rung.finalize, Rung.opening]

/-- A selector name matches a rung by its full tag (`r8_finalize`) or its index alone (`r8`). -/
def rungMatches (n : String) (k : Rung) : Bool :=
  k.tag == n || (k.tag.splitOn "_").headD "" == n

/-- Resolve a `DREGG_SM_RUNGS` selector. ⚑ FAILS CLOSED on a name that is not a rung: a selector
silently falling back to all nine is the same lie the shape docblock above names — the run would
cost ten hours while reporting that it honoured a one-rung request. -/
def parseRungs (spec : String) : Except String (List Rung) := do
  let names := ((spec.splitOn ",").map (fun s => s.trimAscii.copy)).filter (· != "")
  if names.isEmpty then throw s!"DREGG_SM_RUNGS={spec} names no rung"
  names.foldlM (fun acc n =>
    match allRungs.find? (rungMatches n) with
    | some k => pure (acc ++ [k])
    | none => throw s!"DREGG_SM_RUNGS: '{n}' is not a rung — expected one of \
{String.intercalate ", " (allRungs.map Rung.tag)} (or its 'rN' prefix)") []

/-- Emit one rung (wired + unwired), with the phase split. Returns `(rows, probes)`. -/
def emitRung (dir tag : String) (t : StepData) (k : Rung) (wiredOnly : Bool := false) :
    IO (Nat × Nat) := do
  let s := t.sh
  let p := rungPub s k
  let t0 ← IO.monoMsNow
  let rows := rungRows t k true
  -- ⚑ The UNWIRED control is a SECOND full `rungRows` traversal plus a second `placedOf`, i.e.
  -- roughly half this rung's cost. It is the tamper control the `pickles-stepmain-harness` proves
  -- against — and NONE of the three conformance gates reads it: `stepmain-shape-diff`,
  -- `curve-gate-oracle` and `stepmain-region-conformance` all load `stepmain_step_r8_finalize.json`
  -- and never open `_unwired.json`. So a grade pays for it and throws it away.
  -- ⚠ Default stays FALSE. The control is what makes "the tamper is REJECTED here and ACCEPTED on
  -- the unwired twin" a real claim, and a flag that quietly stopped emitting it would hollow out
  -- the harness's whole falsification story. Opt in when you are grading, not when you are proving.
  let rowsU := if wiredOnly then [] else rungRows t k false
  let n := rows.length
  let _ ← force (n + rowsU.length + (if wiredOnly then 1 else 0)) "rows"
  let t1 ← IO.monoMsNow
  let placed := placedOf p (stepGates rows)
  let placedU := if wiredOnly then [] else placedOf p (stepGates rowsU)
  let nw ← force ((placed.map (fun g => g.wires.length)).foldl (· + ·) 0
                  + (placedU.map (fun g => g.wires.length)).foldl (· + ·) 0) "place"
  let t2 ← IO.monoMsNow
  let w := stepWitness t p rows
  let ncell ← force ((w.map (·.length)).foldl (· + ·) 0) "compose"
  let t3 ← IO.monoMsNow
  -- ⚑ NOT `rungProbeRows t k`. That recomputes `rungRows t k true` from scratch — a THIRD full
  -- traversal of the rung's own families per rung, on top of the wired/unwired pair. (It used to be
  -- worse: `rungRows` evaluated all fifteen families on every call before matching on `k`.) This is
  -- `rungProbeRows`' body verbatim over the `rows` already in hand (same `p`, same list).
  let probes := ((rows.zip (List.range rows.length)).filter (fun ri => ri.1.probe)).map
                  (fun ri => p + ri.2)
  let pub := if p == 0 then [] else stepPublic t
  let js := renderCircuit { name := s!"stepmain_{tag}_{k.tag}", pubSize := p, numRows := p + n
                          , gates := placed, witness := w
                          , publicInput := some pub, probeRows := some probes }
  writeAtomic s!"{dir}/stepmain_{tag}_{k.tag}.json" js
  unless wiredOnly do
    let jsU := renderCircuit { name := s!"stepmain_{tag}_{k.tag}_UNWIRED", pubSize := p
                             , numRows := p + n, gates := placedU, witness := w
                             , publicInput := some pub, probeRows := some probes }
    writeAtomic s!"{dir}/stepmain_{tag}_{k.tag}_unwired.json" jsU
  -- ⚠ And REMOVE a stale control rather than leave one from an older run beside a fresh wired
  -- artifact. A `_unwired.json` that no longer corresponds to the `.json` next to it is exactly the
  -- mixed-run directory this pass is closing.
  if wiredOnly then
    let up := s!"{dir}/stepmain_{tag}_{k.tag}_unwired.json"
    if ← System.FilePath.pathExists up then IO.FS.removeFile up
  let t4 ← IO.monoMsNow
  -- A refusal must be LOUD: `placedOf` returns `[]` on refusal, and an empty gate list would
  -- otherwise be written out as a "circuit" the harness rejects for the wrong reason.
  if placed.length != p + n then
    throw (IO.userError s!"{k.tag}: placeChecked REFUSED — {repr (refusalOf p (stepGates rows))}")
  IO.println s!"[{tag}/{k.tag}] rows={p + n} (pub={p}) probes={probes.length} \
cells={ncell} wires={nw}"
  IO.println s!"    rows {t1 - t0} ms | place {t2 - t1} ms | compose {t3 - t2} ms | \
render+write {t4 - t3} ms | TOTAL {t4 - t0} ms"
  pure (p + n, probes.length)

def parseShape (spec : String) : Option StepShape :=
  match spec.splitOn "," with
  | [a, c, e, m, i, b, d, ce, tc, pw] =>
      some { absorbs := a.toNat!, chals := c.toNat!, emsRows := e.toNat!
           , msmTerms := m.toNat!
           , ipaRounds := i.toNat!, ipaBlocks := b.toNat!
           , bRounds := d.toNat!, cipEvals := ce.toNat!, tComms := tc.toNat!
           , pubWords := pw.toNat! }
  | _ => none

def main : IO Unit := do
  -- ⚑ SETTABLE OUTPUT DIR — the shared `/tmp/pickles-stepmain` made concurrent lanes collide BY
  -- CONSTRUCTION. Two lanes emitting the `step` shape write byte-different `stepmain_step_r8_*.json`
  -- to the same path, and whichever finishes last silently wins; the loser's stamp then vouches for
  -- bytes that are no longer there. Measured 2026-08-03 on hbox: that directory held r5–r9 from a
  -- run at 11:58–12:00 beside r1–r4 from a *different* run at 13:06–16:19, and nothing in the
  -- directory recorded that they came from two runs. `DREGG_SM_OUT` lets a lane own its own dir.
  let dir := (← IO.getEnv "DREGG_SM_OUT").getD "/tmp/pickles-stepmain"
  IO.FS.createDirAll dir
  let spec ← IO.getEnv "DREGG_SM"
  let (tag, sh) :=
    match spec with
    | none => ("step", shapeStep)
    | some "smoke" => ("smoke", shapeSmoke)
    | some "step" => ("step", shapeStep)
    | some str => match parseShape str with
                  | some s => (str.replace "," "_", s)
                  -- ⚑ FAIL CLOSED. Falling back to `shapeStep` here would emit the DEFAULT shape
                  -- under a filename nobody asked for, which is the measurement that lies.
                  | none => panic! s!"emit: DREGG_SM={str} is neither 'step', 'smoke', nor a \
ten-field spec 'absorbs,chals,emsRows,msmTerms,ipaRounds,ipaBlocks,bRounds,cipEvals,tComms,pubWords'"
  -- ⚑ THE RUNG SELECTOR. Default = all nine, unchanged. `DREGG_SM_RUNGS=r8_finalize` emits ONLY
  -- what the caller asked for. Measured 2026-08-03 on the `step` shape BEFORE the fix: consecutive
  -- rung artifacts landed 68–69 min apart and the gap did NOT grow with the rung, because
  -- `rungRows` evaluated all fifteen row families before it matched on `k`. It now walks only the
  -- rungs at or below `k`, so the gap should track the rung's own size; the three conformance gates
  -- grade `r8_finalize` alone either way, so the selector stays.
  -- ⚑ `DREGG_SM_WIRED_ONLY=1` drops the unwired control — see `emitRung`. Roughly halves a rung.
  let wiredOnly := ((← IO.getEnv "DREGG_SM_WIRED_ONLY").getD "0") != "0"
  let rungs ← match ← IO.getEnv "DREGG_SM_RUNGS" with
    | none | some "all" => pure allRungs
    | some sel => match parseRungs sel with
                  | .ok ks => pure ks
                  | .error e => throw (IO.userError s!"emit: {e}")
  -- ⚑ FAIL CLOSED on a shape too small for `Common.ft_comm`. `tCommN` is `min 7 tComms`, and the
  -- Horner needs at least two chunks (`common.ml:247-253` seeds at `t_comm.(n-1)` and folds down);
  -- at `tCommN < 2` the add chain would index past its own list and emit a `(0,0)` "point".
  -- The two committed shapes are 7 and 3; an arbitrary `DREGG_SM` spec must not silently degrade.
  if tCommN sh < 2 then
    throw (IO.userError s!"emit: tCommN = {tCommN sh} — the shape carries fewer than two `t_comm` \
quotient chunks (tComms={sh.tComms}); `Common.ft_comm`'s Horner needs at least two")
  -- ⚑ FAIL CLOSED on a shape whose `absorbs` is not the SCHEDULE's own block count, and on one with
  -- too few `chals` to hold upstream's scheduled squeezes. Both are silent-degradation doors: the
  -- first would leave absorb blocks the sponge never feeds, the second would drop a squeeze.
  if sh.absorbs != absorbBlocksOf sh then
    throw (IO.userError s!"emit: absorbs={sh.absorbs} but the transcript schedule has \
{absorbBlocksOf sh} absorb blocks (§2b)")
  if sh.chals < sqScheduled sh then
    throw (IO.userError s!"emit: chals={sh.chals} < {sqScheduled sh} scheduled transcript \
squeezes (β γ α ζ u, one per bullet_reduce round, c)")
  IO.println s!"== step_main assembly: absorbs={sh.absorbs} chals={sh.chals} ems={sh.emsRows} \
msm={sh.msmTerms} terms / {msmChunkPrefix sh.msmTerms} chunks ipa={sh.ipaRounds}x{sh.ipaBlocks} \
b={sh.bRounds} pub={sh.pubWords} =="
  let tc0 ← IO.monoMsNow
  let t := mkStep sh
  -- ⚑ `t.ftc.terms` is in the force since `Common.ft_comm`'s MSM landed: it is eight 255-bit
  -- `scale_fast2` ladders and by far the largest single item in the chain phase, so leaving it out
  -- would report its cost under "rows".
  let _ ← force (t.sp.states.length + t.msm.terms.length + t.ipa.accs.length
                 + t.ft.fp.prog.size + t.segB.states.length + t.ftc.terms.length) "chains"
  let tc1 ← IO.monoMsNow
  IO.println s!"    chain evaluation (sponge + vbm + endo + deferred): {tc1 - tc0} ms"
  for k in rungs do
    let _ ← emitRung dir tag t k wiredOnly
    pure ()
  -- ⚑ THE ROUTE, GRADED IN THE PROCESS THAT PRODUCED THE BYTES. See `installedGate`.
  let _ ← installedGate dir tag rungs wiredOnly
  -- ⚑⚑ …and the assembly's OWN sixteen beside them, for the `step` shape only — the smoke shape is
  -- a different, smaller circuit and its transcript is not what the marshaller proves over.
  -- ⚠ This rides EVERY `step` emission regardless of which rungs ran: the sixteen are a fact about
  -- `mkStep`, not about a rung, and a run that emitted only `r1_transcript` has still settled them.
  if tag == "step" then
    let d ← ownPrechallengesGate dir t
    if d != 0 then
      throw (IO.userError s!"⚑ THE TRACKED {OWN_PRECHAL_NAME} IS STALE. \
`pickles_kimchi_marshal` reads it into `prove_step`'s `step_pre`, so a stale vector makes the wire \
record's `old_bulletproof_challenges` a vector this assembly never squeezed — cells 60–75 of slot \
12. Re-run with DREGG_SM_INSTALL=1, then re-install the accumulator over them \
(`MinaStepOwnAccumulator`) and re-prove.")
  pure ()
