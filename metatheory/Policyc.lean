/-
# Policyc — `lake exe policyc`: the policy language's compiler, extracted from Lean.

    policyc check   <file>                          parse + resolve names; located errors; exit 0/1
    policyc fmt     <file>                          the canonical print (`Policy.print`)
    policyc compile <file> --pattern NAME [--absence]
                                                    the determinized 256-column byte table, JSON
    POLICYC_PROFILE=1 policyc compile ...            phase counts and clocks on stderr
    policyc rules   <file>                          the rules as a stratified program, JSON

Every function this calls is the Lean definition the theorems are about: `parse`
(`parse_print_roundtrip`), `elabRe`/`absenceOf` (`elabRe_semantics`, `absenceOf_semantics`),
`certifySurface` (`Certified.hdec`, from `compiled_decides` through the checked minimization) and, for
`--absence`, `certifySurfaceAbsence` (`Factor.absence_decides`, the checked factor construction over the
whole-word table), `elabProgram`/`strataOf`
(stratification re-checked by `StratifiedCert.stratifiedB` before printing). JSON rendering and
argument handling are the untheorem'd shell.

`compile` JSON (lane D consumes this):

    {"pattern": NAME, "absence": BOOL, "states": N, "alphabet": 256,
     "delta": [[q(s,0), …, q(s,255)] for s < N], "start": S, "accept": [s, …],
     "num_states": N, "transitions": [delta flattened row-major], "accepting": [s, …]}

The last three fields repeat the table in the `dfa` crate's flat layout (`transitions[s*256+b]`),
which `lake exe dfa-run` reads. The table is the derivative automaton, minimized (Moore
refinement) and with a non-accepting sink, when one exists, relabelled to 0; each step is kept
only after `Compile.simCheck` verifies the simulation, so `Certified.hdec` (from
`compiled_decides` through `simCheck_verdict`) is the correctness of exactly the printed table.

`rules` JSON (the shape `lake exe datalog-check` reads for `statement.program`/`strata`):

    {"program": [{"head": ATOM, "body": [{"pos": ATOM} | {"neg": ATOM}, …]}, …],
     "strata": [[rule index, …], …] | null, "stratified": BOOL, "positive": BOOL,
     "predNames": [name, …]}        ATOM = {"pred": n, "args": [{"var": i} | {"const": z}, …]}
-/
import Dregg2.Policy.Theorems
import Dregg2.Policy.Compositional

open Lean (Json)
open Dregg2.Policy

namespace Policyc

def jsonNats (xs : List Nat) : Json := Json.arr (xs.map (fun n => (n : Json))).toArray

def atomJson (a : Dregg2.Datalog.FixpointCert.Atom) : Json :=
  Json.mkObj [("pred", (a.pred : Json)), ("args", Json.arr (a.args.map (fun t => match t with
    | .var i => Json.mkObj [("var", (i : Json))]
    | .const z => Json.mkObj [("const", Lean.toJson z)])).toArray)]

def litJson : Dregg2.Datalog.StratifiedCert.Lit → Json
  | .pos a => Json.mkObj [("pos", atomJson a)]
  | .neg a => Json.mkObj [("neg", atomJson a)]

def readPolicy (path : String) : IO (Except String Policy) := do
  let src ← IO.FS.readFile path
  match parse src with
  | .ok p => pure (.ok p)
  | .error e => pure (.error s!"{path}:{e.pos.line}:{e.pos.col}: found {e.found}, expected one of: {", ".intercalate e.expected}")

def rulesOf (p : Policy) : List Rule := p.decls.filterMap (fun d => match d with | .rule r => some r | _ => none)

def check (path : String) : IO UInt32 := do
  match ← readPolicy path with
  | .error msg => IO.eprintln msg; pure 1
  | .ok p =>
    let mut bad := false
    for d in p.decls do
      if let .policy n cs := d then
        match elabClaims p cs with
        | .ok _ => pure ()
        | .error e => IO.eprintln s!"{path}: policy `{n}`: {e}"; bad := true
    let rs := rulesOf p
    let (P, ps) := elabProgram rs
    if rs.any (fun r => r.body.any (·.neg)) && (strataOf P ps.length).isNone then
      IO.eprintln s!"{path}: the rules are not stratifiable (a cycle through negation)"; bad := true
    let count (f : Decl → Bool) := (p.decls.filter f).length
    IO.println s!"{path}: {p.decls.length} declarations ({count (fun d => match d with | .pattern .. => true | _ => false)} patterns, {count (fun d => match d with | .grammar .. => true | _ => false)} grammars, {rs.length} rules, {count (fun d => match d with | .budget .. => true | _ => false)} budgets, {count (fun d => match d with | .policy .. => true | _ => false)} policies)"
    pure (if bad then 1 else 0)

def fmt (path : String) : IO UInt32 := do
  match ← readPolicy path with
  | .error msg => IO.eprintln msg; pure 1
  | .ok p => IO.print (print p); pure 0

def compileCmd (path name : String) (absence : Bool) : IO UInt32 := do
  match ← readPolicy path with
  | .error msg => IO.eprintln msg; pure 1
  | .ok p =>
    match p.decls.findSome? (fun d => match d with | .pattern m r => if m = name then some r else none | _ => none) with
    | none => IO.eprintln s!"{path}: no pattern `{name}`"; pure 1
    | some r =>
      let t0 ← IO.monoMsNow
      let profile := (← IO.getEnv "POLICYC_PROFILE") == some "1"
      let res : Except String (Table × List String) ←
        if profile then do
          match certifySurface r with
          | .error e => pure (.error e)
          | .ok (c, notes) =>
            let wholeTime ← IO.monoMsNow
            IO.eprintln s!"policyc profile: whole-word states={c.t.n} milliseconds={wholeTime - t0}"
            if absence then
              let result := (certifyAbsenceFrom r c notes).map (fun p => (p.1.t, p.2))
              match result with
              | .ok (t, _) =>
                let factorTime ← IO.monoMsNow
                IO.eprintln s!"policyc profile: absence states={t.n} milliseconds={factorTime - wholeTime}"
              | .error _ => pure ()
              pure result
            else pure (.ok (c.t, notes))
        else pure <| if absence then (certifySurfaceAbsence r).map (fun p => (p.1.t, p.2))
          else (certifySurface r).map (fun p => (p.1.t, p.2))
      match res with
      | .error e => IO.eprintln s!"{path}: pattern `{name}`: {e}"; pure 1
      | .ok (t, notes) =>
        let t1 ← IO.monoMsNow
        for n in notes do IO.eprintln s!"{path}: pattern `{name}`: {n}"
        let rows := (List.range t.n).map fun s => (List.range 256).map fun b => t.step s b
        let acc := (List.range t.n).filter t.acc
        let j := Json.mkObj [
          ("pattern", (name : Json)), ("absence", Json.bool absence), ("source", (printRe r : Json)),
          ("states", (t.n : Json)), ("alphabet", (256 : Json)),
          ("delta", Json.arr (rows.map jsonNats).toArray),
          ("start", (t.start : Json)), ("accept", jsonNats acc),
          ("num_states", (t.n : Json)), ("transitions", jsonNats rows.flatten),
          ("accepting", jsonNats acc)]
        IO.println j.compress
        IO.eprintln s!"{path}: pattern `{name}`{if absence then " (absence)" else ""}: {t.n} states, compiled in {t1 - t0} ms"
        pure 0

def rulesCmd (path : String) : IO UInt32 := do
  match ← readPolicy path with
  | .error msg => IO.eprintln msg; pure 1
  | .ok p =>
    let rs := rulesOf p
    let (P, ps) := elabProgram rs
    let strata := strataOf P ps.length
    let ok := match strata with
      | some st => Dregg2.Datalog.StratifiedCert.stratifiedB P st
      | none => false
    let j := Json.mkObj [
      ("program", Json.arr (P.map (fun r => Json.mkObj [("head", atomJson r.head),
        ("body", Json.arr (r.body.map litJson).toArray)])).toArray),
      ("strata", match strata with
        | some st => Json.arr (st.map jsonNats).toArray
        | none => Json.null),
      ("stratified", Json.bool ok),
      ("positive", Json.bool (rs.all (fun r => r.body.all (fun l => !l.neg)))),
      ("predNames", Json.arr (ps.map (fun s => (s : Json))).toArray)]
    IO.println j.pretty
    pure (if ok then 0 else 1)

def usage : String :=
  "usage: policyc check <file> | fmt <file> | compile <file> --pattern NAME [--absence] | rules <file>"

end Policyc

open Policyc in
def main (args : List String) : IO UInt32 := do
  match args with
  | ["check", f] => check f
  | ["fmt", f] => fmt f
  | ["rules", f] => rulesCmd f
  | "compile" :: f :: rest =>
    match rest with
    | ["--pattern", n] => compileCmd f n false
    | ["--pattern", n, "--absence"] | ["--absence", "--pattern", n] => compileCmd f n true
    | _ => IO.eprintln usage; pure 2
  | _ => IO.eprintln usage; pure 2
