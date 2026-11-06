/-
# Dregg2.Stream.ClaudeCore: the demo policy over Claude Code transcripts (executable, Lean core only)

One entry is one line of a Claude Code session transcript (`~/.claude/projects/<proj>/<session>.jsonl`).
The classifier `classify` reads the line's JSON and yields one of four symbols; the policy is the
product (`Omega.prodSafety`) of

* **safety**: no assistant `Bash` call's command text contains one of ember's forbidden commands
  (`RULES.md`, CLAUDE.md) as a command segment, read syntactically by `commandForbidden` (wrappers
  such as `sudo`, `bash -c`, `ssh host` peeled; `git stash`, `git add -A|--all`, `pkill -f|-x`,
  `killall`, `kill -u`). Tripping is absorbing.
* **liveness** (Büchi): every human prompt is eventually followed by assistant text. The marked set is
  "no prompt waiting".

The classifier is part of the statement: the theorems are about the symbols THIS function computes from
the committed bytes, and the follower computes symbol and leaf from the same bytes (`Crypto.Dfa` Layer
B′'s law: a statement that does not bind content is discharged by a benign word).
-/
import Lean.Data.Json
import Dregg2.Stream.Core

namespace Dregg2.Stream.Claude

open Lean (Json)

/-- The transcript alphabet. -/
inductive Ev
  | prompt
  | reply
  | forbidden
  | other
  deriving DecidableEq, Repr, Inhabited

def isSep (c : Char) : Bool := c == ';' || c == '&' || c == '|' || c == '\n' || c == '(' || c == ')'

/-- Wrappers that run their argument as a command: `sudo`, `env`, `nohup`, `exec`, `command`,
`time`, `bash -c`, `sh -c`, `zsh -c`, `timeout D`, `ssh [opts] host`. Each is peeled before the
command word is read. -/
partial def peel : List String → List String
  | [] => []
  | t :: rest =>
    if t ∈ ["sudo", "env", "nohup", "exec", "command", "time", "xargs"] then peel (rest.dropWhile (·.startsWith "-"))
    else if t ∈ ["bash", "sh", "zsh"] then
      match rest with
      | "-c" :: r => peel r
      | "-lc" :: r => peel r
      | _ => t :: rest
    else if t = "timeout" then
      match rest.dropWhile (·.startsWith "-") with
      | _ :: r => peel r
      | [] => []
    else if t = "ssh" then
      -- options (with their argument for the ones that take one), then the host, then the command
      let rec skip : List String → List String
        | o :: a :: r => if o ∈ ["-o", "-p", "-i", "-l", "-J", "-F"] then skip r
            else if o.startsWith "-" then skip (a :: r) else o :: a :: r
        | [o] => if o.startsWith "-" then [] else [o]
        | [] => []
      match skip rest with
      | _host :: r => peel r
      | [] => []
    else t :: rest

/-- A short-option cluster (`-Av`, `-9f`) containing `c`. -/
def shortHas (t : String) (c : Char) : Bool := t.startsWith "-" && !t.startsWith "--" && t.contains c

/-- One command (already peeled): ember's forbidden set. `git [-C p] [-c k=v] stash …`,
`git add` with `-A` / `--all` (or a short cluster containing `A`), `pkill` with `-f` or `-x` (or a
cluster containing either), `killall`, `kill -u`. -/
def wordsForbidden : List String → Bool
  | "git" :: rest =>
    let rec sub : List String → List String
      | o :: a :: r => if o = "-C" || o = "-c" then sub r else if o.startsWith "-" then sub (a :: r) else o :: a :: r
      | l => l
    match sub rest with
    | "stash" :: _ => true
    | "add" :: args => args.any fun a => a = "--all" || shortHas a 'A'
    | _ => false
  | "pkill" :: args => args.any fun a => shortHas a 'f' || shortHas a 'x'
  | "killall" :: _ => true
  | "kill" :: args => args.any (· = "-u")
  | _ => false

/-- A shell command runs a forbidden command iff one of its segments (split at `;`, `&`, `|`,
newline, `(`, `)`, quotes removed), after peeling wrappers, is a forbidden command. A syntactic
reading of the command text, not of what the shell would execute: `eval`, variables and scripts are
not followed. -/
def commandForbidden (cmd : String) : Bool :=
  let unq := String.ofList (cmd.toList.filter fun c => c != '\'' && c != '"' && c != '`')
  (unq.split isSep).any fun seg =>
    let words := (seg.toString.split (fun c => c == ' ' || c == '\t')).toList.map (·.toString) |>.filter (· ≠ "")
    wordsForbidden (peel words)

def strField (j : Json) (k : String) : Option String := (j.getObjValAs? String k).toOption

def content? (j : Json) : Option Json := do
  let m ← (j.getObjVal? "message").toOption
  (m.getObjVal? "content").toOption

def blocks (j : Json) : List Json :=
  match content? j with
  | some (Json.arr a) => a.toList
  | _ => []

def blockIsForbiddenBash (b : Json) : Bool :=
  strField b "type" == some "tool_use" && strField b "name" == some "Bash" &&
    (match ((b.getObjVal? "input").toOption).bind (fun i => strField i "command") with
     | some c => commandForbidden c
     | none => false)

def blockIsText (b : Json) : Bool :=
  strField b "type" == some "text" &&
    (match strField b "text" with
     | some t => !t.trimAscii.isEmpty
     | none => false)

/-- A human prompt: a `user` record whose content is a non-empty string (or text blocks, no tool
result), not `isMeta`, not a harness-injected command echo or interruption marker. -/
def isPrompt (j : Json) : Bool :=
  let isMeta := (j.getObjValAs? Bool "isMeta").toOption == some true
  let content := content? j
  let human (t : String) : Bool :=
    let t := t.trimAsciiStart.toString
    !t.isEmpty && !t.startsWith "<command-" && !t.startsWith "<local-command" &&
      !t.startsWith "[Request interrupted" && !t.startsWith "<system-reminder>"
  strField j "type" == some "user" && !isMeta &&
    (match content with
    | some (Json.str t) => human t
    | some (Json.arr a) =>
      !a.toList.any (fun b => strField b "type" == some "tool_result") &&
        a.toList.any (fun b => strField b "type" == some "text" &&
          match strField b "text" with | some t => human t | none => false)
    | _ => false)

/-- **The classifier.** Priority: a forbidden Bash call, then assistant text, then a human prompt. -/
def classifyJson (j : Json) : Ev :=
  if strField j "type" == some "assistant" then
    if (blocks j).any blockIsForbiddenBash then .forbidden
    else if (blocks j).any blockIsText then .reply
    else .other
  else if isPrompt j then .prompt
  else .other

def classify (line : String) : Ev :=
  match Json.parse line with
  | .ok j => classifyJson j
  | .error _ => .other

/-! ## The automaton -/

/-- Safety half: state `true` = a forbidden command has run. -/
def safeMon : SafetyMon Bool Ev where
  step s a := s || decide (a = Ev.forbidden)
  start := false
  bad s := s

/-- Liveness half (Büchi): state `true` = a prompt is waiting for a reply; marked = nothing waiting. -/
def respLive : DOmega Bool Ev where
  step w a := match a with
    | .prompt => true
    | .reply => false
    | _ => w
  start := false
  mark w := !w

/-- The demo policy automaton: states `(tripped, waiting)`, Büchi over "not tripped and not waiting". -/
def policyA : DOmega (Bool × Bool) Ev := prodSafety safeMon respLive

/-- Its verdict certificate: tripped states are dead; no state is good. -/
def policyVC : VCert (Bool × Bool) := prodVCert safeMon

/-- A policy over abstract entries, for any committed value and hash (the theorems' form). -/
def policyOver {E : Type} (hash : List Int → Int) (val : E → Int) (sym : E → Ev) : Policy E (Bool × Bool) Ev :=
  ⟨policyA, policyVC, hash, val, sym⟩

end Dregg2.Stream.Claude
