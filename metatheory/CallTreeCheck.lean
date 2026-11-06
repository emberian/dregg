/-
# `lake exe calltree-check`: the call-tree certificate checker (initiative 9)

    calltree-check <bundle.json>      -- prints one JSON verdict; exit 0 ACCEPT, 1 REJECT, 2 bad input

The bundle carries the published root, the verifier's policy (pinned notary keys, allowed hosts),
the tree, and one evidence entry per presentation (the presentation bytes plus what
`presentation.verify()` extracted from them; `dregg-calltree verify` produces this offline). The
verdict is `Dregg2.Lightclient.CallTreeDeploy.deployedVerify`, i.e. `CallTreeCore.verify` at the
deployed hash and hop predicate, about which `Dregg2.Lightclient.CallTree.verify_sound`,
`no_omission` and `verify_attested` are proved. Nothing here decides anything else: the rest of
this file is JSON and hex parsing.
-/
import Lean.Data.Json
import Dregg2.Lightclient.CallTreeDeploy

open Dregg2.Lightclient.CallTreeCore
open Dregg2.Lightclient.CallTreeDeploy
open Lean (Json)

def hexBytes (s : String) : Except String ByteArray :=
  match Dregg2.Crypto.Blake3.ofHex s with
  | some b => .ok b
  | none => .error s!"bad hex ({s.length} chars)"

def hexInt (s : String) : Except String Int := do
  if s = "0" then return 0
  let b ← hexBytes s
  return Int.ofNat (ofBE b)

def getStr (j : Json) (k : String) : Except String String := do
  (← j.getObjVal? k).getStr?

partial def parseTree (j : Json) : Except String CallTree := do
  let kind ← (← j.getObjVal? "kind").getInt?
  let hop : Hop := ⟨kind, ← hexInt (← getStr j "att"), ← hexInt (← getStr j "host"),
    ← hexInt (← getStr j "req"), ← hexInt (← getStr j "resp")⟩
  let kids ← (← j.getObjVal? "kids").getArr?
  let ks ← kids.toList.mapM parseTree
  return .node hop ks

def parseEvidence (j : Json) : Except String Evidence := do
  return { presentation := ← hexBytes (← getStr j "presentation"),
           serverName := ← getStr j "server_name",
           notaryKey := ← getStr j "notary_key",
           sent := ← hexBytes (← getStr j "sent"),
           recv := ← hexBytes (← getStr j "recv") }

def strList (j : Json) : Except String (List String) := do
  (← j.getArr?).toList.mapM (·.getStr?)

structure Bundle where
  root : Int
  pol : Policy
  tree : CallTree
  evs : List Evidence

def parseBundle (j : Json) : Except String Bundle := do
  let p ← j.getObjVal? "policy"
  return { root := ← hexInt (← getStr j "root"),
           pol := { notaries := ← strList (← p.getObjVal? "notaries"),
                    hosts := ← strList (← p.getObjVal? "hosts") },
           tree := ← parseTree (← j.getObjVal? "tree"),
           evs := ← (← (← j.getObjVal? "evidence").getArr?).toList.mapM parseEvidence }

mutual
def countNodes : CallTree → Nat
  | .node _ ks => 1 + countNodesL ks
def countNodesL : List CallTree → Nat
  | [] => 0
  | k :: ks => countNodes k + countNodesL ks
end

def main (args : List String) : IO UInt32 := do
  match args with
  | [path] =>
      let s ← IO.FS.readFile path
      match Json.parse s >>= parseBundle with
      | .error e =>
          IO.eprintln s!"calltree-check: bad bundle: {e}"
          return 2
      | .ok b =>
          let ok := deployedVerify b.evs b.pol b.root b.tree
          let out := Json.mkObj
            [ ("verdict", Json.str (if ok then "ACCEPT" else "REJECT"))
            , ("root", Json.str (hex64 b.root))
            , ("recomputed_root", Json.str (hex64 (commit treeHash b.tree)))
            , ("nodes", Lean.toJson (countNodes b.tree))
            , ("presentations", Lean.toJson b.evs.length) ]
          IO.println out.compress
          return if ok then 0 else 1
  | _ =>
      IO.eprintln "usage: calltree-check <bundle.json>"
      return 2
