/-
# Dregg2.Lightclient.CallTreeCore — the call-tree certificate, computable half (Lean core only).

A **call tree** is what one agent turn did over the network: the turn itself is the root node, every
outbound HTTPS request it made is a child, and a callee that records its own outbound requests
contributes them as that child's children. Each node carries five integers (`Hop`): a kind, the
digest of the transport attestation (a TLSNotary presentation), and digests of the authenticated
server name, request bytes and response bytes. The children are committed by the MMR root of their
commitments, so the root of the whole tree is ONE integer.

This module holds only definitions and imports Lean core, so the extracted checker
(`CallTreeCheck.lean`, `lake exe calltree-check`) compiles in seconds without mathlib. The theorems
are in `Dregg2.Lightclient.CallTree`, which also proves `mrootC = Dregg2.Lightclient.MMR.mroot`:
the MMR here is a verbatim copy of `MMR.lean` §1–§3's definitions (that module imports mathlib),
and the equality is what lets the checker use it without being a second, unrelated algorithm.
-/

namespace Dregg2.Lightclient.CallTreeCore

/-! ## The MMR root, core-only (`MMR.lean` §1–§3, definitions verbatim). -/

/-- A peak tree, as `MMR.PTree`. -/
inductive PT : Type where
  | leaf (v : Int)
  | node (l r : PT)

namespace PT
def height : PT → Nat
  | .leaf _ => 0
  | .node l _ => l.height + 1
def hashOf (hash : List Int → Int) : PT → Int
  | .leaf v => hash [v]
  | .node l r => hash [l.hashOf hash, r.hashOf hash]
end PT

def push : List PT → PT → List PT
  | [], t => [t]
  | s :: rest, t => if t.height = s.height then push rest (.node s t) else t :: s :: rest

def appendLeaf (f : List PT) (v : Int) : List PT := push f (.leaf v)
def peaksOf (L : List Int) : List PT := L.foldl appendLeaf []
def bag (hash : List Int → Int) : List PT → Int
  | [] => hash []
  | t :: rest => hash [t.hashOf hash, bag hash rest]

/-- The MMR root of a list, as `MMR.mroot` (proved equal in `CallTree.mrootC_eq`). -/
def mrootC (hash : List Int → Int) (L : List Int) : Int := bag hash (peaksOf L)

/-! ## The tree. -/

/-- One node's committed record. `kind`: 0 = the local turn node (no transport), 1 = an attested
HTTPS hop, 2 = an attested hop to a callee that records its own calls (its subtree root must appear
in the authenticated response). The other four are digests read as integers. -/
structure Hop where
  kind : Int
  att  : Int
  host : Int
  req  : Int
  resp : Int
deriving DecidableEq, Repr

def Hop.fields (h : Hop) : List Int := [h.kind, h.att, h.host, h.req, h.resp]

/-- The call tree: a hop and its children, in call order. -/
inductive CallTree where
  | node (hop : Hop) (kids : List CallTree)
deriving Repr

namespace CallTree
def hop : CallTree → Hop
  | .node h _ => h
def kids : CallTree → List CallTree
  | .node _ ks => ks
end CallTree

mutual
/-- The commitment of a tree: `hash [kind, att, host, req, resp, kidsRoot]` — arity 6, so a tree
preimage never coincides with an MMR preimage (arity 0, 1 or 2; MMR internal peak nodes and
non-empty bags BOTH have arity 2, which `MMR.lean` handles itself). -/
def commit (hash : List Int → Int) : CallTree → Int
  | .node h ks => hash (h.fields ++ [mrootC hash (commits hash ks)])
/-- The children's commitments, in order. -/
def commits (hash : List Int → Int) : List CallTree → List Int
  | [] => []
  | k :: ks => commit hash k :: commits hash ks
end

/-- The kids root of a node. -/
def kidsRoot (hash : List Int → Int) (ks : List CallTree) : Int := mrootC hash (commits hash ks)

/-- The preimage `commit` hashes. -/
def preimage (hash : List Int → Int) : CallTree → List Int
  | .node h ks => h.fields ++ [kidsRoot hash ks]

mutual
/-- Every node passes the hop predicate `V`, which sees the hop and its kids root. -/
def allOk (V : Hop → Int → Bool) (hash : List Int → Int) : CallTree → Bool
  | .node h ks => V h (kidsRoot hash ks) && allOkL V hash ks
def allOkL (V : Hop → Int → Bool) (hash : List Int → Int) : List CallTree → Bool
  | [] => true
  | k :: ks => allOk V hash k && allOkL V hash ks
end

/-- The hop predicate "this is a transport hop" (kind ≠ 0). -/
def isTransport (h : Hop) (_kr : Int) : Bool := h.kind != 0

/-- **The verifier.** Accept iff the tree's recomputed commitment is the published root, the root
is the local turn node (kind 0) and EVERY other node is a transport hop (kind ≠ 0) — so no hop can
be relabelled "local" to escape the attestation check — and every node passes `V`. This is the
function the extracted checker runs. -/
def verify (V : Hop → Int → Bool) (hash : List Int → Int) (root : Int) (t : CallTree) : Bool :=
  decide (commit hash t = root) && t.hop.kind == 0 && allOkL isTransport hash t.kids &&
    allOk V hash t

end Dregg2.Lightclient.CallTreeCore
