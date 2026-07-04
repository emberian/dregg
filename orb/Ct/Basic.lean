/-
Ct.Basic — the abstract collision-resistant hash interface.

An RFC 6962 Merkle log is a tree of SHA-256 digests over three hash forms
(section 2):

  * `SHA-256()`             — the head of the empty log,
  * `SHA-256(0x00 ‖ d)`     — the *leaf* hash of leaf datum `d`,
  * `SHA-256(0x01 ‖ l ‖ r)` — the *interior node* hash of children `l`, `r`.

We do NOT implement a hash.  The digest type `H` is left abstract and the three
forms are *uninterpreted function parameters* bundled in `HashScheme` together
with the exact algebraic facts a collision-resistant, domain-separated hash
provides:

  * `hleaf_inj`, `hnode_inj` — *collision resistance*: a colliding digest forces
    equal pre-images (the idealized random-function abstraction of SHA-256);
  * `leaf_ne_node`, `empty_ne_leaf`, `empty_ne_node` — *domain separation*: the
    `0x00` / `0x01` (and empty) tag prefixes put the three forms in disjoint
    ranges.

Because the interface is a parameter, not a Lean `axiom`, nothing here enlarges
the axiom footprint: every theorem downstream is discharged relative to an
arbitrary `HashScheme`, and the digest is never realized.
-/

namespace Ct

/-- Abstract collision-resistant, domain-separated hash interface for an
RFC 6962 Merkle tree over leaves of type `Leaf` with digests of type `H`. -/
structure HashScheme (Leaf : Type) (H : Type) where
  /-- `SHA-256()` — head of the empty log. -/
  hempty : H
  /-- `SHA-256(0x00 ‖ d)` — leaf hash. -/
  hleaf : Leaf → H
  /-- `SHA-256(0x01 ‖ l ‖ r)` — interior node hash. -/
  hnode : H → H → H
  /-- Collision resistance of the leaf form. -/
  hleaf_inj : ∀ {x y}, hleaf x = hleaf y → x = y
  /-- Collision resistance of the node form. -/
  hnode_inj : ∀ {a b c d}, hnode a b = hnode c d → a = c ∧ b = d
  /-- Domain separation: a leaf hash is never a node hash (`0x00` vs `0x01`). -/
  leaf_ne_node : ∀ x a b, hleaf x ≠ hnode a b
  /-- Domain separation: the empty-log head is never a leaf hash. -/
  empty_ne_leaf : ∀ x, hempty ≠ hleaf x
  /-- Domain separation: the empty-log head is never a node hash. -/
  empty_ne_node : ∀ a b, hempty ≠ hnode a b

def version : String := "0.1.0"

end Ct
