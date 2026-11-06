# Tree automata over JSON and CBOR — arithmetization note (2026-11-05)

Tags: [READ] seen at file:line; [MEASURED] a pinned #guard or a run; [CLAIM] asserted elsewhere; [INFERRED] derived here.

Hub: `AUTOMATA-ARITHMETIZATION-PROGRAM.md` §2 row "tree automata over JSON/CBOR". M = `/Users/ember/dev/breadstuffs/metatheory/Dregg2`.
Nothing in this note is built. The census's grep over M for "tree automat" returned 0 files [READ census].

A tree automaton over a document can be certified in two ways. (i) Run a VPA over the document's
serialization, reusing `04`. (ii) Commit the document as a Merkleized AST and check one automaton
transition per node. The arithmetic in §3 shows that (i) is cheaper whenever the statement covers the
whole tree and `c` commits the bytes. (ii) is right only when the content scheme already *is* the
Merkle AST, or when the statement concerns one subtree. A JSON Schema is a tree automaton only on its
regular core.

## 1. Semantics object (Lean)

Proposed. Unranked ordered trees, a deterministic bottom-up hedge automaton whose horizontal
languages are given by one shared horizontal DFA, and the pre-order serialization:

```lean
/-- An unranked, ordered, labelled tree (a JSON/CBOR value with object keys as labels). -/
inductive JTree (L : Type) where
  | node (label : L) (kids : List (JTree L))

/-- A deterministic bottom-up hedge automaton. A node labelled `l` runs the horizontal DFA from
    `hstart l` over its children's states; `hfinal l h` is the node's state, or `none` (reject). -/
structure TreeAut (Q H L : Type) where
  hstart : L → H
  hstep  : H → Q → H
  hfinal : L → H → Option Q
  accept : Q → Prop

namespace TreeAut
variable {Q H L : Type} (A : TreeAut Q H L)

def eval : JTree L → Option Q
  | .node l kids =>
      (kids.attach.foldlM (fun h ⟨k, _⟩ => (eval k).map (A.hstep h)) (A.hstart l)) >>= A.hfinal l

def Accepts (t : JTree L) : Prop := ∃ q, A.eval t = some q ∧ A.accept q
end TreeAut

/-- Pre-order serialization: an open event, the children, a close event. -/
inductive Ev (L : Type) | op (l : L) | cl (l : L)

def ser : JTree L → List (Ev L)
  | .node l kids => .op l :: (kids.attach.flatMap fun ⟨k, _⟩ => ser k) ++ [.cl l]
```

(`eval` and `ser` recurse through `List.attach`, so that structural termination on the nested
inductive goes through `sizeOf`. This is the standard Lean 4 idiom; it has not been compiled.)

The VPA view uses `04`'s partitioned alphabet (`VAlphabet` with `Call := L`, `Ret := L`, `Int := Empty`):

```lean
/-- Call on `op l`: push the parent's horizontal state, restart at `hstart l`.
    Return on `cl l`: finish the child (`hfinal l`), pop the parent's `h`, step it. -/
def toVpa (A : TreeAut Q H L) : VpaOver ⟨L, L, Empty⟩ (Option H) (Option H × L) where
  call := fun s l s' γ => γ = (s, l) ∧ s' = some (A.hstart l)
  ret  := fun s l s' γ => γ.2 = l ∧
            s' = (do let h ← s; let q ← A.hfinal l h; let hp ← γ.1; pure (A.hstep hp q))
  int  := fun _ e _ => e.elim

theorem toVpa_correct (A : TreeAut Q H L) (root : H) (t : JTree L) :
    A.Accepts t ↔ LangOver (toVpa A) (some root) (acceptTop A) (ser t)
```

`acceptTop` reads the root's state through a virtual root, and `LangOver` is `04`'s `Lang` over
`VpaOver`. The `γ.2 = l` conjunct, the return checking that the closer's label is the opener's, is
load-bearing; §5's falsifier is the automaton without it.

### Scope: what a JSON Schema is

Every JSON Schema has an equivalent VPA once key order is fixed (Bruyère, Pérez, Staquet, TACAS 2023)
[READ]. Modern JSON Schema is **not** a tree-automaton language in general. Per the snippet of Attouche
et al. (POPL 2024), earlier work showed Draft-04 expressiveness beyond MSO and tree automata
[SNIPPET]. So "schema as tree automaton" holds for the regular core only: `type`, `properties`/`required`
over a finite key set, `items`, `enum`/`const` of bounded size, `pattern` (regular over string bytes,
`02`), bounded `minItems`/`maxItems`, and `$ref` recursion. The snippet does not say which keywords
break regularity. `uniqueItems` (equality of unboundedly large sibling subtrees) is the obvious
candidate [INFERRED, unverified]. JSON objects are unordered. An ordered `TreeAut` needs a horizontal
language closed under key permutation, which costs `2^|keys|` horizontal states for `required` over
`|keys|` keys [INFERRED]. Bruyère et al. sidestep this by fixing key order.

## 2. Certificate shape

`c` commits the document's bytes (`hash_bytes_8`, as in `zkoracle-prove/src/attestation.rs:84` [READ]).

| route | public `x` | witness | per node |
|---|---|---|---|
| (i) serialized run | `c`, the VPA tables of `toVpa A` (`hstart`, `hstep`, `hfinal` as lookup tables) | the bytes, the token/event stream, the run | 2 events (open, close) per node under `ser`; a scalar leaf could be 1 internal event in a serialization with `Int := leaf labels`, which `ser` as written does not use |
| (ii) Merkleized AST | `r` = AST root digest (and, if `c` is the byte commitment, a parse certificate tying `r` to `c`) | one row per node: label, the node's digest, the state `q`, the first-child and next-sibling digests and states | 1 row |

Route (ii) in left-child right-sibling (LCRS) form turns the hedge automaton into a binary tree
automaton with states `(q, h)` pairs. Each node row checks one transition
`(label, (q, h)_firstchild, (q, h)_nextsibling) → (q, h)` and one hash
`d = P2(label ‖ d_fc ‖ d_ns)`. Child rows are wired to parent rows by a lookup on `(digest, state)`.

## 3. Arithmetization and counts

**Commitment:** `n/8` Poseidon2 permutations for `n` bytes = 44 committed cells per byte at the
352-cell permutation [READ `circuit/src/poseidon2.rs:704`, `sel4/dregg-pd/executor-pd/crypto-floor/src/field.rs:94`;
MEASURED `Poseidon2RoundGates.lean` `#guard POSEIDON2_AUX_COLS == 352`]. Chip input width
`CHIP_RATE = 16` lanes and 8 output lanes [READ census, `ChipTableEmit.lean`; MEASURED `#guard CHIP_WIDTH == 386`].

**Route (i), per node** [INFERRED, from `04` §3's proposed VPA row]: 2 rows (open, close), each about 8
main columns. Per row: 1 transition lookup and 1 stack-memory multiset entry. 0 permutations. On top
of that, the lexer (bytes → events): 1 row and 1 lookup per byte (`05` §3). If a node's serialization
averages `b` bytes, the per-node bill is `44b` hash cells + `~3b` lexer cells + `~16` VPA cells.

**Route (ii), per node** [INFERRED]: the hash input is `1 + 8 + 8 = 17` felts (label plus two 8-felt child
digests), one more than `CHIP_RATE = 16`. So it takes **2 permutations per node**, which is `2 · 352 = 704`
committed cells at the wide arm or `2 · 141 = 282` at the narrow arm [MEASURED for 352 and 141, the
census's `narrow_aux_cols_is_141`]. One permutation per node would need child digests of at most 7
felts (about 217 bits, so about 108-bit birthday security) or a label packed into a digest lane. The
hub's "1 node = 1 lookup + 1 hash" is optimistic on both counts. It is 1 transition lookup + 2 wiring
lookups + 2 permutations. A scalar leaf's content (a string of `b` bytes) must still be hashed into its
leaf digest, `b/8` permutations, the same 44 cells per byte as route (i).

**Comparison.** Per node, route (i) costs `47b + 16` cells and route (ii) costs `44b_leaf + 704 + ~10`
cells. The leaf bytes appear in both, so route (ii) is more expensive by about 690 cells per node, and
its structural bytes (`{`, `,`, `:`, quotes) are free only because they are not committed [INFERRED].
**For a whole-tree statement over a byte commitment, route (i) wins at every node size.** If `c` is the
byte commitment, route (ii) also needs a parse certificate from bytes to `r` (`05`), so it pays both
routes. Route (ii) wins in two cases:

1. **The content scheme is the Merkle AST** (a Merkle-DAG record format such as DAG-CBOR [RECALLED]),
   so `r` is `c` and no bytes are hashed as a flat stream.
2. **The statement concerns one subtree** (a local property): an opening path of depth `d` costs `2d`
   permutations plus the subtree's nodes, independent of the rest of the document. That is CERTIFICATES
   L6, lifted from substrings to subtrees.

**CBOR, definite length: the VPA-friendly case.** In definite-length CBOR every container header
carries its item count (major types 4 and 5) and every string header carries its byte length
[RECALLED, RFC 8949]. The call/return structure is therefore a deterministic function of the headers:
a header with count `k > 0` pushes `k`; each completed item decrements the top; at zero, the run pops
(possibly several pops at one position, as virtual return rows the verifier checks with `count = 0`).
Three consequences [INFERRED]:

- No closer tokens are needed and none can mismatch. The `γ.2 = l` check of §1 becomes a counter-zero check.
- String contents are skipped structurally (their extent is the header's length), so the automaton runs
  over headers only, and the per-byte cost is the commitment's 44 cells, not a lexer row per byte. JSON's
  string lexing (escapes, quotes) has no CBOR analogue.
- The counts are up to 64-bit, wider than a BabyBear felt. A count in a stack cell needs a range check,
  which costs `⌈bits/4⌉` lookups on the nibble table (`#guard HEIGHT == 16`, `ByteTableEmit.lean`
  [MEASURED]). That is 8 lookups for a 32-bit count, per container header.

Indefinite-length CBOR (`0x9f … 0xff`) has explicit break codes and is the bracketed VPA case directly.
CBOR's core deterministic encoding makes tree → bytes injective [RECALLED, RFC 8949 §4.2]. JSON's
encoding is not injective (whitespace, key order, number spellings, escapes), so a statement about
"the bytes" and a statement about "the tree" differ for JSON and coincide for deterministic CBOR.

## 4. Binding to the content commitment

Route (i): the run reads the event stream, the lexer reads the bytes, and the bytes are absorbed into
`c` in-circuit. One trace, shared cells, no `b` term inside it (`05` §4 for the lexer weld). Route (ii):
binds to `r`. Binding to a byte `c` needs a bytes ↔ AST certificate (L5 morphism, `05`), and the
morphism is injective only for a canonical encoding (deterministic CBOR, yes; JSON, no). Today nothing
is bound, because nothing exists.

## 5. Soundness statement (Lean syntax) and its vacuity falsifier

```lean
/-- Content-bound tree-automaton statement over bytes, through a named parser. -/
theorem treeCert_bound_sound {Q H L D Proof : Type} {S : ContentScheme UInt8 D}
    (A : TreeAut Q H L) (parse : List UInt8 → Option (JTree L))
    [K : TreeBoundVerifierKernel A parse S Proof]
    (hext : K.extractable) (c : D) (proof : Proof) (haccept : K.verify c proof = true) :
    ∃ bytes, S.commit bytes = c ∧ ∃ t, parse bytes = some t ∧ A.Accepts t
```

For route (i), `K.extract` delivers an accepting `toVpa A` run over `ser t`, and `toVpa_correct` turns
it into `A.Accepts t`. The parser leg is `parse bytes = some t ↔ events (lex bytes) = some (ser t)`, a
round-trip lemma to prove once per format. For route (ii), `K.extract` delivers a node table whose root
digest is `r`, plus the morphism from `c` to `r`. The statement names `c` and the tree, so it meets L0.

**Falsifier: the label-blind return.** Drop the `γ.2 = l` conjunct from `toVpa`'s `ret`. Take labels
`{obj, arr}` and the automaton that accepts every tree (`hfinal _ _ = some ()`). Then the event stream
`[.op obj, .cl arr]` has an accepting run of the label-blind VPA, but it is the serialization of no
tree: `¬ ∃ t, ser t = [.op obj, .cl arr]`, because `ser (.node l _)` begins with `.op l` and ends with
`.cl l` for the same `l`. As decidable guards, with a label-blind checker `runBlind` and the real one `run`:

```lean
#guard runBlind trivialAut [.op .obj, .cl .arr] = true    -- the weaker shape accepts a mis-nesting
#guard run      trivialAut [.op .obj, .cl .arr] = false   -- the label-checked return refuses it
#guard run      trivialAut [.op .obj, .cl .obj] = true    -- and accepts the well-nested stream
```

For JSON bytes this is `{]` being accepted as an object. Route (ii)'s analogue is a node table whose
rows check transitions and hashes but not the child-wiring lookup. The prover can then attach the
state of any row with a valid digest, including a row of another document, so the falsifier is two
documents sharing a subtree digest with different states.

## 6. Composition behaviour

| operator | route (i) | route (ii) |
|---|---|---|
| product / intersection of two schemas | product of horizontal DFAs and states, or two VPA runs sharing the event column: `+1` lookup per row, one witness | `+1` transition lookup per node row |
| complement | deterministic `TreeAut`: totalize `hfinal` (`none` goes to a sink state), then flip `accept`; bottom-up deterministic tree automata are closed under complement, so a rejection certificate is one run | same |
| conjunction with a byte-level regex (`02`, e.g. "no string field contains `{{`") | fuse on the byte rows: one trace, no `b` term | the regex runs inside each leaf's hash input; one trace |
| conjunction with a CFG certificate over the same bytes (`05`) | the parse and the tree run are the same event stream; fuse | needs the bytes ↔ AST morphism |
| weld to `c` | in-circuit sponge over bytes | L5 morphism `r ↔ c` |
| MMR aggregation | L2: `N` documents, `N·ε + b_M + b` | same, with `b_r` (the AST root's binding) added |

Where additivity fails for this family: if the schema leg is route (ii) and a substring leg is over `c`
(bytes), their conjunction is L1 plus L5, so the error is `ε₁ + ε₂ + b + b_r`, and it is unsound for JSON
regardless of `ε`, because bytes → AST is not injective (L5's injectivity condition, hub §3.1 item 4).

## 7. Prior art

- Coral, ePrint 2025/1420, IEEE S&P 2026 [READ]: ZK proofs that a committed byte stream parses under a
  CFG into a left-child right-sibling tree held in segmented memory, then selective field facts (JSON,
  TOML, C). That is route (i)'s parse with route (ii)'s tree representation inside one proof, and the
  closest prior art.
- Bruyère, Pérez, Staquet, *Validating Streaming JSON Documents with Learned VPAs*, TACAS 2023, arXiv
  2211.08891 [READ]: JSON Schema ≡ VPA with fixed key order; a streaming validator.
- Attouche et al., *Validation of Modern JSON Schema: Formalization and Complexity*, POPL 2024 [SNIPPET]:
  the expressiveness caveat of §1.
- zkJSON (weavedb) [SNIPPET]: ZK-provable JSON fields, not grammar-based.
- Merkleized ASTs (BIP 114 / Taproot script trees) [RECALLED; not searched this session].

Not claimed as ours: ZK JSON parsing (Coral), JSON-Schema-as-VPA (Bruyère et al.), Merkleized ASTs. No
hit for tree automata over CBOR/JSON in a circuit, with the query "zero-knowledge proof JSON schema
validation tree automata" (PRIOR-ART §7). That is a "no hit".

## 8. Built vs proposed

| object | where | rung |
|---|---|---|
| `JTree`, `TreeAut`, `eval`, `Accepts`, `ser` | proposed | L0 |
| `toVpa`, `toVpa_correct` | proposed; depends on `04`'s `VAlphabet`/`VpaOver` | L0 |
| `treeCert_bound_sound` | proposed | L0 |
| label-blind falsifier | proposed | L0 → L2 with the three `#guard`s |
| route (i) AIR | proposed; the `04` memory-stack VPA row plus the `05` lexer | L0 |
| route (ii) AIR | proposed | L0 |
| CBOR header walker | proposed | L0 |

**Milestone:** `toVpa_correct` proved for one concrete schema in the regular core, "an object whose
key `"role"` maps to one of three strings", encoded as a `TreeAut` with `|H| ≤ 8` horizontal states.
Land it with the three label-blind `#guard`s and a `#guard` that the computable run accepts the event
stream of `{"role":"admin"}` and rejects `{"role":7}`. Pin the event count (`(ser t).length = 2 · nodes t`, which is 6 for that document's three nodes) beside
the route (ii) count of 2 permutations per node. Rung L2.
