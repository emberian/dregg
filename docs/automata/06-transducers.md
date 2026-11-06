# Transducers, Mealy machines, tokenization and detokenization — arithmetization note (2026-11-05)

Tags: [READ] seen at file:line; [MEASURED] a pinned #guard or a run; [CLAIM] asserted elsewhere; [INFERRED] derived here.

Paths: `M` = `/Users/ember/dev/breadstuffs/metatheory/Dregg2`, `R` = `/Users/ember/dev/breadstuffs`.
Hub: `docs/automata/AUTOMATA-ARITHMETIZATION-PROGRAM.md` §2 (row "transducers / Mealy"), §3 (row
"transducer chain"), §3.1 item 3.

**Status in the tree.** Nothing here is built. There is no BPE tokenizer and no tokenization or
detokenization certificate anywhere in the tree: `R/tokenizer/src` is credential sealing
("Tokenizer — sealed secret encryption for credential isolation", `lib.rs:1-5`), and a grep for
`Mealy|transducer` over `M` returns 0 files [READ, census §5]. The only byte-to-token map in scope is
the JSON lexer `R/zkoracle-prove/src/cfg.rs:215 tokenize`, which is unverified Rust with no Lean twin
[READ, census §5].

## 1. Semantics object (Lean)

Proposed. A subsequential transducer (each input symbol emits a word, plus a final flush) covers both
directions. A strict Mealy machine is the special case where every emission has length 1.

```lean
namespace Dregg2.Crypto.Transducer

/-- Subsequential transducer: deterministic, emits a (possibly empty) output word per input symbol,
plus a final flush that depends on the last state. A Mealy machine has `|emit q a| = 1`. -/
structure Mealy (State In Out : Type) where
  step  : State → In → State
  emit  : State → In → List Out
  start : State
  flush : State → List Out

def Mealy.runFrom (T : Mealy State In Out) : State → List In → State × List Out
  | q, []      => (q, [])
  | q, a :: as =>
      let r := T.runFrom (T.step q a) as
      (r.1, T.emit q a ++ r.2)

/-- The function the transducer computes. -/
def Mealy.translate (T : Mealy State In Out) (w : List In) : List Out :=
  let r := T.runFrom T.start w
  r.2 ++ T.flush r.1

/-- DETOKENIZATION is a one-state transducer (a monoid homomorphism): token `t` emits `vocab t`. -/
def detok (vocab : V → List UInt8) (toks : List V) : List UInt8 := toks.flatMap vocab

def detokMealy (vocab : V → List UInt8) : Mealy Unit V UInt8 :=
  { step := fun _ _ => (), emit := fun _ t => vocab t, start := (), flush := fun _ => [] }

/-- Tokenization as a RELATION: every token sequence that detokenizes to the bytes. Not functional. -/
def IsTokenization (vocab : V → List UInt8) (bytes : List UInt8) (toks : List V) : Prop :=
  detok vocab toks = bytes

/-- BPE in the rank-order formulation: apply each merge rule, in priority order, left to right over
the whole sequence. Berglund-van der Merwe show the SentencePiece and HuggingFace variants differ, so a
deployed tokenizer must be matched to ONE named formulation; this is the one written here. -/
structure Bpe (V : Type) where
  vocab   : V → List UInt8
  byteTok : UInt8 → V
  merges  : List (V × V × V)          -- (left, right, merged), highest priority first

def mergeOnce [DecidableEq V] (a b m : V) : List V → List V
  | x :: y :: rest => if x = a ∧ y = b then m :: mergeOnce a b m rest
                      else x :: mergeOnce a b m (y :: rest)
  | l => l

def Bpe.encode [DecidableEq V] (B : Bpe V) (bytes : List UInt8) : List V :=
  B.merges.foldl (fun toks r => mergeOnce r.1 r.2.1 r.2.2 toks) (bytes.map B.byteTok)

/-- The canonical tokenization: the one the tokenizer function returns. -/
def IsCanonical [DecidableEq V] (B : Bpe V) (bytes : List UInt8) (toks : List V) : Prop :=
  B.encode bytes = toks

end Dregg2.Crypto.Transducer
```

The asymmetry the hub's §3.1 item 3 names is visible in the types: `detok` is a function, so a
certificate for it has exactly one correct output per input. `IsTokenization` is a relation with
several inhabitants per byte string; only `IsCanonical` is functional, and it is defined through
`Bpe.encode`, which is a sequential algorithm over the merge list, not a finite-state run.

## 2. Certificate shape

**Detokenization (tokens → bytes).** Public `x = (vocabId, c_tok, c_byte)`: the name of the public
vocabulary table, the commitment to the token sequence, the commitment to the byte string. Witness
`w = (toks, bytes)` laid out as one row per OUTPUT BYTE: `(TOK, OFF, BYTE, LAST, TIDX)`, where `TOK`
is the current token id, `OFF` the offset inside it, `LAST` marks its final byte and `TIDX` counts
tokens. Each row is checked against the vocabulary table of rows `(token_id, i, byte_i, isLast_i)`.

Alternative when the vocabulary is committed rather than public: one map-op opening per token
against a vocabulary root (`token_id ↦ digest(vocab t)`), plus a re-hash of that token's bytes.

**Tokenization (bytes → tokens).** Public `x = (tokenizerId, c_in, c_out)` with `c_in` the byte
commitment and `c_out` the token commitment (the hub's naming). Witness: the detokenization trace
above (it proves `IsTokenization`) PLUS a canonicity certificate. Three shapes for the latter:
(a) replay `Bpe.encode` in the trace (one pass per merge rule); (b) a run of the Cognetta-Okazaki
canonical-tokenization transducer, one row per input byte; (c) a local canonicity test per adjacent
token pair, if a bigram-local characterization of canonical BPE holds for the deployed variant
[RECALLED from outside PRIOR-ART.md, unchecked; no number below depends on it].

## 3. Arithmetization and counts

Pinned primitives: table-routing DFA step 3 columns, 1 lookup, 4 constraints [MEASURED
`M/Circuit/Emit/DfaRoutingTableEmit.lean:540-543`]; Poseidon2 wide permutation 352 committed cells
[MEASURED `M/Circuit/Emit/Poseidon2RoundGates.lean:121` `POSEIDON2_AUX_COLS == 352`], narrow 141
[MEASURED `Poseidon2RoundGates.lean:833`]; map-op opening 16 chip rows per key at depth 16 [MEASURED
`M/Circuit/Emit/AttestedAutomatonEmit.lean:1201`].

**Commitment cost, exact form.** `bytes_to_lanes` packs two bytes per lane and prepends four 16-bit
length lanes [READ `R/sel4/dregg-pd/executor-pd/crypto-floor/src/field.rs:94-112`]; `hash_many_8`
absorbs at rate 4 and squeezes 8 lanes with one extra permutation [READ
`R/circuit/src/poseidon2.rs:410-435`]. So an 8-felt byte digest costs
`⌈(⌈n/2⌉ + 4)/4⌉ + 1` permutations, which is the hub's `~n/8` [INFERRED]. A felt-native token
digest (`hash_many_8` over one felt per token, length in the capacity lane, no length lanes) costs
`⌈T/4⌉ + 1` [INFERRED from `poseidon2.rs:377-394`].

**Detokenization AIR, per output byte** [INFERRED]:
- columns: `TOK, OFF, BYTE, LAST, TIDX` = 5;
- lookups: 1, the tuple `(TOK, OFF, BYTE, LAST)` into the vocabulary table (arity 4);
- constraints: `LAST·(1 − LAST) = 0`; `OFF' = (1 − LAST)·(OFF + 1)`; `(1 − LAST)·(TOK' − TOK) = 0`;
  `TIDX' = TIDX + LAST`; boundaries `OFF₀ = 0`, `TIDX₀ = 0`, `LAST_last = 1`,
  `TIDX_last + 1 = T`. That is 4 transition + 4 boundary + 1 Boolean = 9, max degree 2;
- permutations in the run: 0;
- table size: `B_V = Σ_t |vocab t|` rows (unpinned; depends on the vocabulary).

**Worked instance** (a 4 KiB output, assumed 4 bytes per token, so `n = 4096`, `T = 1024`;
the bytes-per-token ratio is an assumption, not a measurement):
- run: 4096 rows × 5 columns = 20,480 cells; 4096 vocabulary lookups;
- binding lookups (§4): 1024 `(TIDX, TOK)` routing lookups + 2048 lane-routing lookups;
- `c_byte`: `⌈(2048 + 4)/4⌉ + 1 = 514` permutations; `c_tok`: `⌈1024/4⌉ + 1 = 257`;
- commitments: `(514 + 257) × 352 = 271,392` cells, against 20,480 run cells: the hash is
  `271,392 / 20,480 ≈ 13.3×` the transducer, inside the hub's 4-15× band [INFERRED].

**Committed-vocabulary route** [INFERRED]: per token, one map-op read (16 chip rows at depth 16) plus
the token's byte digest (`⌈(4 + 4)/4⌉ + 1 = 3` permutations for a token of at most 8 bytes) = 19
permutations; for `T = 1024` that is 19,456 permutations = 6,848,512 cells, about 25× the
public-table route. A depth-16 map holds `2^16 = 65,536` keys (`AttestedAutomatonEmit` pins
`NKEYS == 2 ^ MAP_TREE_DEPTH` [MEASURED `:1212`]), so a vocabulary larger than 65,536 entries does not
fit the deployed depth.

**Multiplicity caveat** [READ census §1(b)4]: the deployed `exactPublicRows` table is a UNIT-capacity
LogUp receive. Detokenization reuses vocabulary rows (the same token appears many times), so the
1-lookup-per-byte figure needs a multiplicity-carrying lookup. Under the deployed carrier the
declared table must instead equal the run's own multiset of rows, which publishes the output. This
is the "Eulerian obstruction" of `DfaRoutingTableEmit`, and it applies to every table-lookup count in
this note.

**Tokenization** [INFERRED]: the detokenization cost above, plus canonicity:
- (a) merge replay: one pass per merge rule over the sequence, so `|merges| · n` rows; at a 50,000-rule
  merge list [RECALLED, GPT-2 size] and `n = 4096` that is about `2.0 × 10^8` rows. Not viable;
- (b) Cognetta-Okazaki transducer: 1 row and 1 lookup per input byte into the transducer's transition
  table; that table's size for a deployed vocabulary is unpriced here;
- (c) the bigram route, if it holds: 1 lookup per adjacent token pair, against a table of up to
  `V²` pairs. Unpriced.

## 4. Binding to the content commitment

- **Detokenization**: by shared witness cells, in the U3 sense. The token sponge's input lanes
  receive `(TIDX, TOK)` from exactly the rows with `LAST = 1` (one LogUp send per token, one receive
  per sponge input). The byte sponge's lanes receive `BYTE_{2j} + 256 · BYTE_{2j+1}` from consecutive
  rows (one routing lookup per two bytes), with the four length lanes pinned to `n`. Both digests
  appear as public inputs `c_tok`, `c_byte`. If the inference prover already commits the output
  tokens (U3), `c_tok` is that prover's witness and the token sponge is not paid again.
- **Tokenization**: the same two bindings, with the canonicity certificate reading the same `BYTE`
  and `TOK` columns.
- **Today**: NOT BOUND. There is no certificate. The zkOracle lexer's token stream is tied to the body
  bytes only because both Rust verifier legs run over the same authenticated body [INFERRED, census §5].

## 5. Soundness statement (Lean syntax) and its vacuity falsifier

```lean
open Dregg2.Crypto.Dfa (ContentScheme)

structure DetokStatement (DB DT : Type) where
  vocabId : String
  cByte   : DB      -- commitment to the byte string
  cTok    : DT      -- commitment to the token sequence

class DetokKernel (V DB DT : Type) (SB : ContentScheme UInt8 DB) (ST : ContentScheme V DT)
    (vocab : V → List UInt8) (Proof : Type) where
  verify      : DetokStatement DB DT → Proof → Bool
  extractable : Prop
  extract : extractable → ∀ st π, verify st π = true →
    ∃ toks bytes, ST.commit toks = st.cTok ∧ SB.commit bytes = st.cByte ∧ detok vocab toks = bytes

/-- Detokenization soundness: both commitments in the conclusion. -/
theorem detok_bound_sound [K : DetokKernel V DB DT SB ST vocab Proof] (hext : K.extractable)
    (st : DetokStatement DB DT) (π : Proof) (hacc : K.verify st π = true) :
    ∃ toks bytes, ST.commit toks = st.cTok ∧ SB.commit bytes = st.cByte ∧ detok vocab toks = bytes

structure TokStatement (DB DT : Type) where
  tokenizerId : String
  cIn  : DB         -- commitment to the input bytes
  cOut : DT         -- commitment to the output tokens

class TokKernel (V DB DT : Type) [DecidableEq V] (SB : ContentScheme UInt8 DB)
    (ST : ContentScheme V DT) (B : Bpe V) (Proof : Type) where
  verify      : TokStatement DB DT → Proof → Bool
  extractable : Prop
  extract : extractable → ∀ st π, verify st π = true →
    ∃ bytes toks, SB.commit bytes = st.cIn ∧ ST.commit toks = st.cOut ∧
      detok B.vocab toks = bytes ∧ B.encode bytes = toks

/-- Tokenization soundness: the token sequence behind `cOut` is THE tokenization of the bytes behind
`cIn`, not merely a tokenization. -/
theorem tok_bound_sound [DecidableEq V] (B : Bpe V) [K : TokKernel V DB DT SB ST B Proof]
    (hext : K.extractable) (st : TokStatement DB DT) (π : Proof) (hacc : K.verify st π = true) :
    ∃ bytes toks, SB.commit bytes = st.cIn ∧ ST.commit toks = st.cOut ∧
      detok B.vocab toks = bytes ∧ B.encode bytes = toks
```

The named-record form (as `Dfa.dfa_bound_identifies_record_or_collides`, `M/Crypto/Dfa.lean:294`):
for a record `bytes₀` with `SB.commit bytes₀ = st.cIn`, the extracted `bytes` equals `bytes₀` or is a
different preimage of the same commitment. The AIR-level obligation (L3) is
`Satisfied2Public hash (detokDesc vocabTbl) … t → detok vocab (tokCol t) = byteCol t`, with `htbl`
saying every table row is `(t, i, (vocab t)[i], decide (i + 1 = |vocab t|))`, as
`tableRouting_refines_classify` does for DFAs (`DfaRoutingTableEmit.lean:438`).

**Falsifier** (a non-canonical tokenization accepted by a checker that forgets canonicity):

```lean
def toyB : Bpe Nat :=
  { vocab   := fun | 0 => [97] | 1 => [98] | 2 => [97, 98] | _ => []
    byteTok := fun b => if b = 97 then 0 else 1
    merges  := [(0, 1, 2)] }

example : detok toyB.vocab [0, 1] = [97, 98] := by decide     -- "a","b" detokenizes to "ab"
example : toyB.encode [97, 98] = [2]          := by decide     -- the canonical tokenization is ["ab"]
example : toyB.encode [97, 98] ≠ [0, 1]       := by decide     -- so [a, b] is NOT canonical
```

A checker of shape `IsTokenization` (detokenization run only, the cheap certificate) accepts
`(c_in = commit "ab", c_out = commit [0, 1])`. `tok_bound_sound`'s conclusion requires
`B.encode bytes = toks` and refutes it. The detokenization statement is not weakened by this: for
`detok_bound_sound` the pair is CORRECT (`[0, 1]` does detokenize to `"ab"`), which is why U3 can use
detokenization without canonicity.

## 6. Composition behaviour

- **Fusion into an inference trace (U3)**: detokenization fused into the output boundary: `+1`
  vocabulary lookup per output byte, and a policy DFA over the `BYTE` column adds one table-routing
  lane (3 cells, 1 lookup per byte). No second token commitment.
- **Pre-image composition (cheaper U3)** [INFERRED]: a byte-level policy DFA `d` composed with
  `detok` is a token-level DFA, `δ'(q, t) = classifyFrom d q (vocab t)`. Then the policy costs
  1 lookup per TOKEN and no byte commitment at all, against a table of `|Q| · V` rows (64 states ×
  50,257 tokens = 3,216,448 rows; the vocabulary size is [RECALLED]). The table's agreement with `d`
  is a per-table check of `|Q| · V` entries, far past kernel `decide`; it is a native check.
- **Transducer chain** `T₂ ∘ T₁`: one proof with the intermediate word as a hidden column. Not
  order-commutative. Tokenization is not functional unless canonicalized (hub §3.1 item 3).
  Pre-tokenization (a regex split before BPE) is a second transducer in the chain and must be in the
  statement, or `B.encode` is the wrong function.
- **Product with a DFA, concatenation, star**: inherited through the composed DFA above.
  Complement: only for the composed token-level DFA (complement of the policy, not of the transducer).
- **ε-additivity fails** when the two commitments `c_in`, `c_out` come from different provers: L4's
  `ε_inf + ε_c + ε_bridge`, plus `bindAdv` for each scheme (L1, L5).

## 7. Prior art

- Cognetta, Okazaki, *Tokenization as Finite-State Transduction*, CL 2025, arXiv 2410.15696 [READ in
  PRIOR-ART §4]: transducers for BPE and WordPiece that encode all and the canonical tokenizations.
- Berglund, van der Merwe, *Formalizing BPE Tokenization*, NCMA 2023, arXiv 2309.08715 [READ in
  PRIOR-ART §4]: the SentencePiece and HuggingFace semantics differ; a string-to-string transducer
  tokenizes left to right.
- zkLLM (Sun, Li, Zhang, CCS 2024, arXiv 2404.16109) and NanoZK (arXiv 2603.18046) [READ in
  PRIOR-ART §4]: inference proofs that start at the token or tensor level.
- PRIOR-ART §4 records no hit for a ZK or verifiable proof that bytes tokenize to tokens, with the
  four listed queries. "No hit" is not "none exists".

Not claimed as ours: the transducer constructions (Cognetta-Okazaki) and the BPE semantics
(Berglund-van der Merwe).

## 8. Built vs proposed

| object | where | rung |
|---|---|---|
| `Mealy`, `detok`, `Bpe.encode`, `IsCanonical` | proposed | none |
| `detok_bound_sound`, `tok_bound_sound` | proposed | L0 (statement only) |
| detokenization AIR (5 columns, 1 lookup, 9 constraints per byte) | proposed | none |
| JSON lexer `cfg.rs:215 tokenize` | `R/zkoracle-prove/src/cfg.rs:215` | unverified Rust, no Lean twin |
| canonical tokenization certificate | proposed; route (b) unpriced | none |

**Milestone**: `M/Crypto/Transducer/Detok.lean` at L2: the definitions above, the three `toyB`
`decide` facts as the falsifier, `detok_bound_sound` derived from its kernel, and a `#guard` that
pins the worked instance's bill: 4096 run rows, 4096 vocabulary lookups, `514 + 257 = 771`
commitment permutations.
