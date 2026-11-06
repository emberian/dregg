# Symbolic automata and Boolean-closed Brzozowski derivatives — arithmetization note (2026-11-05)

Tags: [READ] seen at file:line; [MEASURED] a pinned #guard or a run; [CLAIM] asserted elsewhere; [INFERRED] derived here.

Hub: `AUTOMATA-ARITHMETIZATION-PROGRAM.md` §2 row "symbolic / predicate automata". Algebra:
`zkml-research/docs/CERTIFICATES.md` L0, L3, P4. M = `/Users/ember/dev/breadstuffs/metatheory/Dregg2`.

The family's job in the zoo: it is the only one with native complement and intersection in the
syntax, so it is where absence certificates (L3) come from. The derivative tower is proved in Lean
over the `Value` alphabet; the deployed byte compiler is Rust and is not proved against it. Most of
this note is about that gap and about the one composition rule (padding) that the proofs do not enforce.

## 1. Semantics object (Lean)

Syntax, `M/Crypto/Deriv/Core.lean:41` [READ], verbatim (doc comments elided):

```lean
inductive PredRE where
  | ε
  | sym   (φ : Pred)
  | alt   (l r : PredRE)
  | inter (l r : PredRE)
  | cat   (l r : PredRE)
  | star  (r : PredRE)
  | neg   (r : PredRE)
  deriving Repr
```

`abbrev bot : PredRE := .sym .ff` (:61) and `abbrev any : PredRE := .sym .tt` (:64) [READ]. There is
no empty-language constructor and no lookarounds.

Operational semantics, `Core.lean:157` [READ]:

```lean
@[simp] def derives : List Value → PredRE → Bool
  | [],      R => null R
  | a :: as, R => derives as (der a R)
```

with `der a (.neg r) = .neg (der a r)` and `der a (.inter l r) = .inter (der a l) (der a r)` (:143-153).
Denotational semantics: `Core.lean:267 def Matches : List Value → PredRE → Prop`, with
`| w, .neg r => ¬ Matches w r` and `| w, .inter l r => Matches w l ∧ Matches w r` [READ].

The theorems that make it a semantics object, verbatim [READ]:

- `M/Crypto/Deriv/Correctness.lean:103`
  `theorem derives_neg (w : List Value) (r : PredRE) : derives w (.neg r) = !(derives w r)`
- `Correctness.lean:267`
  `theorem correctness (w : List Value) (R : PredRE) : derives w R = true ↔ Matches w R`
- `M/Crypto/Deriv/Finiteness.lean:347`
  `theorem der_finite {r : PredRE} : ∃ (xs : List PredRE), ∀ {n : Nat}, steps r n ⊆[ (· ≅ ·) ] xs`
  (finite up to ACI similarity `≅`, over the satisfiability-free symbolic `step`; the witness is
  `⊕(pieces r)`, an existential with no pinned size).
- `M/Crypto/Deriv/TableDfa.lean:133`
  ```lean
  theorem tableDfa_faithful (td : TableDfa PredRE Value) (R : PredRE)
      (hagree : ∀ w, td.accepts w ↔ derives w R = true) :
      ∀ w, td.accepts w ↔ Matches w R
  ```
  Its proof is `rw [hagree w, correctness]`. **The premise `hagree` is the whole obligation**: the
  theorem says a table that already agrees with `derives` on every word agrees with `Matches`. It
  does not say any table does. `Thompson.lean:136 tableDfa_faithful'` generalizes the state type.
- `M/Crypto/Deriv/Powerset.lean:108 structure DerivDeterminizer (State : Type) (R : PredRE)` with
  fields `td : TableDfa State Value`, `decode : State → PredRE`,
  `start_spec : LangEquiv (decode td.start) R`,
  `step_spec : ∀ s a, LangEquiv (decode (td.step s a)) (der a (decode s))`,
  `accept_spec : ∀ s, td.accept s ↔ null (decode s) = true`; and `Powerset.lean:150`
  `theorem determinizer_faithful (D : DerivDeterminizer State R) (w : List Value) : D.td.accepts w ↔ Matches w R`
  [READ]. This structure discharges `hagree` (`accepts_derives`, :139). It is the contract
  `dfa/src/derivative.rs::Re::compile` would need. The docstring at Powerset.lean:105-107 says the Rust
  "satisfies [it] by construction"; that sentence is a [CLAIM]. **Nothing proves the Rust meets it.**

### The alphabet split

| side | symbol | leaf | file |
|---|---|---|---|
| Lean tower | `Dregg2.Exec.Value` (a record frame) | `Pred` over record fields (`symEq f s`, `symMemberOf f set`, `digEq`, `fieldEqField`, ...), evaluated as `leaf φ a = φ.eval (symbolOld a) a` | `Deriv/Core.lean:118`; `Exec/PredAlgebra.lean:127` [READ census] |
| Rust compiler | `u8` | `ByteClass { ranges: Vec<(u8, u8)> }` (sorted, disjoint, merged) | `dfa/src/derivative.rs:53`, `enum Re` at `:189` with an explicit `Empty` arm [READ] |

The Lean tower has no byte-class leaf. `InjectionGuardCircuit.lean`'s header calls the shipped byte
guard a "RE-IMPLEMENTATION, not a call into Lean" [READ census]. So `determinizer_faithful` cannot even
be *stated* about the Rust table until a byte instance exists. Proposed (not in the tree):

```lean
/-- A byte as a one-field frame, so byte words are `Value` words. -/
def byteFrame (b : Fin 256) : Value := .record [("b", .sym b.val)]

/-- `ByteClass` as a leaf: membership of field "b" in a finite set. -/
def byteClassPred (s : List (Fin 256)) : Pred := .symMemberOf "b" (s.map (·.val))

/-- The byte-alphabet contract: quantifies over the 256 frames only, so `step_spec` is decidable. -/
structure ByteDeterminizer (R : PredRE) where
  step   : Nat → Fin 256 → Nat
  start  : Nat
  accept : Nat → Bool
  decode : Nat → PredRE
  start_spec  : LangEquivOn byteFrame (decode start) R
  step_spec   : ∀ s b, LangEquivOn byteFrame (decode (step s b)) (der (byteFrame b) (decode s))
  accept_spec : ∀ s, accept s = null (decode s)
```

where `LangEquivOn f X Y := ∀ w : List (Fin 256), derives (w.map f) X = derives (w.map f) Y`.
(The `symMemberOf` constructor name is from the census of `PredAlgebra.lean:127`; its argument order
is unchecked here.)

## 2. Certificate shape

The derivative automaton is compiled once per regex into a table DFA; the per-word certificate is
then the DFA certificate of `01-dfa.md`. So there are two certificates with different owners:

| certificate | prover supplies | public `x` | witness `w` | checked |
|---|---|---|---|---|
| **compile certificate** (per regex, offline) | the table `step : Q × Σ → Q`, accept bits, and `decode : Q → PredRE` (the residual per state) | `R`, the table (or its commitment) | none (all public) | per entry: `aciNorm (decode (step s a)) = aciNorm (der a (decode s))` for every state `s` and every alphabet class `a`; per state: `accept s = null (decode s)`; `decode start ≅ R` |
| **run certificate** (per word) | the replay rows `(state, sym, next)` | the table, `c`, the final verdict | the word `w` (the SYMBOL column) | the DFA AIR (`01-dfa.md`) |

The compile certificate is translation validation in the sense of Jourdan, Pottier and Leroy (§7):
it checks the output of an untrusted compiler instead of proving the compiler. Over bytes it is a finite
check, `|Q|·256` derivative computations (or `|Q|·k` over `k` minterm classes), because `step_spec` is
then quantified over a finite alphabet. It requires the ACI normalizer to be sound (`≅ → LangEquiv`);
`AciNormal`/`AciComplete` exist in `Deriv/` [READ census, headers only].

For a symbolic (non-byte) alphabet the deployed route is the minterm encoding:
`M/Crypto/GuardToAutomatonCircuit.lean:282` [READ]

```lean
theorem guardDfa_decides (G : GuardAut C) (w : List Value) :
    G.guardDfa.accepts (classifyFrom G.guardDfa G.guardDfa.start (w.map (enc C)))
      ↔ derives w G.root = true
```

The circuit reads `w.map (enc C)` (minterm indices, `enc` at :247), not `w`. That is a
letter-to-letter projection, and it matters for §4.

The content commitment `c` commits the word the record holds: bytes for the byte guard, `Value`
frames for the record-level guard. In the minterm route the circuit's SYMBOL column holds `enc C a`,
not `a`, so `c` and the run do not range over the same alphabet.

## 3. Arithmetization and counts

The run is the DFA run. Pinned costs from `01-dfa.md` and the census:

| shape | cols | constraints | lookups / symbol | perms / symbol | source |
|---|---|---|---|---|---|
| table routing | 3 | 4 | 1 table (arity 3) | 0 | [MEASURED `DfaRoutingTableEmit.lean:540-543`: `traceWidth == TRT_WIDTH` (3), `constraints.length == 4`, `tables.length == 1`] |
| hash-chained routing (injection DFA, 3 states, 2 symbols) | 22 | 14 | 2 chip (arity 4 + arity 2) | 2 | [MEASURED `DfaRoutingGeneralEmit.lean:272-278`] |

What the derivative family adds is the table, not rows. Table size is `|Q| · |Σ|` rows for a flat
table, or `256 + |Q|·k` with a byte-to-class lookup first (`k` = minterm classes), at the price of a
second lookup per symbol [INFERRED]. Worked instance, the padded complement of `{{` over bytes,
`neg (any* · "{{" · any*)`: residual states {clean, saw-one-brace, found}, where found is the
absorbing rejecting state, so `|Q| = 3` and
`k = 2` classes (`{`, other) [INFERRED by hand from the derivatives; the Lean twin is the 3-state
injection DFA of `DfaRoutingGeneralEmit`, which matches]. Flat table: `3 · 256 = 768` rows; class form:
`256 + 3 · 2 = 262` rows and 2 lookups per byte [INFERRED].

`|Q|` for intersection is bounded by `der_finite` but the bound is existential (`⊕(pieces r)`), not a
number; the census records the related `emptinessBound` as past kernel reach. Intersection of two
derivative automata can be built either as one `inter` table (`|Q| ≤ |Q₁|·|Q₂|` reachable residuals)
or as a `k`-lane product witness with the tables kept separate (`TinyAutomataLanesK`, hub §3 "product").
The second keeps tables at `|Q₁|·|Σ| + |Q₂|·|Σ|` rows and pays `k` lookups per symbol [INFERRED].
Measured area for the `prodI k` family: `[some 12, some 36, some 72, some 150]` at `k = 1..4`
[MEASURED `AttestedAutomatonEmit.lean:1171-1212`, the `costOf (tableRoutingDesc "wg" (reachTable (prodI k) 24))` guard].

**Commitment cost** (shared by every statement over the same `c`): `n/8` Poseidon2 permutations for
`n` bytes (rate-4 absorb, 2 bytes per lane, 4 length lanes) = 44 committed cells per byte at the
352-cell wide permutation [READ `circuit/src/poseidon2.rs:704`; `sel4/dregg-pd/executor-pd/crypto-floor/src/field.rs:94`;
MEASURED `Poseidon2RoundGates.lean` `#guard POSEIDON2_AUX_COLS == 352`]. Against the 3-cell table-routing
row that is ~15× [INFERRED: 44/3]; against the 22-cell hash-chained row, 2× [INFERRED: 44/22]. The
compile certificate is paid once per regex, offline, and has no per-byte cost.

## 4. Binding to the content commitment

**NOT BOUND in any derivative theorem.** `tableDfa_faithful`, `determinizer_faithful` and `guardDfa_decides`
quantify over words; they are language facts, which is correct for them. The binding has to come from
the run certificate (`01-dfa.md`), whose abstract form now carries `c` (`Dfa.lean:249 BoundStatement`,
`:273 dfa_bound_verify_sound`) [READ]. Two family-specific wounds sit between them:

1. **Alphabet.** The run reads bytes or minterm indices; the derivative theorems are about `Value` words.
   For bytes the gap is `byteFrame` (§1). For the minterm route, `c` must commit `w` and the circuit
   must compute `enc C` per frame in-circuit (a lookup `(frame-signature, index)`), or `c` must commit
   `w.map (enc C)` and the statement then is about the encoded word, which is weaker: two records with
   the same minterm word are indistinguishable to it. That is sound for the guard (`derList_enc`
   shows the guard cannot tell them apart either), but a consumer conjoining another statement over
   the same `c` (L1) needs the unencoded word.
2. **Padding.** L3 holds only for the padded pattern. Nothing in the run certificate checks that the
   regex in the statement is of the form `neg (any* · P · any*)`. That check belongs in the statement
   (the verifier recomputes the table from `P`, or the statement names `P` and the table is a function
   of it), not in the prover.

## 5. Soundness statement (Lean syntax) and its vacuity falsifier

Proposed, composing what exists (`dfa_bound_verify_sound`, `tableRun_dfaAccepts`, `determinizer_faithful`)
with one missing lemma:

```lean
/-- Missing lemma: over a functional δ, an accepting relational trace IS the table run. -/
theorem dfaAccepts_functional_eq_runTrace (td : TableDfa State Sym)
    (trace : List (Step State Sym)) (h : DfaAccepts td.δ td.start td.accept trace) :
    ∃ a as, traceWord trace = a :: as ∧ trace = runTrace td td.start (a :: as)

/-- The derivative certificate, content-bound. -/
theorem derivCert_bound_sound {State D Proof : Type} {S : ContentScheme Value D} {R : PredRE}
    (Det : DerivDeterminizer State R)
    [K : DfaBoundVerifierKernel State Value D S Proof]
    (hext : K.extractable) (stmt : BoundStatement State Value D)
    (hδ : stmt.δ = Det.td.δ) (hq : stmt.q₀ = Det.td.start) (hacc : stmt.accept = Det.td.accept)
    (proof : Proof) (haccept : K.verify stmt proof = true) :
    ∃ w : List Value, S.commit w = stmt.c ∧ w ≠ [] ∧ Matches w R

/-- The absence corollary, with the padding in the statement, not in the prose. -/
def AbsentIn (w : List Value) (P : PredRE) : Prop :=
  ∀ i j, i ≤ j → j ≤ w.length → derives ((w.take j).drop i) P = false

def padNeg (P : PredRE) : PredRE := .neg (.cat (.star .any) (.cat P (.star .any)))

theorem absent_iff_padded_complement (w : List Value) (P : PredRE) :
    AbsentIn w P ↔ derives w (padNeg P) = true

theorem absenceCert_bound_sound ... (Det : DerivDeterminizer State (padNeg P)) ... :
    ∃ w : List Value, S.commit w = stmt.c ∧ AbsentIn w P
```

`derivCert_bound_sound` meets L0: `c` and the word are in the conclusion. `AbsentIn` uses
`take`/`drop` rather than a `slice` function so that it reads in core Lean. Its proof is
`dfa_bound_verify_sound` → `dfaAccepts_functional_eq_runTrace` → `tableRun_dfaAccepts` (`TableDfa.lean:110`)
→ `determinizer_faithful`. The `w ≠ []` conjunct is there because `DfaAccepts` needs a non-empty trace;
the empty record is the `PiBinding` boundary case of `Dfa.lean`.

**Falsifier: the whole-word complement trap (CERTIFICATES P4), as `#guard`s.** These belong in
`Deriv/Core.lean` next to the existing guards at :309-349, because `frameK7`, `frameK9` and `isK7` are
`private` there:

```lean
-- the record [k9, k7, k9] CONTAINS a k7 frame at slice [1, 2)
#guard PredRE.derives [frameK7] (.sym isK7) = true
-- ... yet the whole-word complement `neg P` ACCEPTS it: the trap
#guard PredRE.derives [frameK9, frameK7, frameK9] (.neg (.sym isK7)) = true
-- the padded complement REFUSES it
#guard PredRE.derives [frameK9, frameK7, frameK9]
         (.neg (.cat (.star .any) (.cat (.sym isK7) (.star .any)))) = false
-- and ADMITS a record that really lacks a k7 frame (the padded form is not just `bot`)
#guard PredRE.derives [frameK9, frameK9]
         (.neg (.cat (.star .any) (.cat (.sym isK7) (.star .any)))) = true
```

As a theorem: `whole_word_complement_is_not_absence : ∃ w P, derives w (.neg P) = true ∧ ¬ AbsentIn w P`,
witnessed by `w := [frameK9, frameK7, frameK9]`, `P := .sym isK7`, `i := 1`, `j := 2`. A certificate
system that accepts `neg P` as an absence statement meets the first two guards and is refuted by the third.

A second falsifier, aimed at the compile certificate: take the 768-entry byte table for
`padNeg "{{"` (states clean, saw-one-brace, found; the first two accept) and flip one entry,
`step clean 'x' := saw-one-brace`. The mutant rejects `"x{"`, which contains no `{{`. The checker of §2
must reject the mutant, because `decode saw-one-brace` is not `≅` to `der 'x' (decode clean)`. A checker
that compares only the accept bit of the target state passes it (both states accept). That is exactly
the hole that `hagree` hides.

## 6. Composition behaviour

| operator (hub §3) | here | note |
|---|---|---|
| product / intersection | native: `inter` is a derivative constructor; or a `k`-lane product witness | one proof, no `b` term |
| complement | native: `neg`; the table swaps accept bits (`| .neg r => !(null r)`, Core.lean:134) | **absence needs `padNeg`**; whole-word `neg` is not absence (L3) |
| concatenation, star | native (`cat`, `star`); `der a (star r) = cat (der a r) (star r)` | finite by `der_finite` |
| weld to `c` | via the DFA run certificate | the alphabet wound of §4 is specific to this family |
| MMR aggregation | Count=0 over a corpus is L2 ∘ L3: `N` absence certificates plus `N` MMR openings, error `N·ε + b_M + b` | |
| fusion (U3) | the table is fused into another prover's output cells | `+1` lookup per output cell; the detokenizer is the real price (`06`) |

Where additivity fails for this family specifically: two derivative certificates over one `c`, one
over the record's bytes and one over its minterm encoding, are not conjoinable by L1 alone, because the
second's extractor returns `w.map (enc C)`, not `w`; the conjunction needs the encoding computed
in-circuit (§4.1) or a morphism (L5).

## 7. Prior art

- Stanford, Veanes, Bjørner, *Symbolic Boolean Derivatives for Efficiently Solving Extended Regular
  Expression Constraints*, PLDI 2021 [SNIPPET]: derivatives of symbolic EREs with complement and
  intersection over an arbitrary character theory.
- Zhuchko, Veanes, Ebner, *Lean Formalization of Extended Regular Expression Matching with Lookarounds*,
  CPP 2024 [SNIPPET]; and *Finiteness of Symbolic Derivatives in Lean* [SNIPPET]. `Deriv/` is a
  re-instantiation of that ERE≤ development (its own headers say so: "ERE≤'s `RE α` minus the four
  lookarounds").
- Nipkow, Traytel, *Unified Decision Procedures for Regular Expression Equivalence*, ITP 2014 [READ];
  Coquand, Siles, CPP 2011 [RECALLED]: verified derivative-based deciders, without complement.
- Reef (ePrint 2023/1886) [cited in CERTIFICATES §6]: ZK proofs that a committed document matches or
  does not match a regex. Crepe (arXiv 2504.01198) [READ]: ZK regex equivalence via derivatives.
- Jourdan, Pottier, Leroy, *Validating LR(1) Parsers*, ESOP 2012 [SNIPPET]: the translation-validation
  pattern §2 applies to the derivative compiler.

Not claimed as ours: derivatives with complement (Brzozowski; Stanford et al.), their finiteness in
Lean (Zhuchko et al.), and ZK absence over a committed document (Reef). What the notes may say is ours
(hub §6): machine-checked complement compilation, of which `determinizer_faithful` is the Value-alphabet
half and the byte half is not done.

## 8. Built vs proposed

| object | where | rung |
|---|---|---|
| `PredRE`, `derives`, `Matches` | `Deriv/Core.lean:41, 157, 267` | L1 |
| `derives_neg`, `correctness` | `Deriv/Correctness.lean:103, 267` | L1 |
| `der_finite` | `Deriv/Finiteness.lean:347` | L1 (size unpinned) |
| `tableDfa_faithful` (premise `hagree` = the obligation) | `Deriv/TableDfa.lean:133` | L1 |
| `DerivDeterminizer`, `determinizer_faithful` | `Deriv/Powerset.lean:108, 150` | L1, Value alphabet only |
| `guardDfa_decides` (minterm route) | `GuardToAutomatonCircuit.lean:282` | L1; `nodb_pipeline` (:440) is L2 at `hash0` |
| Rust `Re::compile` | `dfa/src/derivative.rs:560` | L4 deployed, **unproved**; ACI canonical form since 2026-11-06 (below) |
| `byteFrame`, `ByteDeterminizer`, compile-certificate checker | proposed | L0 |
| `dfaAccepts_functional_eq_runTrace`, `derivCert_bound_sound`, `absent_iff_padded_complement` | proposed | L0 |
| whole-word trap guards | proposed (Core.lean) | L0 → L2 when the four `#guard`s land |

**Rust-side status (2026-11-06).** Until this date `Re::compile` did not terminate on padded
complements: `~(any* · "AKIA" · any*)` ran 60 s without finishing [MEASURED, lane C], because `Re::or`
normalized commutativity and idempotence of its top pair only, so derivatives that `der_finite` identifies up
to ACI similarity stayed distinct. The smart constructors now keep an ACI canonical form (flattened, sorted,
deduplicated `|` and `&` chains, right-associated `·`, `∅`/`any*` units and absorbers, `~~r = r`; invariant on
`enum Re`, `dfa/src/derivative.rs:189`; Owens, Reppy and Turon 2009). Measured: `~(any*·AKIA·any*)` 5 states,
its conjunction with `~(any*·-----BEGIN·any*)` 14, demo (a)'s two-pattern policy 4,577 states, 129 after
`Dfa::minimize` (`dfa/src/compiler.rs:147`), the same table byte for byte as the demo's former interim compiler
(`demo/absence-receipt/tests/differential.rs`). That is differential evidence; the normalizer is not proved
to meet Lean's similarity, and the milestone below is still the first statement about a Rust table.

**Milestone:** a Lean checker `checkByteTable : PredRE → FlatTable → (Nat → PredRE) → Bool` with
`checkByteTable R tbl dec = true → ByteDeterminizer R`, run as `#guard` on the table the Rust
`Re::compile` emits for `padNeg "{{"`: `3 · 256 = 768` step checks return `true`, and the one-entry
mutant of §5 returns `false`. Rung L2. This is the first statement in the tree that says something
about a table the Rust compiler produced.
