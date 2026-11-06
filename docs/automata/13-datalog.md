# Datalog: derivation firings (built) and least-fixpoint certificates with exact Count (Part D, landed) — arithmetization note (2026-11-05)

Tags: [READ] seen at file:line; [MEASURED] a pinned `#guard` or a run; [CLAIM] asserted elsewhere;
[INFERRED] derived here. Metatheory root `M = /Users/ember/dev/breadstuffs/metatheory/Dregg2`.

## 1. Semantics object (Lean)

Landed today [READ `M/Datalog/FixpointCert.lean`]:
```lean
inductive Term | var (i : Nat) | const (c : ℤ)
structure Atom where pred : Nat; args : List Term
structure Rule where head : Atom; body : List Atom
abbrev Fact := Nat × List ℤ;  abbrev Program := List Rule;  abbrev Subst := List ℤ
def activeDomain (P : Program) (edb : List Fact) : List ℤ   -- constants of the EDB and the program
def substs (dom : List ℤ) : Nat → List Subst                 -- dom^n, executable

inductive Derives (P : Program) (edb : List Fact) : Fact → Prop
  | edb {f} : f ∈ edb → Derives P edb f
  | fire {r s h} : r ∈ P → s ∈ substs (activeDomain P edb) (varBound r) →
      (∀ b ∈ r.body, (applyAtom s b).isSome = true) →
      (∀ b ∈ r.body, ∀ f, applyAtom s b = some f → Derives P edb f) →
      applyAtom s r.head = some h → Derives P edb h
```
This is the **active-domain (finite Herbrand) least fixpoint**: rule substitutions range over the
constants of the EDB and the program. For safe (range-restricted) programs it is the standard
semantics; the coincidence theorem is a named follow-up and is NOT claimed in the file. The
single-firing AIR that already exists, `M/Circuit/Emit/DerivationEmit.lean`, has no Lean semantics
object of its own: it transcribes the hand AIR's 28 constraint families and proves one gate lemma
[READ header].

## 2. Certificate shape

Public `x = (program, root, pred, count)`: the program, the MMR root of the length-prefixed
flattening of the EDB (`flatten`, injective, `flatten_injective`), the counted predicate, the
claimed count. Witness `w = (edb, trace)`: the EDB itself (it is committed, not hidden: the
statement is about a public log) and a **semi-naive trace**: rounds of firings
`⟨rule index, substitution⟩`. The verifier replays the trace (each firing's instantiated body must
already be present; its substitution must be admissible: exactly `varBound r` values, all in the
active domain), checks **closure** (for every rule and every admissible substitution, if the body
holds the head is present — an executable enumeration of `|P| · |dom|^{vars}` candidates), and
compares the count.

The trace is the semi-naive evaluation's own log (Soufflé provenance, Zhao-Subotić-Scholz
[READ prior art]), so an honest prover produces it at zero extra cost; the derivation-tree
certificate of Tantow et al. (ITP 2025) [READ] certifies "these facts are entailed" (soundness
only); the closure leg is what makes "and no others" (exactness of Count) a statement.

## 3. Arithmetization and counts

L2 (this landing) is native: counts are checker steps.

| leg | cost | source |
|---|---|---|
| root recompute | one MMR fold over `flatten edb` (`2 + arity` felts per fact), `≈ |flat|` sponge calls of arity 2 in the model | [READ `MMR.lean:402 mroot`] |
| replay | per firing: `|body|` membership tests + 1 `addFact`; transitive closure over 4 nodes: 6 firings in 3 rounds | [MEASURED `#guard`: 9 facts after replay, `countQ … PATH = 6`] |
| closure | `|P| · |dom|^{varBound r}` body evaluations once: the 4-node instance has `|dom| = 6`, `rStep` has 3 variables, so 216 substitutions for `rStep` and 36 for `rBase` | [MEASURED `#guard (substs … (varBound rStep)).length == 216`, `(activeDomain tc edb).length == 6`] |

L3 (proposed): iterate `DerivationEmit` (one firing = 386 columns, 393 constraints, 13 PIs,
degree 8 [MEASURED `DerivationEmit.lean` pins]) under a fold, one descriptor instance per firing,
with the running fact table as a `MapOp`-committed sorted map (each body atom = one map-op read =
16 chip rows at depth 16 [MEASURED `AttestedAutomatonEmit` aux bill]); closure in-circuit is the
expensive leg: `|P| · |dom|^{vars}` body evaluations, each `|body|` map-op reads. For `|dom| = 2^10`
and 3 variables that is `2^30 · |body|` openings — **closure does not arithmetize naively**; the
honest L3 shape is: prove closure by a SORTED-ENUMERATION argument per rule (sort the candidate
heads, show the sorted candidate list equals the sorted present list at the counted predicate,
one lookup per candidate), which is `|dom|^{vars}` lookups, not map-op openings. That number is
the Count's price of exactness, and the program doc §3 names it as the place alternation does not
help.

Content commitment: the EDB is the committed object; `flatten` costs `2 + arity` felts per fact;
at 2 bytes per lane the per-byte law of the hub does not apply (facts are felts, not bytes).

## 4. Binding to the content commitment

`st.root = mroot hash (flatten c.edb)`, recomputed by the verifier. `edb_bound_or_collides`: two
accepted certificates for one root have the same EDB or `MRootColl hash (flatten e₁) (flatten e₂)`
(the sponge collides at the pair `mrootFind` names; `MMR.mroot_binds_or_collides`, floor-free, no
`Poseidon2SpongeCR`). The flattening is injective, so the collision is in the sponge, never in the
encoding.

## 5. Soundness statement (Lean syntax) and vacuity falsifier

Landed [READ `FixpointCert.lean` §5]:
```lean
theorem verify_sound (hash : List ℤ → ℤ) (st : Statement) (c : Certificate)
    (h : verify hash st c = true) :
    mroot hash (flatten c.edb) = st.root ∧
    ∃ db : List Fact, db.Nodup ∧
      (∀ f, f ∈ db ↔ Derives st.program c.edb f) ∧
      countQ db st.pred = st.count

theorem count_unique_or_collides (hash) (st₁ st₂ : Statement) (c₁ c₂ : Certificate)
    (hP : st₁.program = st₂.program) (hR : st₁.root = st₂.root) (hp : st₁.pred = st₂.pred)
    (h₁ : verify hash st₁ c₁ = true) (h₂ : verify hash st₂ c₂ = true) :
    st₁.count = st₂.count ∨ MRootColl hash (flatten c₁.edb) (flatten c₂.edb)
```
Law L0 met: the statement carries the root and the conclusion names the committed EDB. The second
theorem is the exact-Count statement without a prover: Count is a function of `(program, root,
pred)`.

Falsifiers [MEASURED, kernel-evaluated `#guard`s in `Reference`]:
- the honest 3-round trace verifies at `count = 6`;
- the OPEN trace (2 rounds) is refused at `count = 6` AND at `count = 5`, the number it did
  derive: **closure is the gate, not the count** — a checker that counts what the prover bothered
  to derive is caught;
- `count = 5` and `count = 7` with the honest trace are refused;
- a firing whose body does not hold (`rStep` at `[1, 3, 4]`, no `edge(1,3)`) makes `replay` return
  `none`;
- a substitution outside the active domain is refused, isolated on the unsafe rule `p(X) :- q()`
  (whose body holds for every `X`), so only the domain check can refuse `X := 9`;
- the closure-forgetting checker `verifyNoClosure` ACCEPTS the open trace at count 5 while
  `verify` refuses it: the weaker checker's acceptance is exhibited;
- a wrong root is refused.
Non-vacuity of the semantics: `path14_derives : Derives tc edb (PATH, [1, 4])` as a term.

What is NOT claimed: coincidence with the unrestricted fixpoint for safe programs; stratified
negation (a `¬` body atom needs the closed-world leg: absence of the negated fact in the FINAL
database, which is a statement about closure of the lower stratum — the shape is the same gate,
run per stratum, and is the first extension); an executable extractor for the trace (the trace is
supplied, not extracted: there is no proof system here yet).

## 6. Composition behaviour

- **MMR aggregation (L2)**: the EDB is already a committed log; appending receipts changes the root
  and the certificate must be re-run (semi-naive evaluation resumes from the previous fixpoint; the
  trace certificate for the delta is a follow-up that `dregg-query`'s CALM classification makes
  precise: positive Datalog is monotone, so the old facts stay and only the delta's rounds are new).
- **Conjunction with absence (L3)**: `Count = 0` over a corpus is this certificate at `count := 0`
  with a program whose head fires on a match; exactness is what turns "no match reported" into
  "no match exists".
- **Error accounting** (codex round 2 §1e, adopted): native verification has proof-system error 0
  for its relation on the supplied EDB; identifying that EDB with the intended committed one costs
  `b_EDB`. A STARK over the whole checker carries `ε_STARK(q) + b_EDB(q)` — ONE `ε`, not one per
  firing (the trace is one witness). Conjunction with another certificate: `ε₁ + ε₂ + b_EDB`; over
  `N` records: `Σ εᵢ + b_MMR` (no separate content term when the EDB IS the facts). No number
  follows from the abstract `hash`; a one-felt BabyBear instantiation is ~2^15.5.
- **Scope** (codex round 2 §1a-c): active-domain semantics only (unsafe `p(X) :- q()` over `{q()}`
  derives nothing here and everything unrestricted); `countQ` is by predicate symbol, not
  `(pred, arity)`; `count_unique_or_collides` needs identical rule lists; the deployed leaf encoding
  must be canonical felts or `flatten`'s injectivity is lost to modular aliasing.
- **CALM**: `dregg-query/src/classify.rs` grades negation and aggregation as finalized-dependent
  and says "there is no recursion" [READ header]. This certificate adds recursion on the monotone
  side; Count stays finalized-dependent (it is exact as of the committed root).

## 7. Prior art

Tantow et al., ITP 2025 (Lean checker for Datalog proof-tree/DAG certificates from Nemo) [READ];
Circuitree, IEEE Access 2022 (Datalog reasoning in Bulletproofs) [SNIPPET]; Soufflé provenance
(Zhao-Subotić-Scholz, 1907.05045) [READ]; Benzaken-Contejean-Dumbrava, ITP 2017 (certified
stratified Datalog in SSReflect) [RECALLED]; CALM (Hellerstein-Alvaro, CACM 2020) [READ]. Not ours
to claim: verified Datalog certificate checking, ZK Datalog. Ours, as far as the search went (no hit
is not none-exists): the closure leg as an executable exactness certificate composed with an MMR
root binding and the named-pair collision residual.

## 8. Built vs proposed

| object | where | rung |
|---|---|---|
| `Derives`, `verify`, `replay_sound`, `closed_complete`, `verify_sound`, `edb_bound_or_collides`, `count_unique_or_collides`, falsifiers | `M/Datalog/FixpointCert.lean` (28 kernel-clean keystones) | **L2** (statement + proof + executable certificate + counts) |
| single-firing AIR | `M/Circuit/Emit/DerivationEmit.lean` | L3 (emitted; one firing) |
| iterated firings under a fold + sorted-enumeration closure | proposed | L3; milestone: the 4-node transitive-closure instance as `6` firing descriptors plus `216 + 36` closure lookups, with pinned counts against `DerivationEmit`'s 386-column row |
| safe-program coincidence theorem; stratified negation per stratum | proposed | L1 each; one file |
