# Codex (gpt-6-astra) adversarial rounds on the automata program, with adjudication

Method: `codex exec -c model="gpt-6-astra" --sandbox read-only "<prompt>"` from the breadstuffs root,
file paths in the prompt, statements attacked before commit. Codex's words are summarized and
attributed; the verdicts are mine (the Fable deputy). Tags: ACCEPT (changed the code or doc),
ACCEPT-DOC (changed only the prose), DEFER (right, not done today, named as follow-up), REJECT
(with reason).

---

## Round 1 (2026-11-05): the Part A statements before commit

Prompt: attack every theorem statement in `Dfa.lean` Layer B′ and `AttestedAutomatonLanes8.lean`
for vacuity, tautology, free passes, docstring overreach; propose the strongest replacement.
Output: `scratchpad/codex/round1.out` (9.3 KB). Codex did not run Lean.

| # | finding (Codex) | verdict | what changed |
|---|---|---|---|
| 1a | `dfa_bound_verify_sound` is an adapter over `extract` (reflexive `w := traceWord`); it says "SOME word commits to `c`", which at `commit := fun _ => ()` is as weak as the unbound form. Binding matters even for ONE certificate when identifying THE record. Proposed: for a named `record` with `commit record = c`, conclude `traceWord tr = record ∨ (traceWord tr ≠ record ∧ commit (traceWord tr) = commit record)`. | ACCEPT | added `dfa_bound_identifies_record_or_collides` with exactly that conclusion; the Layer B′ prose now says binding is NAMED by this theorem, not assumed, and that a trivial scheme collapses the bound form. The adapter shape is the tree's convention for every `*_verify_sound` (the carrier is the claim); kept. |
| 1b | No accepting bound-kernel instance exhibited (reference kernel still OPEN). | DEFER | the file's own OPEN note stands; the falsifier does not need a kernel instance. A decidable-table reference kernel is the named follow-up. |
| 1c | `dfaDisclose.leaked := fun _ => ()` does not establish "full disclosure". | REJECT as out of scope | unchanged from the pre-existing wiring; the dial floor is a declared obligation, not a theorem about leakage. |
| 2 | Splice separation is genuine but scheme-relative (identity scheme). Proposed a scheme-generic form with hypothesis `∀ tr, DfaAccepts … tr → commit (traceWord tr) ≠ c`. | ACCEPT | added `splice_fails_bound_of_sep` (any scheme, any `c` no accepting run opens); `splice_fails_bound` is its identity instance. |
| 3 | `Satisfied2Lanes8` matches `Satisfied2Public` field for field with only the two map legs swapped (checked all eleven). BUT "deployed-width twin" overstates: `opensToMerkle8` is the DENSE `2^d`-leaf model; the deployed builder computes the sentinel-headed padded `padImtRoot8`; `writesToMerkle8` demands full-sized post-heaps. | ACCEPT-DOC | header now says "the weld under the dense 8-felt model, not the deployed verifier"; for the attested automaton the two coincide in content because `autoHeapW` is total over `2^16` keys; re-basing onto `padImtRoot8` is the named follow-up. |
| 4 | `LaneCanonical` is not implied by satisfaction (shift a public lane by `p`); it constrains roots only, not `NEXT` or hidden heap values. Congruence vs equality handled correctly. | ACCEPT-DOC | already stated as a hypothesis; header records that the missing deployment obligation is a canonical-decoding theorem. |
| 5a | `weld8_forged_edge_refused` pins the heap by length/root/key/forged value, so an unrelated pigeonhole collision cannot discharge it; but the heap is existential in `Prop` (no executable extractor). | DEFER | correct; `Satisfied2Lanes8` hides heaps inside `opensToMerkle8` exactly as `Satisfied2`'s `opensTo` does. Carrying heaps as data (`M i` per row) is the named follow-up. |
| 5b | `weld8_accepted_run_is_committed_run`'s right disjunct is available even for an honest row (change an unqueried value by `p` at a chip that reduces mod `p`; the root is unchanged; `MapRootColl` fires). The OR is true, not exclusive. | ACCEPT-DOC | header says so; the content is the forged-edge theorem; the corollary is demoted from headline. |
| 5c | `MapRootColl` may be a leaf-block (arity 3) collision, not an arity-16 node collision. | ACCEPT-DOC | wording fixed everywhere: "a collision of the chip absorb `chipAbsorb8` at a node block (arity 16) or a leaf block (arity 3), whichever `mapRoot8Find` resolves". |
| 5d | Neither theorem proves a whole accepting run (`d.start`, `d.accepts` unused). | DEFER | per-row today; the chaining corollary is the next theorem (named in the header). |
| 5e | The forgery premises are inhabited (constChip: constant-0 vs constant-1 automata on `[0]`), but the file does not package the example. | ACCEPT | added `forgeD`, `forgeE`, `forgeT`, `weld8_forgery_premises_inhabited`: a closed instance meeting every hypothesis of the forged-edge theorem. |
| 6 | The constChip falsifier refutes universal lane freedom, not content equivocation (every automaton shares the zero root there). Proposed the characterization `Satisfied2Lanes8 constChip … (weldWit8 d R8 q w) ↔ R8 = zeroDigest8`. | ACCEPT | added `autoRoot8_constChip` and `lanes8_constChip_iff`; the falsifier's docstring already said "vacuity falsifier, not deployed content". |
| 7 | The bookkeeping lemmas are definitional and need nothing. | — | — |
| R | Would refuse to merge: `weld8_accepted_run_is_committed_run` as a binding headline; "prover-supplied arity-16 collision" wording; "P9 completion" claims over dense semantics; `dfa_bound_verify_sound` as identifying THE record; `weld_collision_disjunct_refutable` as a deployment non-vacuity certificate. | ACCEPT (all four wordings) | none of the four claims appears in the commit messages or headers after this round; P9 is described as "the denotation half under the dense model, shared `holdsAt` unmoved". |

Net effect of round 1: two theorems added to `Dfa.lean`, three to `AttestedAutomatonLanes8.lean`,
no statement weakened, four claims retracted from prose before they were ever committed.

---

## Round 2 (2026-11-05): `FixpointCert.lean` and the program's gaps

Prompt: attack the Datalog statements (semantics, exactness, collision disjunct, falsifiers, error
accounting) and list missing families/operators and cost errors. Output: `scratchpad/codex/round2.out`.

| # | finding | verdict | what changed |
|---|---|---|---|
| 1a | Active-domain semantics loses nothing for safe programs (argument given, unproved); differs for unsafe `p(X) :- q()` over `{q()}` (derives nothing vs everything). | ACCEPT-DOC | scope paragraph in the file header and note `13`; coincidence theorem stays the named follow-up. |
| 1b | Exactness holds; duplicates in the EDB are refused, not deduplicated; `countQ` is by symbol not `(pred, arity)`; `varBound`/`substs dom 0` correct. | ACCEPT-DOC | scope paragraph. |
| 1c | No free pass in `MRootColl`; `hP` needs identical rule lists; `flatten_injective` fine over `ℤ`, but modular reduction at deployment aliases `e(0)`/`e(p)` and `Reference.hash0` has that alias. | ACCEPT-DOC | scope paragraph: canonical leaf encoding required. |
| 1d | Guards are regression checks; formalize the weaker checker's ACCEPTANCE; the out-of-domain guard was confounded by body failure; "every #guard the kernel evaluates" is inaccurate. | ACCEPT | added `verifyNoClosure` with `#guard … = true` beside `verify … = false`; the domain falsifier now uses the unsafe rule `p(X) :- q()` over `{q(), d(1)}` with `X := 9`; header wording corrected (compiled evaluation; `path14_derives` is the kernel-checked instance). |
| 1e | One `ε_STARK + b_EDB` for the whole checker, no per-firing multiplier; L2 is `Σεᵢ + b_MMR`; the hub's "shared randomness prevents union bounds" is false — what needs justification is each bound in the adaptive experiment. | ACCEPT-DOC | note `13` §6 and hub §3.1 item 2 rewritten. |
| 2 | Eight missing/mis-costed families: weighted sum-over-paths, counter/Parikh, two-way, shuffle product, CFL-certificate intersection, relational transduction, Kleene-star table growth, symbolic predicate evaluation cost. | ACCEPT-DOC | hub §2.0 added. |
| cost | `hash_bytes_8` is `⌈n/8⌉ + 2` permutations (squeeze at `poseidon2.rs:430`); "3-11 cells" mixes a binary-symbol shape with map authentication into a byte-step comparison; "hash dominates every regular family" overstated. | ACCEPT-DOC | hub §0 and note `01` §3 corrected. |

Not adopted: nothing refused outright this round.
