# Dregg2/Datalog — Datalog certificates with an exact Count

Tags: [MEASURED] a pinned `#guard`, a kernel `decide`, or a run on this Mac (2026-11-06);
[READ] seen in the file. Design notes: `docs/automata/13-datalog.md`,
`docs/automata/SEMANTIC-CEILING.md` §1.2-1.3.

A statement is `(program, [strata,] root, pred, count)`. A certificate is the committed EDB plus a
semi-naive trace. The checker replays the trace, checks CLOSURE (no derivable fact is missing),
recomputes the MMR root, and compares the count. Every checker has a weaker twin whose acceptance
of a forgery is exhibited beside the strong checker's refusal.

| file | what it proves | keystones | `lake env lean` |
|---|---|---|---|
| `FixpointCert.lean` | positive Datalog: `verify_sound` (the database is EXACTLY the least fixpoint, count exact, root bound), `count_unique_or_collides` | 28 | 17 s |
| `StratifiedCert.lean` | stratified negation: `verifyS_sound` (EXACTLY the stratified model `DerivesS`), `verifyS_strata_exact` (one database per stratum, each the cumulative model `Mᵢ`), `countS_unique_or_collides`, `verifyS_intended_or_collides`, `verifyS_supported_model` (negation read against the final database: where `stratifiedB` carries weight), `verifyS_receipt` (all of these about one database), `verifyS_count_zero_absent` | 40 | 15-33 s |
| `Aggregates.lean` | `sumAt`/`minAt`/`maxAt` as folds, each a function of the member set; `seq_acc_is_fold`, `accValid_iff`; the budget statement: `verifyBudget_sound`, `budget_final_unique_or_collides`; restates what `audit::BudgetProof` claims | 21 | 11 s |
| `SafeCoincidence.lean` | for safe programs the active-domain semantics IS the unrestricted one: `derives_iff_unrestricted`, `derivesS_eq_unrestricted`, `verifyS_sound_unrestricted`, `verifyJ_sound_unrestricted` (what the exe accepts is the standard model, no side condition), `verifyJ_receipt` (the receipt-level export); falsifier `unsafe_semantics_differ` | 19 | 14 s |
| `JoinClosure.lean` | the closure leg by JOIN over the positive atoms instead of `|dom|^{vars}` enumeration: `closedJoinS_closedS`, `mem_candidates` (safe rules); `verifyJ_verifyS` and `verifyBudgetJ_verifyBudget` (what the executable accepts, the theorems cover) | 20 | 16 s |

Falsifiers [MEASURED]. Every separation below is a NAMED theorem (`weak = true ∧ strong = false`, plus
the false semantic claim where there is one) under `#assert_all_clean`, with `#guard` mirrors:
`forged_absence_separation`, `open_lower_separation`, `current_db_separation`,
`nonstrat_separation`, `tampered_accepted_by_trustFinal` with `tampered_refused_by_verifyBudget`,
and `join_safety_separation`. The exception is FixpointCert's `verifyNoClosure` pair, which is
`#guard` only.
- `FixpointCert`: the open trace is refused at the honest count and at its own count; `verifyNoClosure` accepts it.
- `StratifiedCert` (a): the honest revocation trace verifies at count 1.
- `StratifiedCert` (b): forged absence. `FixpointCert.verify` on the positive projection accepts it; `verifyS` refuses it.
- `StratifiedCert` (c): the revocation is derivable later (codex round 3, finding 18). `verifyCurrentDbNegation` and `verifyNoLowerClosure` accept; `verifyS` refuses. All three verdicts are kernel-decided theorems.
- `StratifiedCert` (d): `p :- q, ¬p`. `stratifiedB` refuses; `verifyNoStratCheck` accepts; `supportedB` is false.
- `Aggregates`: the tampered accumulator row hides an overrun. `verifyTrustFinal` accepts; `verifyBudget` refuses (kernel-decided).
- `JoinClosure`: an unsafe rule. The join closure without `safeB` accepts; `verifyS` and `verifyJ` refuse.

## The gate

```
cd metatheory
lake build Dregg2.Datalog.FixpointCert                  # once, for the olean the others import
lake env lean Dregg2/Datalog/StratifiedCert.lean       # each file prints its #assert_all_clean line
lake env lean Dregg2/Datalog/Aggregates.lean
lake env lean Dregg2/Datalog/JoinClosure.lean
lake build datalog-check                               # the extracted checker (DatalogCheck.lean)
```

`lake build datalog-check` took 2 min 53 s on first build. Almost all of that was C objects for
the imported Mathlib tactic modules [MEASURED].

## The executable

`DatalogCheck.lean` → `lake exe datalog-check <file.json>`: it runs `verifyJ` (and `verifyBudgetJ`
when the statement has a `budget`), prints the statement, the counts and the verdict, and exits 0 or 1.
The hash is SHAKE256 with a domain prefix over a canonical framed encoding of `List ℤ`. Python's
`hashlib` reproduces it byte for byte (a pinned `#guard`, and the demo's root). The deployed hash is
the leaf's cSHAKE (`SUBSTRATE-DECISION.md` §2). Injectivity of the byte encoding is checked by
round-trip `#guard`s, not by a theorem. The demo is `demo/datalog-governance/`.

## Not claimed
- "Safe" means range-restricted WITH dense variable numbering: every index below a rule's variable
  bound occurs in a positive atom. A range-restricted rule that skips an index is refused by
  `datalog-check`. Variable ids are not normalized.
- Unsafe programs: the active-domain semantics differs from the unrestricted one
  (`SafeCoincidence.unsafe_semantics_differ`). For safe programs they coincide (proved), and
  `datalog-check` refuses unsafe rules.
- The count is exact for the strata NAMED in the statement. Independence of the perfect model from
  the choice of stratification is not proved.
- `countQ` counts by predicate symbol.
- No proof system: verification is native re-execution. The L3 shape is in note 13 §3.
