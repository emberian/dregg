# LRAT refutation certificates

[READ] `LratCert.lean` checks deletion/RUP replay over numbered CNF clauses. Every
addition requires a fresh live identifier and an ordered chain of hints producing
a conflict under the negation of the proposed clause. A checked empty clause
finishes the refutation. This is the deletion/RUP fragment, not full RAT support.
`checkStd` cross-checks the examples with Lean's shipped LRAT checker.

`checkLrat_sound` derives `Unsat f` from acceptance. `verify` additionally binds
the certificate CNF to the statement's MMR root through a length-prefixed clause
encoding. `refutes_intended_or_collides` transfers unsatisfiability to the intended
CNF, or produces the named collision for those concrete openings. The hash
function is a parameter; the toy reference hash is not a cryptographic claim.

## Reproduce

From the repository root, with warm Lean dependencies:

```sh
cd metatheory
lake env lean Dregg2/Sat/LratCert.lean
```

[MEASURED] The file pins 28 kernel-clean theorems. Exact `#guard_msgs` axiom
expectations guard the soundness boundaries and the new audit witnesses. The
new separation/count theorems use kernel `decide`, with no `native_decide`.

## Falsifiers and counts

| Named term | What it isolates |
|---|---|
| `Reference.reusedId_separation` | `[[1],[-1]]`, `.add 1 [] [1,2]`: passes `checkNoFresh`, fails freshness in `checkLrat` |
| `Reference.dropHint_separation` | PHP's last conflict hint omitted: no-RUP comparator accepts, real replay refuses |
| `Reference.noRup_not_superset` | An empty input clause causes early conflict; an unused trailing dead hint is accepted by real replay but rejected by the comparator |
| `Reference.forged_accepted_by_noRup`, `forged_refused`, `satCnf_sat` | A false unsatisfiability claim at a correct statement root, with an explicit satisfying assignment |
| `Reference.php3_counts` | Recomputes every benchmark count below as a kernel-checked term |

The no-RUP comparator requires every hint to resolve, so it is **not** an
acceptance superset of the production checker. `php3ReusedId` remains a malformed
replay regression; it also leaves later hints pointing to the old identifier and
does not isolate freshness.

[MEASURED] PHP(3,2): 9 input clauses, 7 additions, 18 supplied hint lookups,
maximum hint chain 5, maximum input/proof widths 2/1, and 29 hinted literal reads.
The count function replays all supplied hints and widths, including any suffix
unused after an early conflict; these are reproducible certificate-work counts,
not total runtime instruction counts or a bound on table-search comparisons.
