# Streaming certificates: grounding (initiative 11)

2026-11-06. Lane: streaming certificates (ω-automata prefix receipts over an MMR-committed live log).
Tags: [READ] seen at file:line; [MEASURED] a run or pinned `#guard`; [RECALLED] from memory, not re-read;
[SNIPPET] a search-result abstract only. Paths: `M` = `breadstuffs/metatheory/Dregg2`, `R` = `breadstuffs`.

## 1. What already exists, and what this lane does with it

| object | where | what it proves / does | use here |
|---|---|---|---|
| MMR model: `push`, `peaksOf`, `bag`, `mroot`, `peaksOf_append` | `M/Lightclient/MMR.lean:263-402` | the carry IS the append; `peaksOf (L++[v]) = push (peaksOf L) (.leaf v)` by `foldl` | **reused verbatim**: the window receipt's frontier update is `push`, abstracted to (height, hash) pairs |
| `mroot_binds_or_collides`, `MRootColl` | `MMR.lean:493`, `:570` | equal roots ⇒ equal logs or a NAMED, refutable sponge collision (no CR floor) | the only crypto residual of every stream theorem |
| `RVerifies`, `range_complete`, `rverifies_iff_exact`, `server_cannot_omit_position` | `MMR.lean:705-785` | dense-position range answers: nothing skipped, nothing forged | **inherited**: a chain of accepted windows ends at a root whose every range answer is the monitored log |
| `append_preserves_range` | `MMR.lean:684` | an old range is verbatim true of the appended log | prefix monotonicity of the receipts' MMR half |
| `light_client_position_non_omission`, `anchored_history_starts_at_genesis` | `MMR.lean:882`, `Circuit/RecursiveAggregation.lean` | the chain-face composition | not consumed at L2; it is the route by which a stream root rides the dregg chain commitment (L4) |
| Rust MMR (`Mmr`, `verify_range`, `MmrHasher`, `Blake3Mmr`) | `R/dregg-query/src/mmr.rs` | the client `RVerifies` check, root-pinned length, positional directions | **reused** for the producer and for third-party range openings; one new hasher instance (Lean's arity-domain shape over blake3) and one new incremental frontier (today `Mmr::peaks()` recomputes every subtree: O(n) per root, `mmr.rs:206`) |
| `verify_windows` | `R/dregg-query/src/windows.rs:44` | paged windows tile `[0, len-1]` against ONE trusted root | the *static* whole-log read; the stream receipt is its incremental dual (each window moves the root, the tiling is the `n0 = prev.n1` chain check) |
| `10-omega.md` (automata family note) | `R/docs/automata/10-omega.md` | proposes `DBuchi`, `BadPrefix`, `SafeLang`, the 3-valued `Verdict`, `monitor_whole_log_sound`; says liveness is invisible at a finite prefix | **implemented and extended** (§3); its milestone `M/Crypto/Omega/PrefixMonitor.lean` becomes `M/Stream/` |
| `Crypto/Dfa.lean` Layer B′ (`BoundStatement`, `dfa_bound_verify_sound`) | `M/Crypto/Dfa.lean:243-294` | a DFA statement must bind the content, or a benign word discharges it for any record (the "splice") | the same law here: the verifier computes each symbol AND each leaf from the same raw bytes, so the symbol stream cannot be detached from the committed log |
| `Automata/TableRun` + `TableRunSpec`, `lake exe dfa-run`, `lake exe datalog-check` | `M/Automata/TableRun.lean`, `R/metatheory/DatalogCheck.lean` | the house pattern for "accept routed through the Lean predicate": a core-only executable module, a spec file proving the exe's fold IS the theory object | **copied as a pattern**: `Stream/Core.lean` is core-only and executable; `Stream/Omega.lean` and `Stream/Window.lean` prove theorems about those very definitions; `lake exe stream-check` runs them |
| `Crypto/Blake3Compute.lean` | `M/Crypto/Blake3Compute.lean` | BLAKE3 in pure Lean, KAT-pinned, no `implemented_by` twin | the verifier's hash; it is the same function the Rust producer calls through the `blake3` crate |
| `AttestedAutomatonLanes8` (the weld) | `M/Circuit/Emit/AttestedAutomatonLanes8.lean` | an attested-automaton run whose rows open a committed transition table at the 8-felt root | not consumed at L2. It is the L4 route: a window receipt proved inside the weld removes the follower's need to see the window's entries; §4 prices it |
| `Datalog/FixpointCert`, `StratifiedCert` | `M/Datalog/` | fixpoint certificates for stratified Datalog | not used: the demo policy is finite-state. A first-order policy (per-tool-call-id obligations) is the register-automaton / Datalog extension, named in §5 |
| `dregg-stream-ingest` | `R/dregg-stream-ingest/` | crowd-stream (YouTube Super Chat) events to weighted ballots | unrelated despite the name: no commitment, no monitor |
| counts model | `zkml-research/notes/construction-search/space.py --certs` | pinned per-symbol cell counts per automaton family | **extended** at L2/L3 with a `stream-window` family (monitor step + leaf digest + amortized carry), not forked |

`Deos/FlowRefine.lean:18` is the only other Büchi content in `M`, and it is a decision procedure (well-foundedness collapses Büchi acceptance in a simulation game), not a certificate [READ via 10-omega.md].

## 2. Outside prior art, and what the MMR receipt adds

- **LTL3 / three-valued monitoring** (Bauer, Leucker, Schallhart, *Runtime Verification for LTL and TLTL*, TOSEM 2011) [SNIPPET, RECALLED]: a finite prefix gets ⊤ (every extension satisfies), ⊥ (every extension violates) or ? ; the monitor is built from the Büchi automata of φ and ¬φ by emptiness per state. Our `Verdict` is exactly this, with one honest weakening: the dead / good state sets are a *checked certificate* (closed under every step, disjoint from / contained in the acceptance set), which is sound and may be incomplete (it can say ? where LTL3 would say ⊥ if the supplied dead set is not the maximal one). Soundness is proved; completeness for the demo automaton is shown by exhibiting both extensions from each ? state.
- **Safety-liveness decomposition** (Alpern & Schneider, *Recognizing safety and liveness*, Dist. Comp. 1987) [SNIPPET]: every ω-regular property is safety ∩ liveness, characterized on the Büchi automaton. The demo policy is built as exactly that product, and the theorem `prod_accepts_iff` states it.
- **Stream RV**: Lola (D'Angelo et al., TIME 2005), RTLola (Baumeister, Finkbeiner et al.; tutorial arXiv 2501.15913), TeSSLa (Convent, Hungerecker, Leucker et al., arXiv 1808.10717) [SNIPPET]: bounded-memory stream specifications with formal semantics. None produces a third-party-checkable artefact; the monitor's output is trusted.
- **Parametric trace slicing** (Chen & Roşu 2009; Havelund, Reger et al., QEA / MarQ) [SNIPPET]: per-parameter-instance slices for first-order properties. Out of scope at L2 (finite alphabet); it is the route to per-`tool_use_id` obligations (§5).
- **Verified monitors**: VeriMon (Basin, Dardinier, Traytel et al., Isabelle/HOL, IJCAR 2020 / ICTAC 2022) for MFODL; Chattopadhyay & Mamouras (Coq, RV 2020) for past-time MTL [SNIPPET]. These prove the *monitor algorithm* correct; they do not let a third party check that a *particular run* was monitored over a *particular, complete* log. Our theorems are the per-run statement plus the log binding.
- **Monitoring LLM conversations**: Cohen, Havelund et al., RV 2026 (DejaVuGuard, first-order past-time LTL over conversation traces) [SNIPPET]. Closest in subject matter; trusted monitor, no receipt.
- **Oblivious monitoring**: Banno et al., CAV 2022 (FHE-run DFA for safety LTL) [SNIPPET]: privacy of the trace, no non-omission and safety only.
- **Append-only commitments**: Bonneau, Chen, Christ, Karantaidou, *MMRs are optimal* (CRYPTO 2025, ePrint 2025/234); the Merkle Mountain Belt (arXiv 2511.13582, increment proofs); IETF draft-bryce-cose-merkle-mountain-range-proofs (consistency proofs) [SNIPPET]. These give consistency between two roots; none pairs it with a monitor state.
- **IVC / PCD**: collaborative IVC (ePrint 2026/410) [SNIPPET]. The weld leg (§4) is where a window receipt becomes an IVC step; not claimed at L2.
- I searched for a "proof of correct monitoring" ePrint (2025-2026) and found none [two searches, no hit]. No hit is not "none exists", and nothing here claims a first.

**What the receipt adds over all of the above**: (1) *non-omission, when anchored*: if the chain's final root equals the root published for the source log, the monitored entries ARE that log (`anchored_is_genuine`), and any auditor holding only that root gets, by `server_cannot_omit_position`, the same entries at every position. Without an anchor, the chain check ties the receipts only to the windows it was shown (a producer that drops a line before windowing and recomputes every receipt passes the chain check; the demo shows the anchor refusing it); (2) *third-party checkability*: the receipt chain is checked by a Lean predicate, not trusted; (3) *incrementality*: checking window k needs only the follower's own state after window k−1, not the prefix.

## 3. The bar, restated (peer correction)

The opening bar asks each receipt to state that the liveness condition "has been met k times". That is
the right finite content, but it must not be read as a liveness verdict: **no finite prefix certifies a
liveness property true** (every prefix of `□(prompt → ◇reply)` extends to a violating ω-word: never
reply again). What the receipts can and do certify:

1. **safety half**: ⊥ is final (`verdict_monotone`) and sound (`verdict_viol_sound`: every infinite extension is rejected by the Büchi condition);
2. **liveness half**: the Büchi visit count `k` over positions `(0, n]` is exact, and `buchi_iff_count_unbounded` ties it to the ω-semantics: the infinite stream is accepted iff the receipts' counters are unbounded. A receipt chain is therefore a finite approximant of the acceptance condition, not a verdict on it, and the verdict stays ? until the safety half fires;
3. **obligation age**: the receipt also carries `lastMark`, the last position at which the run was in an accepting state (`lastMark_spec`, `lastMark_marked`; 0 = none), so `n − lastMark` is certified as the length of the current unaccepting stretch: an upper bound on the age of the oldest open prompt (and, after a trip, the time since the trip).

And the verifier's cost is O(w + log n) hash evaluations for a window of w entries at log height n (the
frontier has popcount(n) ≤ log₂ n + 1 peaks; the carry is amortized O(1) per append), not "independent
of n". That is the honest bar; the measurement in L3 reports both terms.

Bar for done (unchanged otherwise): a real ω-automaton with the acceptance condition in the statement
(Büchi and co-Büchi), `window_sound`, `windows_compose` (prefix + non-omission), `verdict_monotone`,
falsifiers (dropped position, swapped windows, a flag-DFA mutant), axioms pinned; a Rust producer over
dregg-query's MMR; `lake exe stream-check` as the only acceptor; a demo over a live Claude Code session
transcript with receipts every 100 events, a follower, and a microsite with the measured per-window cost.

## 4. Build plan

- `M/Stream/Core.lean` (Lean core only, executable): `DOmega`, `scan`, `Verdict`, `HPeak`/`hpush`/`hbag`, `Acc`, `WindowCert`, `checkWindow`, `checkChain`.
- `M/Stream/Omega.lean` and `M/Stream/Window.lean`: ω-semantics (`Accepts` for Büchi/co-Büchi over `ℕ → Sym`), `buchi_iff_count_unbounded`, `verdict_{false,true}_sound`, `verdict_monotone`, `prod_accepts_iff`, `hfront` = abstraction of `peaksOf`, `window_sound`, `windows_compose`, falsifiers, `#assert_axioms`.
- `M/Stream/ClaudePolicy.lean`: the transcript classifier and the demo policy (safety: none of ember's forbidden commands — `git stash`, `git add -A`, `pkill -f`, `killall`, `kill -u`; liveness: every human prompt is eventually followed by an assistant reply), as a product automaton.
- `R/metatheory/StreamCheck.lean`: `lake exe stream-check {produce|verify|follow}`.
- `R/dregg-query`: `ArityBlake3` hasher (Lean's arity domains over blake3) and an incremental `Frontier`; a `stream-monitor` binary that tails a JSONL file, appends to the MMR, cuts a window every N events, and has `stream-check produce` compute the receipt; the follower is `stream-check follow`.
- Counts: a `stream-window` row in `space.py --certs`.

## 5. Not in scope at L2, named

- First-order obligations (every `tool_use` id gets its `tool_result`): needs registers or slicing (`11-register.md`, QEA); the finite alphabet cannot count open ids.
- Succinct receipts (a follower that does not see the window's entries): the weld (`AttestedAutomatonLanes8`) or IVC; priced in counts, not built.
- Midstream join without a trusted checkpoint: the executable follower always starts at genesis. `chain_tracks` covers a follower that starts from any state it already knows `Tracks` the prefix; no theorem lets a follower adopt a stranger's receipt k as a checkpoint (the frontier's heights are not bound by the root alone).

## 6. Audit record

- Cross-model (`gpt-6-astra` via codex), round 1, 2026-11-06: **blocked**. Two runs (78k and 46k tokens)
  ended in "approved for Daybreak Blue, but this response cannot be shown as this session was not
  authenticated with one of your authorized hardware keys". A short probe ("reply OK") passes; the audit
  answers are withheld. Needs ember to re-authenticate codex with a hardware key; until then the
  required cross-model rounds are owed.
- Interim fresh-context audit (Claude, not cross-model), 2026-11-06: no blocker; two MAJOR (no published
  anchor, so omission was not caught at the source; the Rust `audit` read an unchecked root and cited a
  theorem it does not instantiate) and seven MINOR (checkpoint wording, the reach-once falsifier missed
  the counter mutant, `lastMark` unproved, `streamHash` tags not prefix-free, classifier weaker than its
  prose, doc drift, `sat` vacuous at the demo policy). All fixed in the same landing: `anchored_is_genuine`
  and `verify --anchor`; `audit --root`; `lastMark_marked` and the `lastMark` conjuncts of
  `windows_compose`; `reach_once_not_buchi` on `other, prompt^ω` (counter 1 forever, rejected);
  prefix-free tags `…:mmr:n` / `…:mmr:w`; a tokenizing classifier (wrappers peeled, `git -C`, option
  clusters, `pkill -x`, `ssh host '…'`) with 13 new `#guard`s; the vacuity of `sat` at the demo stated.
