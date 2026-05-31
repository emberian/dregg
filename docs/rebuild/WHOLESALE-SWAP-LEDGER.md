# WHOLESALE-SWAP-LEDGER — everything that must exist in Lean before we flip `turn/src/executor/` in ONE cutover

> **Goal (ember, 2026-05-31).** Replace ALL of dregg1's turn semantics
> (`turn/src/executor/`: `authorize.rs` + `execute.rs` + `execute_tree.rs` + `apply.rs`) with the
> verified Lean turn executor in a **single cutover** — no partial / half swap (a Frankenstein
> executor is exactly where laundering hides). Produced by the `wholesale-swap-coverage` workflow
> (`wdr55hc1o`, 6 source-grounded mappers + synthesis) over a direct read of the Rust + Lean.

## Headline (honest)

The verified Lean turn covers a small, honest sliver of dregg1's complete turn and is **NOT** close
to wholesale-swap-ready. The only thing the FFI dispatches is `@[export] dregg_exec_full_turn →
TurnExecutorFull.execFullTurn` (`FFI.lean:936`), a **flat `List FullAction`** fold over exactly
**five** kinds (balance/delegate/revoke/mint/burn) whose wire grammar carries only `{cells, caps,
actions}`. Verified facts: the `Effect` enum is **52** variants (`action.rs:760`) of which **~4** are
dispatched; the `Authorization` enum is **10** variants (`action.rs:206`) of which **ZERO** reach the
executed path (it authorizes solely via `Kernel.authorizedB` = `actor==src` ∨ holds-cap — **no
signature/proof/token check, no signing-message reconstruction**); there are **ZERO** real `@[extern]`
crypto bindings (all 7 `@[extern]` strings are doc-comment prose; every Rust `extern` block calls
*into* Lean as a differential oracle, the opposite direction from a crypto portal); and **none** of
the rich sibling modules (EffectsState/Paired/Supply/Authority, AuthModes, CrossCellForest/TurnForest,
the 12 Crypto/* + 13 Authority/*) is imported by the dispatched path. A single safe cutover therefore
requires a **core rebuild**: widen `FullAction` into the full Effect+Authorization sum over a
tree-shaped forest, fold the stranded proofs onto the dispatched executor, build the ~12 `@[extern]`
crypto portals + their §8 discharge, widen the wire codec to the whole turn, and add the two missing
TCB obligations (a parse∘encode roundtrip **theorem** + a committed golden corpus).

## Coverage (~140 distinct turn-semantic elements)

| tag | count | meaning |
|---|---|---|
| **FAITHFUL_AND_DISPATCHED** | ~23 | in the executed `execFull`/`execFullTurn` path + narrow codec primitives that round-trip |
| **MODELED_BUT_STRANDED** | ~63 | real per-effect/per-mode/forest/crypto proofs EXIST in sibling files, **none imported by the dispatch** |
| **THIN** | ~20 | a generic shadow stands in for the load-bearing Rust mechanism |
| **ABSENT** | ~34 | no Lean model at all |

Net **dispatched** coverage of the complete turn: **~4/52 effects, 0/10 auth modes, 0/11 admission
gates, 1 tree property (all-or-nothing), 0 crypto operations.**

## The build checklist (dependency-ordered; ALL soundness-critical)

1. **META-FILL A [XL] — tree-shaped `FullForest`.** Widen `FullAction` into a node = (`Action` with a
   real `Vec<Effect>` effect-list + `Authorization` + `Preconditions` + `may_delegate`) and children,
   replacing `List FullAction`; either a recursive node executor or a PROVED pre-order lowering
   `lowerForest : FullForest → List node` with execFullTurn-over-tree = flat-fold. *The structural
   keystone every other fill depends on.* (deps: none)
2. **META-FILL B [XL] — port the ~30 stranded per-effect steps** onto the dispatched executor (one
   `FullAction`/effect-list arm each) and **re-prove the spine** (conservation `execFull_ledger`,
   chain-link, four-conjunct `StepInv`) over the widened sum. EffectsState (setField/emitEvent/
   incrementNonce/setPermissions/setVK/seal/unseal/destroy), EffectsSupply (createCell/spawn/refresh/
   bridge*), EffectsAuthority (introduce/attenuate/dropRef/revokeDelegation/validateHandoff/exercise),
   EffectsPaired+RecordKernel (obligation + escrow via the chains — switch the conserved measure to
   `chainTotal`). *This is the FILL-1 pattern I validated end-to-end, ×30.* (deps: A)
3. **META-FILL C [L] — extend `RecChainedState`** so account creation can **grow** the `accounts`
   Finset (createCell/spawn), add nonce/proved_state/permissions/lifecycle fields, thread the
   escrow/obligation/nullifier/note-root side-tables through the dispatched fold. (deps: none)
4. **META-FILL D [L] — wire `AuthModes` INTO `recCexec`.** Replace the bare `authorizedB` gate with
   `authModeAdmits` over a per-action `Authorization` sum (OneOf/Custom/CapTpDelivered/Bearer/Token/
   Unchecked through their proved-sound arms); **add `.stealth`** (the one mode AuthModes omits); add a
   per-cell `AuthRequired` lattice field. (deps: A)
5. **META-FILL E [XL] — build the ~12 `@[extern]` crypto portals + §8 discharge.** SignatureKernel
   (ed25519), VerifierKernel (STARK/FRI), Pedersen+Schnorr-excess, Poseidon2, BLAKE3, nullifier,
   Seal (X25519+AEAD), MacKernel (HMAC). Wire the already-DERIVED `verify_sound` bridges onto the
   binding instances. *The entire post-swap TCB floor.* (deps: D)
6. **META-FILL F [L] — byte-exact signing-message preimages** ported to Lean over the FFI turn record
   (domain separators, federation_id, per-effect hash, postcard preconditions) + a differential
   asserting Lean preimage bytes == Rust preimage bytes BEFORE any portal verify. *Without it every
   signature portal verifies the wrong message.* (deps: E)
7. **FILL G [XL] — per-node forest threading:** parent-cell + DelegationMode (None/ParentsOwn/Inherit/
   SnapshotRefresh) + path-vector + gas/excess accumulators through the recursive executor; port the
   CrossCellForest/TurnForest `Caps.derive_no_amplify` Granovetter law onto the dispatched world;
   16-hop SnapshotRefresh chain-walk; cross-cell access gate. (deps: A, B)
8. **FILL H [XL] — admission preamble** as a fail-closed prologue: empty-forest-reject (fix Lean's
   ADMITS-`[]` mismatch), valid_until, agent-existence, nonce-replay, fee-coverage, write-set freeze;
   prevHash-linked `ReceiptChain` (replace `List Turn` log); `BudgetSlice` for Stingray. **The Phase-1
   fee-debit+nonce-tick COMMIT is never-rolled-back — it breaks pure all-or-nothing**; prove the
   prologue survives a body `none`. (deps: C, E)
9. **FILL I [XL] — widen the wire codec to the COMPLETE turn:** full `Turn` envelope, recursive
   action-tree grammar, the `Authorization` sum, all 52 effect tags + typed args, `args`/witness_blobs/
   preconditions, proof sidecars, the side-tables; widen `Value.dig`→ByteArray32 and cap target→256-bit;
   pin integer widths to dregg1 types. (deps: A, B, D, E)
10. **FILL J [L] — the parse∘encode roundtrip THEOREM** for every production (+ fuel-adequacy lemma),
    which removes the codec from the Lean-side TCB. *Entirely absent today.* (deps: I)
11. **FILL K [M] — committed golden-vector corpus** (canonical wire-in/wire-out byte pairs spanning
    every effect/mode/rollback/boundary/tree shape), asserted byte-for-byte in CI against BOTH the Lean
    export and the Rust reference — breaks the symmetric-codec-bug co-drift. (deps: I)
12. **FILL L [XL] — de-THIN the load-bearing mechanisms:** queue ring-buffer FIFO (6 ABSENT effects),
    CapTP swiss-table+refcount+handoff-merkle, factory constraint enforcement, committed-escrow
    Pedersen+range path (#121 regression) + release/refund (ABSENT), MakeSovereign, Refusal witness,
    ReceiptArchive, permission-effect-LAST ordering. (deps: B, E)

## The post-swap TCB line (crypto boundary — CONFIRMED)

**ASSUMED** (`@[extern]`-delegated to Rust, soundness via a Prop carrier — the §8 floor, ~8
primitives / ~24 elements): ed25519 EUF-CMA; STARK/FRI extractability; Pedersen binding (DLog) +
Schnorr-excess; Poseidon2 collision-resistance; BLAKE3 CR/preimage; nullifier derivation; AEAD+X25519;
HMAC-SHA256. **VERIFIED-IN-LEAN** (NOT in the TCB): ledger arithmetic + per-asset conservation; the
authority lattice / granted≤held non-amplification (Granovetter — a property dregg1 itself misses);
anti-double-spend (determinism of the derivation — a theorem; only *unlinkability* is assumed);
caveat-chain monotone attenuation; the auth-mode admit⇒Discharged soundness theorems; the
merkle/pedersen `verify_sound` bridges (accept⇒witness, already DERIVED given `extractable`); and —
once FILL J lands — the wire codec itself. *This is the seL4 boundary: verify the logic that uses
crypto, assume the crypto primitives. The line exists ONLY AFTER META-FILL E+F wire the portals in;
today the executed turn is crypto-free.*

## Single-cutover plan

1. **Build to parity behind the differential** (checklist in dep order; `turn/src/executor/` stays
   live, Lean is never the production path during build).
2. **Ratchet the differential to full surface** — evolve `full_turn_differential.rs` into a
   complete-turn differential (all 52 effects + 10 modes + tree + admission); make it a CI ratchet
   (monotone pass-count gate); **kernel-vs-intended-semantics, NEVER vs the buggy dregg1 oracle**
   (matching a buggy oracle launders the bug).
3. **Completeness gate** — cutover BLOCKED until: 0 ABSENT + 0 STRANDED for all soundness-critical
   elements; the roundtrip theorem (J) compiles sorry-free; the golden corpus (K) byte-equal in CI;
   the §8 portal set is exactly the documented floor with every discharge stated; the preimage
   differential (F) byte-exact green; the full-surface differential at 100%.
4. **Flip in one go** — replace the bodies of `turn/src/executor/{execute,execute_tree,apply,authorize}.rs`
   with thin marshallers that encode→`dregg_exec_full_turn`→decode; delete the hand-written Rust logic.
5. **Burn-in** — shadow mode (both execute, results compared, Lean discarded) across historical replay +
   live traffic; zero divergence for the window is the promotion gate; then flip authoritative, keep the
   old path as shadow one more window before deletion. Golden corpus + roundtrip theorem stay permanent
   CI ratchets.

## Biggest risks

- **Tree-shape structural debt** — A is the XL keystone; a flat-list lowering that doesn't genuinely
  re-prove the CrossCellForest no-amplify law over the dispatched world ships an authority-unsound executor.
- **Signing-message preimage mismatch (silent hole)** — a one-byte divergence verifies the wrong message
  while the differential (which never checks preimages) passes. FILL F is non-negotiable.
- **Codec is TCB and can co-drift** — without J (roundtrip theorem) + K (golden corpus) the only certified
  object is the bare `execFullTurn` term, not the wire boundary the swap crosses.
- **Stranded-proof false comfort** — "it's proved in EffectsPaired/AuthModes" is NOT coverage; porting
  surfaces integration mismatches (accounts must grow; conservation → chainTotal) the isolated proofs never faced.
- **Crypto floor entirely unrealized** — 0 real `@[extern]` bindings today; getting the §8 discharge
  statements wrong misrepresents the trust boundary.
- **Admission breaks purity** — the Phase-1 fee+nonce commit is never-rolled-back, the opposite of the
  pure all-or-nothing fold; botching the prologue-survives-body-`none` proof reopens replay or escapes the fee.
- **Oracle framing / burn-in** — differential must be kernel-vs-intended-semantics; never promote
  Lean-FFI authoritative without a zero-divergence shadow burn-in window.
