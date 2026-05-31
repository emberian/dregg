# SWAP-READINESS — how close is the Lean kernel to HOSTING a real turn-decision?

> **Read-only assessment (2026-05-31).** Scope: can `dregg2`'s verified Lean
> `execFullTurn` (hosted over the FFI) replace dregg1's `turn/src/executor/authorize.rs`,
> and what is the first *safe* rewiring step? Companion to `SUCCESSOR-ROADMAP.md`
> (Phase B, "execute the cascade, oracle-first"), `DREGG1-TO-DREGG2.md` (crate fates),
> `PHASE-EXTRACTION.md`. **No code was changed producing this.**
>
> **THE SWAP FRAMING (do not violate).** Deleting the Rust kernel and routing the node
> through the Lean FFI is a *massive staged rewrite*, NOT an FFI drop-in. It is gated on
> (1) the executor being complete, (2) the FFI hosting a real turn, (3) the differential
> as a safety net **kernel-vs-new-Rust, NEVER vs the buggy old dregg1** (matching a buggy
> oracle launders the bug). This doc recommends NO blind deletion.

## TL;DR readiness verdict

| Axis | Status | One-line |
|---|---|---|
| FFI hosts a turn-decision *function* | **READY** | `dregg_exec_full_turn` runs the PROVED `execFullTurn` from C; archive fresh; 9000-case differential is GREEN today (verified this session). |
| The hosted function = the node's *real* turn-decision | **NOT-YET** | `execFullTurn` is the abstract ledger/authority kernel (5 action kinds, cap-table authority). The node's `verify_authorization` is a 9-mode *cryptographic* gate over a 51-effect call-forest with nonce/fee/freeze/receipt-chain preamble. Different universe. |
| Differential is the staged-swap regression net | **READY-as-built, NEEDS-automation** | The net exists, runs clean (5000 structured + 4000 adversarial, 0 divergence, 3384 rollbacks). It is **kernel-vs-fresh-Rust-reference** (correct framing), but it is **NOT in CI** — the crate is workspace-detached, so it can silently rot. |
| Any Rust kernel code rewired to call Lean | **NOT-YET (zero)** | `grep` of `node/src` + `turn/src` + `bridge/src` for `dregg_exec_full_turn`/`dregg_lean`/`execFullTurn` returns **nothing**. The only consumer of the FFI is the differential harness itself. |

**Bottom line:** the FFI hosts *a* proved turn-decision and the safety net is live and
honestly-framed — but the hosted decision is a **model of the conservation+authority
core**, not the node's production authorization. We are READY to begin the *oracle-shadow*
rewiring (run Lean alongside Rust, compare, never trust) on the **conservation/ledger
sub-decision**; we are NOT-YET ready to route *authorization* through Lean, and deletion of
`authorize.rs` is gated on the cryptographic-authority and call-forest gaps below.

---

## (a) What the FFI carries vs. what a real node turn-decision needs

### What is `@[export]`-ed today (`metatheory/Dregg2/Exec/FFI.lean`)

Five C entry points, three "real" (string-codec) and two scalar PoC:
- `dregg_kernel_transfer_total` / `dregg_kernel_authorized` — scalar PoC (`FFI.lean:26`, `:42`).
- `dregg_record_kernel_step` / `_caps` — single `recKExec` step over a real `Value` record cell (`FFI.lean:369`, `:643`).
- **`dregg_exec_full_turn`** (`FFI.lean:936`) — **the swap-enabler.** Marshals a whole
  `(RecChainedState, List FullAction)` across a JSON wire grammar (`FFI.lean:715-734`), runs
  the PROVED `TurnExecutorFull.execFullTurn`, re-encodes the `Option` result *including the
  all-or-nothing rollback* (`ok:0` echoes unchanged pre-state, `FFI.lean:948-950`).

The C bridge (`dregg-lean-ffi/src/lean_init.c:28`,`:31`) boxes the string, does the
one-time Lean runtime init (`dregg_ffi_init`, `lean_init.c:31`), and exposes
`dregg_exec_full_turn_str`.

### What the hosted `execFullTurn` is (the model it carries)

`FullAction` (`metatheory/Dregg2/Exec/TurnExecutorFull.lean:255-265`) = **5 kinds**:
`balance` (a `TurnExecutor.Action` transfer), `delegate`, `revoke`, `mint`, `burn`.
Authority is the **abstract cap table**: `authorizedB` = `actor == src` OR a `node src` cap
OR an `endpoint src` cap carrying `write` (mirrored in the Rust reference at
`dregg-lean-ffi/src/full_turn_differential.rs:210-219`); mint/burn require a `node`/`control`
cap (`:223-229`). It carries genuine PROVED laws — `execFullTurn_ledger` (`TurnExecutorFull.lean:571`),
`execFullTurn_conserves` (`:592`), and step-completeness `execFullTurn_each_attests`
(`:600`: *every committed action attests `fullActionInv`*). This is real, machine-checked,
all-or-nothing transaction semantics.

### What the node's *real* turn-decision is (`turn/src/executor/`)

`TurnExecutor::execute` (`turn/src/executor/execute.rs:54`) is the entry the node calls. Its
authorization core is `verify_authorization` (`turn/src/executor/authorize.rs:8`), invoked per
action from `execute_tree` (`turn/src/executor/execute_tree.rs:489`). The gap is on three
axes, all large:

1. **Cryptographic authorization (the headline gap).** `Authorization`
   (`turn/src/action.rs:206`) has **9 variants**, *all cryptographic*: `Signature`
   (Ed25519), `Proof` (ZK/STARK with bound action+resource), `Breadstuff` (token hash),
   `Bearer` (delegation-chain proof), `CapTpDelivered` (introducer-signed handoff cert +
   sender sig), `Custom` (a `WitnessedPredicate` resolved through a registry), `OneOf`
   (disjunctive coproduct), `Stealth`, `Unchecked`. The Lean kernel's authority is an
   **abstract cap-table membership** — it models *whether the actor has the right*, not
   *the cryptographic proof that they do*. Signing-message construction
   (`authorize.rs:1750` `compute_signing_message`, `:1801` partial, `:1842` custom), bearer
   verification (`:1103` `verify_bearer_cap`), nonce/federation binding — none of this exists
   in `execFullTurn`. (By design: dregg2 keeps crypto out of the trusted Lean via the
   `CryptoKernel`/`World` portals — see `SUCCESSOR-ROADMAP.md`.)

2. **The effect catalog.** The node's `Effect` enum (`turn/src/action.rs:760`) has **51
   variants** — `Transfer`, `GrantCapability`, `RevokeCapability`, `CreateCell`,
   `NoteSpend`/`NoteCreate`, `Seal`/`Unseal`, bridge mint/lock/finalize, escrow create/release/
   refund (+ committed variants), obligations, queues, CapTP export/enliven/drop, factory,
   sovereign, attenuate, burn, … The FFI carries **5 abstract kinds**, and even those
   ignore the `method`/`effect` tag in the balance branch (`FFI.lean:740-755`, faithfully
   round-tripped but unread). Note: the *EffectsPaired/EffectsState/EffectsSupply* Lean
   modules model ~50 effects' conservation (task E3-breadth, #104) — but `execFullTurn`/the
   FFI expose only the 5-kind ledger surface.

3. **The pre-authorization turn preamble.** `execute` (`execute.rs:54-173+`) rejects on
   empty forest, expiration (`valid_until`), nonce replay (`:88`), fee coverage (`:99`),
   migration-freeze of agent and write-set cells (`:112-131`), receipt-chain self-binding
   (`:145`), and the Stingray budget gate (`:159`). `execFullTurn` has *none* of these — it
   is the pure ledger+authority core that runs *after* admission.

**Mapping (the swap's coordinate transform that does not yet exist):** there is no
`Turn → wire-string` encoder and no `Authorization-decision → cap-table` reduction in Rust.
A real swap needs (i) a `CryptoKernel` Rust impl discharging the crypto the Lean portal
abstracts, (ii) a `Turn`/`Effect` → `List FullAction` lowering (or a widened `FullAction`),
(iii) the preamble kept Rust-side (admission control) or modeled. None exist.

## (b) Gap: "execFullTurn runs via FFI" → "the node routes authorization through Lean"

These are **two different milestones** and only the first is done.

- **Done:** `execFullTurn` *runs* via FFI, deterministically, all-or-nothing, with the
  proved laws attached, and a Rust reference agrees with it on 9000 cases (this session,
  see §d).
- **Not started:** *zero* production code calls it. `node/src/api.rs` builds a
  `dregg_turn::TurnExecutor` and calls `.execute(...)` directly (`api.rs:1879`, `:2122`,
  `:2518`, `:3512`, `:3797`, `:3992`, `:5451`); the cipherclerk authorize endpoint
  (`api.rs:1451` `post_authorize`) calls `s.cclerk.verify_token`. None of these touch the
  FFI. The bridge between "a proved function I *can* call from C" and "the gate the node
  *does* call" is the entire unbuilt span: a `CryptoKernel` impl, a `Turn`→wire lowering,
  and a shadow/compare harness inside the node process.

The honest size of this gap: the FFI is the **last 5%** of "make the proved kernel
*callable*"; routing authorization through it is the **first 5%** of a multi-phase rewrite
whose bulk is (1) modeling cryptographic authority faithfully in Lean (or proving the
portal discharge sound) and (2) covering the call-forest/effect breadth.

## (c) READY-to-rewire vs NEEDS-more vs NOT-YET (per Rust kernel surface)

**READY to rewire now (low-risk, behind the differential — oracle-SHADOW only):**
- **The conservation/ledger sub-decision of a balance-only turn.** Where the node computes
  "does this transfer/mint/burn conserve and is the actor cap-authorized over `src`", the
  Lean `execFullTurn` is a faithful, proved oracle. SAFE first step: a **shadow call** that
  lowers the balance-subset of a turn to the wire form, calls `dregg_exec_full_turn`, and
  **compares (logs/asserts) — never decides**. This is pure observation; if Lean and Rust
  disagree on a real turn, that is a *finding*, and the Rust path remains authoritative.
- **The single-step record-cell transfer** (`dregg_record_kernel_step`) as a shadow over the
  `Transfer` effect's balance write specifically.

**NEEDS-more executor/FFI work before even shadowing:**
- **Cap delegation/revocation** decisions — the FFI carries `delegate`/`revoke` and proves
  `execFull_delegate_addEdge`/`_revoke_removeEdge` (`TurnExecutorFull.lean:424`,`:444`), but
  the Rust cap kernel (derivation/attenuation chains, `verify_bearer_cap`) is far richer.
  Shadow only after a `Bearer`/`GrantCapability` → cap-edge lowering exists and is
  differential-validated.
- **Multi-action / call-forest turns** — `execFullTurn` is a flat `List FullAction`; the
  node's `execute_tree` is a *tree* with per-node parent/path authorization. Needs a
  forest→list lowering (or a tree-shaped Lean executor) first.

**NOT-YET (gated on real model work — do not rewire, do not shadow):**
- **All cryptographic authorization** (`Signature`/`Proof`/`Bearer`/`CapTpDelivered`/
  `Custom`/`Token`/`OneOf`/`Stealth`). The Lean kernel has no notion of these; it models the
  *right*, not the *proof*. Gated on a `CryptoKernel` Rust impl + the portal-discharge
  argument (`PHASE-CRYPTO-TCB.md`).
- **The 46 non-ledger effects** (notes, seals, bridges, escrow, obligations, queues, CapTP
  transport, factory, sovereign). Gated on exposing those Lean modules through the FFI
  surface (they are modeled but not `@[export]`-ed) and a `Effect`→action lowering.
- **The admission preamble** (nonce/fee/freeze/receipt-chain/budget). Either kept
  Rust-side permanently (admission ≠ kernel) or modeled — a design call, not a rewiring.

## (d) Differential-ratchet safety-net status — IS it the regression net for a staged swap?

**Yes, in construction; not yet as an automated ratchet.**

- **It exists and is GREEN (verified this session).** Built `full_turn_differential`
  (`dregg-lean-ffi/src/full_turn_differential.rs`) clean against the fresh
  `libdregg_lean.a` (archive 05:59 ≥ `FFI.lean` 05:56 — current) and ran it:
  - `5000/5000` structured multi-action turns agree, **3384 all-or-nothing rollbacks
    observed** (`N_STRUCTURED = 5_000`, `full_turn_differential.rs:809`);
  - `4000` adversarial proptest cases, **0 divergences** after minimization
    (`N_FUZZ = 4_000`, `:1067`) — overflow/underflow amounts straddling the i64 boundary
    (`:1016`), unauthorized delegates, double-mints, empty/huge/mis-ordered action lists
    (`:1060-1064`);
  - 4 explicit witness cases (mixed net-0 commit, mid-turn-fail rollback, delegate+revoke
    cap mutation, empty turn) all agree.
  - **5000 + 4000 = the "9000-case" net.** Exit 0; banner: "the proved turn-decision runs
    from Rust."
- **The framing is CORRECT.** The Rust side is a *fresh faithful reference reimplementation*
  of `execFull`/`execFullTurn` (`:257`), NOT the buggy dregg1 `turn` crate. Agreement
  cross-validates **kernel vs new-Rust**, exactly the swap-safe orientation; the harness
  doc states it plainly (`full_turn_differential.rs:24-28`): agreement does NOT certify the
  Rust reference (only Lean carries proofs) and does NOT prove the codec (a bug corrupting
  both sides identically passes). It is the *empirical* layer under the proved core.
- **The gap: it is NOT a ratchet yet.** The crate has an empty `[workspace]` table
  (`dregg-lean-ffi/Cargo.toml`) detaching it from the repo workspace, and the workspace CI
  (`.github/workflows/ci.yml`: `cargo check/test/clippy --workspace`, lines 23/40/53) never
  builds or runs it. The `libdregg_lean.a` archive is hand-rebuilt (8200 `.o` from `leanc`,
  per `build.rs`). So the net **runs only when a human runs it**, and can silently rot when
  `FFI.lean` or the kernel changes. A regression *net* that isn't wired to a trigger is a
  one-shot, not a ratchet.

**Verdict:** the differential IS the right safety net for a staged swap (right framing,
real adversarial coverage, green today) — but to be the *ratchet* a staged swap needs, it
must (1) auto-rebuild the archive when `Dregg2/Exec/**` changes and (2) run in CI as a
required check, blocking merges on any divergence.

---

## The exact FIRST SAFE rewiring step (do this, nothing more)

**Oracle-SHADOW the balance-conservation sub-decision — observe, never decide.**

1. **Make the net a ratchet first (prerequisite, no node change).** Add a CI job that, on
   any change under `metatheory/Dregg2/Exec/**` or `dregg-lean-ffi/**`, rebuilds
   `libdregg_lean.a` and runs `full_turn_differential` as a *required* check. Until the net
   is automated, do not rewire anything — a stale oracle is worse than none.
2. **Add a feature-gated shadow in the node, off by default.** Behind a
   `lean-shadow` cargo feature (default off, never in the consensus path), after the Rust
   `execute` decides a *balance-only* turn (transfer/mint/burn, no caps, no crypto modes
   beyond the actor owning `src`), lower that turn to the `dregg_exec_full_turn` wire form,
   call the FFI, and **compare** the commit-bit + post-balances. On mismatch: increment a
   metric and log loudly (`node/src/metrics.rs`); **do not alter the decision**. The Rust
   path stays 100% authoritative.
3. **Promote to a differential corpus.** Feed real turns observed in the shadow back into
   `full_turn_differential` as regression seeds. Drive divergences to zero on *production
   traffic shapes* (not just generated ones) — this is the "100% on real inputs" of
   `SUCCESSOR-ROADMAP.md` Phase B, on the balance subset.

This step is reversible (a feature flag), cannot affect consensus (observe-only), and
extends the existing, honestly-framed net rather than trusting Lean prematurely.

## What gates the actual Rust deletion (`authorize.rs` removal)

Deletion of `verify_authorization`/`authorize.rs` is gated on **all** of:

1. **Cryptographic authority modeled or portal-discharged.** A `CryptoKernel` Rust impl
   (Ed25519/STARK/Pedersen/Poseidon) whose discharge of the Lean portal laws is argued
   sound (`PHASE-CRYPTO-TCB.md`), so the 9 `Authorization` modes reduce to verified
   cap-table facts the Lean kernel consumes. Until then, *the security-critical half of
   `authorize.rs` has no Lean counterpart at all.*
2. **Call-forest + effect-catalog parity.** A `Turn`/`Effect`-tree → Lean-executor lowering
   covering the 51 effects (the modeled Lean effect modules `@[export]`-ed), differential
   at 100% on real inputs including the tree-shaped per-node authorization.
3. **Admission preamble decided.** Nonce/fee/freeze/receipt-chain/budget either kept
   permanently Rust-side (admission control is legitimately not the kernel) or modeled —
   explicitly chosen, not left implicit.
4. **The differential is a green required CI ratchet** over the full surface (not just the
   5-kind ledger), with the archive auto-rebuilt, at 0 divergence on a real-traffic corpus.
5. **A staged cutover with the Lean path authoritative behind the differential for a
   burn-in window** — shadow → canary (Lean decides, Rust shadows, divergence = halt) →
   primary — *before* the Rust code is removed. Delete last, never first
   (`SUCCESSOR-ROADMAP.md`: "Frozen v1 stays until its check is oracle-equal").

Anything short of all five and the deletion launders an unverified gap into the TCB.

---

## Evidence index (file:line)

- FFI exports: `metatheory/Dregg2/Exec/FFI.lean:26,:42,:369,:643,:936`; wire grammar `:715-734`,
  rollback `:948-950`; effect-tag round-trip (unread) `:740-755`.
- C bridge: `dregg-lean-ffi/src/lean_init.c:28,:31` (`dregg_exec_full_turn`/`_str`), init `:31`.
- Proved kernel: `metatheory/Dregg2/Exec/TurnExecutorFull.lean` — `FullAction` `:255-265`,
  `execFullTurn` `:290`, laws `_ledger:571`, `_conserves:592`, `_each_attests:600`,
  delegate/revoke edge laws `:424,:444`.
- Node's real decision: `turn/src/executor/execute.rs:54` (`execute`); preamble `:56-173`;
  `turn/src/executor/authorize.rs:8` (`verify_authorization`), bearer `:1103`, signing-msg
  `:1750,:1801,:1842`; tree dispatch `turn/src/executor/execute_tree.rs:489`.
- Authorization modes (9, cryptographic): `turn/src/action.rs:206`. Effect catalog (51):
  `turn/src/action.rs:760`.
- No FFI wiring in node/turn/bridge: `grep` for `dregg_exec_full_turn|dregg_lean|execFullTurn`
  in `node/src node/turn/src bridge/src` → empty. Node calls `.execute` directly:
  `node/src/api.rs:1879,:2122,:2518,:3512,:3797,:3992,:5451`; cclerk `:1451,:1468`.
- Differential net: `dregg-lean-ffi/src/full_turn_differential.rs` — Rust reference `:257`,
  authority mirror `:210-229`, `N_STRUCTURED=5_000:809`, `N_FUZZ=4_000:1067`, honesty note
  `:24-28`. **Run this session:** 5000/5000 + 4000/0-divergence + 3384 rollbacks, exit 0.
- Not a ratchet: detached `[workspace]` in `dregg-lean-ffi/Cargo.toml`; CI never runs it
  (`.github/workflows/ci.yml:23,:40,:53` are `--workspace` only). Archive fresh:
  `libdregg_lean.a` 05:59 ≥ `FFI.lean` 05:56.
