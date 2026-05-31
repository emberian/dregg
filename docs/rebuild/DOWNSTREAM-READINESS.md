# DOWNSTREAM-READINESS — what the consumers need for the Lean-kernel SWAP

> **Read-only assessment.** No code changed. Companion to `DREGG1-TO-DREGG2.md` §A/§B
> (crate fates + the SDK split), `PHASE-EXTRACTION.md` (the FFI Path-A mechanism +
> wasm/cross-compile opens), and `SUCCESSOR-ROADMAP.md` (Phases A–D). This doc answers:
> *what do the SDK, discord-bot, and the other turn/authorize/prove consumers need when
> the executor routes through the Lean FFI kernel — and what is interface-stable enough
> to do now vs. gated on the swap.*
>
> **The SWAP framing is binding (do NOT violate).** Routing the node through the Lean
> FFI is a MASSIVE staged rewrite, NOT an FFI drop-in. It is gated on (1) the verified
> executor covering the *real* turn shape, (2) the FFI hosting a *real* turn, and (3) the
> differential as the safety net — kernel-vs-new-Rust, NEVER vs. the buggy old dregg1.
> Nothing here recommends blind deletion of the Rust kernel.

---

## 0. The one-paragraph answer

The turn/authorize/prove *semantics* live in exactly four Rust surfaces that consumers
touch: **`dregg_turn::TurnExecutor`** (the kernel — `execute` / `apply_encrypted_turn` /
`compute_signing_message`), the **`dregg_sdk` runtime/cipherclerk** (turn *construction* +
the in-process executor), the **`dregg-node` HTTP surface** (`/turn/submit`,
`/cipherclerk/authorize`, fast-path, conditional, encrypted), and the **prover** (the
`circuit` STARK pipeline reached via `sdk::full_turn_proof` and `wasm::prove_turn`). When
the swap happens, **only the *semantics* (admissibility / post-state / conservation /
authority) move behind the FFI** — turn *construction* (keys, tokens, signing, receipt
chain) stays Rust per `DREGG1-TO-DREGG2.md:87-104`. The good news: **every "operator /
agent / bot / CLI" consumer is already insulated** — they go through the SDK
cipherclerk's *construction* API or through the node's *HTTP* boundary, neither of which
exposes `TurnExecutor` as a type in its signature. The hard cases are the **two crates
that embed a `TurnExecutor` in-process**: `dregg-sdk`'s `AgentRuntime`
(`sdk/src/runtime.rs:61`) and the `dregg-wasm` `DreggRuntime` (`wasm/src/runtime.rs:304`).
And the **decisive blocker for the SDK/wasm runtime is that the FFI cannot cross-compile
to wasm32** (it links a 247 MB native Lean archive + the Lean runtime — `gmp`/`uv`/`c++`).

---

## 1. The kernel-dependency surface (who calls what)

Three semantic entry points; everything else is construction or transport.

### 1a. `dregg_turn::TurnExecutor` — the kernel that the swap replaces
The thing the Lean FFI (`dregg_exec_full_turn`) is meant to become the oracle for, then
host. Its semantic methods:
- `TurnExecutor::execute(&turn, &mut ledger) -> TurnResult` — the all-or-nothing turn
  decision (admissible? post-state?). This is `execFullTurn` in Lean
  (`metatheory/Dregg2/Exec/FFI.lean:936`, the `@[export] dregg_exec_full_turn`).
- `TurnExecutor::apply_encrypted_turn(...)` — node-only encrypted path
  (`node/src/api.rs:2523`). **No Lean analog yet** (the FFI marshals cleartext
  `RecChainedState` only — `FFI.lean:923-951`).
- `TurnExecutor::compute_signing_message(action, &federation_id)` — **pure, construction-side**,
  NOT semantics. Used by the SDK runtime (`sdk/src/runtime.rs:254,659`), the app-framework
  authorizer (`app-framework/src/authorizer.rs:120`), and the discord-bot intent flow
  (`discord-bot/src/intent_flow.rs:91`). This **stays Rust** and **does not move** — it
  computes the bytes that get signed, which is local cryptographic bookkeeping.
- `set_last_receipt_hash` / `set_local_federation_id` / `set_budget_gate` — executor
  configuration the runtime drives (`sdk/src/runtime.rs:128,211,217`; `node/src/api.rs:1698`).

### 1b. The authorizer
- Node: `/cipherclerk/authorize` → `s.cclerk.verify_token(token, &auth_req)`
  (`node/src/api.rs:1238,1468`). This is token/caveat evaluation (`cell::predicate`
  registry), which `DREGG1-TO-DREGG2.md:160+` maps onto the `Laws.Verifiable` seam — a
  **separate, later** migration from the turn executor.
- SDK / app-framework: `AgentCipherclerk::authorize(token, request, mode)` and the
  `Authorizer` trait (`app-framework/src/authorizer.rs:72-77`, used by `escrow.rs:152`).
  These produce/check `Authorization`s **at construction time**; they stay Rust.

### 1c. The prover
- SDK: `sdk::full_turn_proof::{prove_full_turn, prove_turn_with_auth, verify_full_turn}`
  (re-exported `sdk/src/lib.rs:186-189`) over the `circuit` STARK pipeline.
- wasm: `DreggRuntime::prove_turn` (`wasm/src/runtime.rs:670`) → `circuit::stark::prove`.
- node: `aggregate_bilateral_prover::prove_aggregated_bundle` (`node/src/api.rs:2398`),
  `circuit::stark::try_prove` (`node/src/api.rs:1805`).
- **The prover NEVER moves into Lean** (`SUCCESSOR-ROADMAP.md` / `DREGG1-TO-DREGG2.md:265`:
  "Never reimplement the prover in Lean"). Lean *emits the AIR / constraint semantics*
  (Task #90 W9-CIRCUIT-SEM); the Rust circuit crate keeps proving. So the prover surface
  is **swap-neutral** — no consumer change is forced by the kernel swap.

---

## 2. Per-consumer dependency table

| Consumer | How it reaches the kernel | Insulated by | Swap impact |
|---|---|---|---|
| **`cli`** | Pure HTTP: `post_json(cfg, "/turn/submit", ...)` (`cli/src/commands/turn.rs:49,388`). **Zero `dregg-*` deps** (`cli/Cargo.toml` — only clap/reqwest/serde). | The node HTTP boundary | **None.** The swap is invisible behind `/turn/submit`. CLI is the *template* for swap-safety. |
| **`discord-bot`** | `AppCipherclerk` (construction) + `submit_transfer_turn` to a node (`discord-bot/src/commands/transfer.rs:165`); HTTP read surface for RemoteRuntime (`http_server.rs`). Uses `compute_signing_message` (construction-side) at `intent_flow.rs:91`. | `dregg-app-framework` → SDK construction API + the node HTTP boundary | **None forced.** It never holds a `TurnExecutor`. Semantics are the node's job. |
| **`demo` / `demo-agent`** | Construction + `cclerk.authorize(...)` (e.g. `demo-agent/examples/unified_harness.rs:603`); circuit `verify_authorization_dsl`. Depend on `dregg-turn`/`dregg-sdk`/`dregg-circuit` directly. | SDK + circuit verify APIs | **Low.** Examples that build `Turn`/`Effect` structs by hand are exposed *only* if those types change shape (see §3). The verify/authorize calls are unaffected. |
| **`app-framework`** | `AppCipherclerk` wraps `AgentCipherclerk` + `AgentRuntime` (`app-framework/src/cipherclerk.rs:54,68`); `Authorizer` trait (construction). `EscrowManager` etc. emit signed actions. | SDK construction surface | **Low–Medium.** Inherits the SDK runtime's executor transitively (via `AgentRuntime`). If an app uses the embedded `AgentRuntime::execute`, it inherits the SDK's swap story (§4). |
| **`node`** | **9 direct `TurnExecutor::new(...)` sites** + `execute` / `apply_encrypted_turn` (`api.rs:1879,1881,2122,2124,2518,2523,3512,3797,3992,5451`). The federation daemon that *runs* turns. | Nothing — it IS the host | **HIGH.** This is the FFI-shim host (`DREGG1-TO-DREGG2.md:54,256`). Each `execute` site re-seats onto the FFI'd kernel. The *HTTP request/response types stay stable* so CLI/bot/RemoteRuntime don't notice. |
| **`sdk` (`AgentRuntime`)** | Embeds a `TurnExecutor` (`sdk/src/runtime.rs:61`), calls `executor.execute(&turn, &mut ledger)` for **local/offline** execution (`runtime.rs:313,359,691`). | Nothing — it embeds the kernel | **HIGH + wasm-blocked.** The local executor is the load-bearing swap surface AND the one that must run in-browser (§4, §5). |
| **`wasm` (`DreggRuntime`)** | Embeds a `TurnExecutor` (`wasm/src/runtime.rs:304`), `executor.execute` in-browser; `prove_turn` runs a real STARK in wasm (`runtime.rs:670`). | Nothing — it embeds the kernel | **HIGHEST.** Same as SDK runtime, but on wasm32 where the FFI archive cannot link (§5). |
| **`sdk-ts` / `extension` (TS)** | Thin TS client → node endpoints (`DREGG1-TO-DREGG2.md:137-139`). | Node HTTP boundary | **None.** "No TS reimplementation of semantics." Same as CLI. |

**Today nobody links `dregg-lean-ffi`** (verified: no `Cargo.toml` references it except its
own). It is a detached PoC crate with an empty `[workspace]` (`dregg-lean-ffi/Cargo.toml:5`).
The first real consumer is meant to be `verifier`, then `node` (`DREGG1-TO-DREGG2.md:71,218`).

---

## 3. The interface that must STAY STABLE vs. what SHIFTS

### Stays stable (the contract consumers code against)
1. **The node HTTP API shapes** — `SubmitTurnRequest`/`SubmitTurnResponse`
   (`node/src/api.rs:1821-1869`), `/cipherclerk/authorize`, fast-path, conditional,
   encrypted endpoints. CLI, discord-bot, sdk-ts, extension, RemoteRuntime all bind to
   these. **The swap must preserve them byte-for-byte** so the whole product surface above
   the node is swap-invisible. This is the single most important stability boundary.
2. **`compute_signing_message`** (construction-side, pure) — the SDK, app-framework, and
   bot all depend on its exact byte layout. It does NOT move into Lean; it must keep
   producing identical bytes or every existing signature/receipt chain breaks.
3. **`AgentCipherclerk` construction API** (mint/attenuate/sign/receipt-chain) — the
   "construction stays Rust" half of the SDK split (`DREGG1-TO-DREGG2.md:90-96`).
4. **`TurnReceipt` / `WitnessedReceipt` shapes + `verify_receipt_chain`** — re-exported
   at `sdk/src/lib.rs:150-153,203-206`. Receipts are the cross-process artifact;
   their encoding must survive the swap (the Lean kernel must produce receipts that the
   existing verifier accepts, or the verifier moves in lockstep).

### Shifts (the semantics that move behind the FFI)
1. **`TurnExecutor::execute` answer** — "is this turn admissible + what is the post-state"
   becomes a call to `dregg_exec_full_turn` (`FFI.lean:936`). The *Rust type signature*
   `execute(&Turn, &mut Ledger) -> TurnResult` can be preserved as a thin shim that
   marshals to the FFI; the *implementation* moves.
2. **The `Turn` / `Effect` / `Ledger` ↔ Lean wire codec** — currently the FFI marshals a
   JSON `{cells, caps, actions}` of `RecChainedState` + `List FullAction`
   (`FFI.lean:923-951`). Consumers that build raw `Turn { ... }` structs (the SDK runtime
   `runtime.rs:292`, node `api.rs:1851`, wasm) feed those into the codec. As the Lean
   `FullAction` grows (§6), the codec — NOT the consumer — absorbs the change.

---

## 4. The SDK `AgentRuntime` — the load-bearing change

`AgentRuntime` (`sdk/src/runtime.rs:51-64`) does BOTH jobs the SDK split must cleave:
- **Construction** (stays): builds the unsigned `Action` (`runtime.rs:239-250`), computes
  the signing message (`:254`), signs with the cipherclerk (`:258`), assembles the `Turn`
  (`:292-310`), appends the receipt to the chain (`:322-325`). All local crypto bookkeeping.
- **Semantics** (moves): `self.executor.execute(&turn, &mut ledger)` (`runtime.rs:313`)
  and `SubAgent::execute` (`runtime.rs:691`). This is where the runtime *decides* a turn —
  and where it must call the FFI-hosted kernel after the swap.

**What it needs at the swap:** a feature-gated executor backend. The runtime keeps its
exact public API (`execute(Vec<Effect>) -> Result<TurnReceipt>`, `execute_turn`,
`spawn_sub_agent`) but, behind a `kernel-ffi` feature, routes `execute` through the
FFI shim instead of the in-process Rust `TurnExecutor`. The **differential is the gate**:
ship the FFI backend only after the harness proves `Rust-TurnExecutor ≡ Lean-oracle` on
the real turn domain (the new-Rust-vs-kernel framing, never vs. dregg1).

**What can be done NOW (interface-stable, pre-swap):**
- (a) Make the executor backend a trait/enum boundary inside `AgentRuntime` so the FFI
  backend can drop in without touching the public API. Today it is a concrete field
  (`executor: TurnExecutor`, `runtime.rs:61`).
- (b) Extend `dregg-lean-ffi`'s `full_turn_differential` to mirror the SDK's *actual*
  effect set, not just transfer/mint/burn/delegate/revoke (§6). The Rust reference there
  is already a "faithful mirror" (`PHASE-EXTRACTION.md:98`); grow it to the SDK domain.
- (c) Nothing about construction needs to wait — keys/tokens/signing/receipts are already
  the right shape.

---

## 5. The wasm32 constraint — the decisive blocker for SDK runtime + wasm

The `dregg-wasm` `DreggRuntime` embeds a `TurnExecutor` (`wasm/src/runtime.rs:304,440`)
and runs `execute` *in the browser*. The SDK is already wasm-aware: `dregg-sdk` gates
tokio/wire/captp behind features so it builds with `default-features = false`
(`sdk/Cargo.toml:53-66`; `sdk/src/lib.rs:81-105`), and wasm pulls `dregg-turn`/`dregg-cell`
with default features off (`wasm/Cargo.toml:27-31`).

**The FFI cannot follow them to wasm32.** `dregg-lean-ffi/build.rs` links:
- a **247 MB native static archive** `libdregg_lean.a` — compiled Lean objects for the
  whole transitive closure (Dregg2 + mathlib + batteries + aesop + Qq, ~8200 `.o`,
  `PHASE-EXTRACTION.md:36`), and
- the **Lean runtime + stdlib**: `leancpp`, `Init`, `Std`, `Lean`, `leanrt`, `Lake`,
  **`gmp`**, **`uv`**, and **`dylib=c++`** (`build.rs:54-58`).

`gmp`, `libuv`, and the native C++ runtime are not wasm32 targets, and the archive is a
native-object blob. `PHASE-EXTRACTION.md:289` names "wasm32 cross-compilation of compiled
Lean" as an explicit **open engineering problem**. So:

**Consequence for the swap:** there is **no in-browser Lean kernel** on the FFI Path A.
The browser keeps the Rust `TurnExecutor` (`DREGG1-TO-DREGG2.md:53` explicitly marks `wasm`
**STAY-RUST** — "compiles the Rust portal impl … could also host wasm-compiled Lean later").
Three honest options, in preference order:
1. **wasm runtime delegates semantics to the node** (the CLI/extension pattern) — the
   browser builds+signs the turn locally, the node (which links the FFI) decides it. This
   is the cleanest swap-coherent path and matches `DREGG1-TO-DREGG2.md:139`.
2. **wasm runtime keeps the Rust `TurnExecutor`** as a *differentially-validated* local
   fast-path (Rust ≡ Lean asserted off-line in CI), accepting that the in-browser path is
   the Rust mirror, not the verified kernel itself.
3. **(research) wasm-compiled Lean** — a separate Path; out of scope for the near-term swap.

**Do NOT** try to link the FFI into wasm. The SDK's `default-features=false` wasm build must
*never* gain a `dregg-lean-ffi` dependency; any `kernel-ffi` feature added to `dregg-sdk`
(§4a) must be a **non-wasm32, non-default** feature, mutually exclusive with the wasm build.

---

## 6. The coverage gap that GATES the swap (kernel-side, but it bounds consumers)

The Lean FFI today decides a `List FullAction` with **5 shapes**: `balance` (transfer),
`delegate`, `revoke`, `mint`, `burn` (`metatheory/Dregg2/Exec/TurnExecutorFull.lean:255-265`,
mirrored in the wire at `FFI.lean:909-914`). The Rust `Effect` enum has **~50–70 variants**
(`turn/src/action.rs:760`; ~70 record-struct arms counted). Until the verified executor +
the FFI wire cover the effect set a given consumer actually emits, that consumer **cannot**
route through the FFI kernel — its turns would fail-closed at the codec.

**Implication for downstream readiness:** the swap is **per-effect-class staged**, and a
consumer is swap-ready exactly when *all the effects it emits* are FFI-covered.
- `cli` / `discord-bot` transfers → already covered (balance/transfer + mint/burn). These
  could ride an FFI'd node first.
- SDK `AgentRuntime::execute(vec![Effect::IncrementNonce { ... }])` (`runtime.rs:48`) and
  the wasm runtime's `CreateCell`/`CreateCellFromFactory` (`wasm/src/runtime.rs:955,1069`)
  emit effects with **no Lean analog yet** — gated on `SUCCESSOR-ROADMAP.md` Phase A
  (grow the verified kernel to the real cell/effect shape) and the E3-breadth effect
  catalog (Task #104) reaching the FFI wire.
- The **encrypted** (`apply_encrypted_turn`, `node/src/api.rs:2523`) and **conditional**
  (`api.rs:3992`) node paths have no FFI export at all — last to swap.

---

## 7. What is interface-stable NOW vs. gated on the swap

### Can do now (no swap, no risk, prepares the seam)
- **N1.** Make `AgentRuntime`'s executor a backend boundary (trait/enum) without changing
  its public API (`sdk/src/runtime.rs:61`). Pure refactor; enables a future `kernel-ffi`
  feature to drop in.
- **N2.** Freeze + document the node HTTP contract (`SubmitTurnRequest/Response` et al.,
  `node/src/api.rs:1821+`) as the *stability boundary* — add a contract test so the swap
  cannot silently alter the wire the CLI/bot/extension depend on.
- **N3.** Grow `dregg-lean-ffi/full_turn_differential.rs` to mirror the *real* SDK/node
  effect set and the encrypted/conditional shapes, and **wire a real fuzzer to the Path-A
  oracle** (`PHASE-EXTRACTION.md:202` calls this "the single sharpest near-term
  improvement"). This is the safety net that must exist *before* any swap.
- **N4.** Confirm `compute_signing_message` byte-stability under a golden vector so the
  construction-side surface is provably unchanged across the swap.
- **N5.** Add a CI guard that `dregg-sdk --no-default-features` (the wasm config) and
  `dregg-wasm` **never** transitively pull `dregg-lean-ffi` (§5 invariant).
- **N6.** Adopt the **wasm-delegates-to-node** pattern for any new wasm semantics
  (don't deepen the in-browser executor's reach), so the wasm runtime's swap story stays
  option-1 (§5).

### Gated on the swap (do NOT do until the gate is met)
- **G1.** Route the SDK `AgentRuntime::execute` through the FFI — gated on (a) the FFI
  covering the SDK's effect set (§6), (b) the differential proving `Rust ≡ Lean` on that
  set, (c) a non-wasm32 feature flag.
- **G2.** Re-seat the **9 node `TurnExecutor` sites** onto the FFI-shim — gated on the same
  per-effect coverage, staged effect-class by effect-class, HTTP contract held fixed (N2).
- **G3.** Encrypted + conditional node paths — gated on FFI exports that don't exist yet.
- **G4.** Any in-browser verified kernel — gated on the wasm-compiled-Lean research path
  (`PHASE-EXTRACTION.md:289`); not on the critical path. Until then wasm is STAY-RUST.
- **G5.** Authorizer/predicate migration (`/cipherclerk/authorize`, `Authorizer` trait) —
  a *separate* seam (`Laws.Verifiable`, `DREGG1-TO-DREGG2.md:160+`), not the turn-executor
  swap; sequence after the executor.

---

## 8. Sequencing (braided, swap-safe)

1. **Hold the boundaries (now):** N2 (HTTP contract test) + N4 (signing-message golden) +
   N5 (wasm-no-FFI CI guard). These make the swap *non-observable* to CLI/bot/extension/
   sdk-ts and lock the construction surface.
2. **Build the net (now):** N3 — grow the differential + fuzzer to the real effect set and
   the encrypted/conditional shapes. Kernel-vs-new-Rust, never vs. dregg1.
3. **Prepare the seam (now):** N1 — executor backend boundary in `AgentRuntime`.
4. **Swap the node, effect-class by effect-class (gated):** G2, starting with
   transfer/mint/burn/delegate/revoke (already FFI-covered), HTTP contract frozen. CLI,
   discord-bot, sdk-ts, extension see **nothing change** — that is the success criterion.
5. **Swap the SDK local executor (gated):** G1, behind a non-wasm `kernel-ffi` feature,
   once its effect set is covered + differentially equal.
6. **wasm stays Rust** (option-1 delegation for new semantics); G4 is a later research arc.
7. **Encrypted/conditional (G3) and the authorizer seam (G5)** last.

---

## 9. Bottom line per consumer

- **`cli`, `discord-bot`, `sdk-ts`, `extension`:** ready now, by virtue of the node HTTP
  boundary. They need **no change** at the swap as long as the HTTP/signing contracts hold
  (N2, N4). They are the proof that the swap can be product-invisible.
- **`demo` / `demo-agent` / `app-framework` apps:** low impact; only exposed if `Turn`/
  `Effect` struct shapes change (they shouldn't — the codec absorbs the Lean side). Apps on
  the embedded `AgentRuntime` inherit the SDK story (G1).
- **`node`:** the host; HIGH impact, staged (G2), but its *callers* don't notice.
- **`dregg-sdk` `AgentRuntime`:** the load-bearing change — split construction (stays) from
  semantics (FFI), behind a feature, gated on coverage + differential (N1 → G1).
- **`dregg-wasm`:** highest impact, but the **FFI cannot go to wasm32** (247 MB native Lean
  archive + gmp/uv/c++). It STAYS RUST and either delegates semantics to the node or keeps a
  differentially-validated Rust fast-path. The wasm-no-FFI invariant (N5) is non-negotiable.

---

*Cited surfaces:* `sdk/src/runtime.rs:51,61,254,313,659,691`; `sdk/src/lib.rs:81-105,150-153,186-189`;
`sdk/Cargo.toml:53-66`; `node/src/api.rs:1238,1468,1821-1869,1879,2523,3992`;
`wasm/src/runtime.rs:304,440,670,955`; `wasm/Cargo.toml:27-31`; `cli/src/commands/turn.rs:49,388`;
`cli/Cargo.toml`; `discord-bot/src/commands/transfer.rs:165`; `discord-bot/src/intent_flow.rs:91`;
`discord-bot/src/cipherclerk.rs:30,84`; `app-framework/src/authorizer.rs:72-77,120`;
`app-framework/src/cipherclerk.rs:54,68`; `metatheory/Dregg2/Exec/FFI.lean:923-951,936`;
`metatheory/Dregg2/Exec/TurnExecutorFull.lean:255-265`; `turn/src/action.rs:760`;
`dregg-lean-ffi/Cargo.toml:5`; `dregg-lean-ffi/build.rs:54-58`;
`docs/rebuild/DREGG1-TO-DREGG2.md:52-104,137-139,160+,256,265`;
`docs/rebuild/PHASE-EXTRACTION.md:36,98,202,289`.
