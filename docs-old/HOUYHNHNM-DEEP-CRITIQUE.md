# HOUYHNHNM ↔ dregg — A Deep Critique

**Date:** 2026-05-25
**Companion to:** `HOUYHNHNM-COMPARISON.md` (diplomatic). This is the
sharp version: what dregg is fooling itself about, where the code
contradicts its own marketing, and the smallest fixes that would let
it stop pretending.
**Stance:** I am holding the houyhnhnm worldview as load-bearing,
not as decoration. If dregg wants to be a *Houyhnhnm-style*
computing-mesh — and large parts of `NEW-WORLD.md` very much want
to claim that lineage — then it has to be evaluated by the
houyhnhnm yardstick, not graded on a curve against Ethereum.

> "When a casual user mistake causes a tool to fail catastrophically,
> fools blame the user; wise men blame the toolsmiths." — Ch.11
>
> When the toolsmith *advertises proof-carrying mesh* but ships a
> 13,905-line executor that *trusts itself* on nine effect variants
> and `MockProofVerifier` semantics for the trustless intent flow,
> the toolsmith is the one being blamed here.

---

## §1 — The Houyhnhnm worldview I am holding dregg to

Before evaluating dregg, I need to be honest about which Ann I'm
channelling. The previous lane summarised her diplomatically.
Here is the un-diplomatic version, taken at full strength.

### 1.1 The system is the interaction, not the artifact

> "Humans have computer systems, Houyhnhnms have computing systems."
> (Ch.1)

The unit of design is *the interaction including the sentient
user*. Asking "is the proof done? is the verifier done? is the
cclerk done?" is the wrong shape of question. The right shape:
"can a user holding only public information about a federation
verify a third party's claim about their cell's state, undo it if
they made a mistake, branch the system to try the change in a
sandbox first, and audit the responsible chain of toolsmiths if the
verifier turns out to be lying?" That sentence is one
interaction. If it's not closed end-to-end, no individual artifact
is done.

### 1.2 Persistence is a system-wide protocol

> "Houyhnhnm computing systems make data persistence the default,
> at every level of abstraction... the change you made will remain
> in the system forever — that is, until Civilization itself
> crumbles, or you decide to delete it (a tricky operation)."
> (Ch.2, Ch.3)

Not "the ledger persists". Not "the receipt chain persists". **All
state at every level of abstraction**, including in-memory
caches, including capability-handle tables, including
program-source. If a fact existed in the system at moment t, you
should be able to ask the system about it at moment t' > t. The
test is: *can the system fully replay any past session by reading
its own log?* If not, it isn't persistent in the Houyhnhnm sense.

### 1.3 Code and data are one history

> "Houyhnhnms think of code and data as coming together... part of
> the same interaction with the Sentient user, with data and code
> being useless without the other, or out of synch with the
> other; and thus Houyhnhnm computing systems casually apply
> version control to the entire state of the system." (Ch.3)

A program-change is a first-class history event of exactly the same
kind as a state-change. "I redeployed cell X with a new program at
height 1234" is a system event with the same standing as "I
transferred 5 to cell Y at height 1234". Both must show up in the
log; both must be replayable; both must be governable.

### 1.4 Type changes ship with typed upgrade functions

> "Houyhnhnm systems, since they remember the history of type
> modifications, require every type modification to be accompanied
> by a well-typed upgrade function, taking an object in the old
> type and returning an object in the new type... The system also
> uses linear logic to ensure that when writing an upgrade
> operator, you must explicitly drop any data that you don't care
> about anymore, so you can't lose information by mistake or
> omission." (Ch.5)

This is the load-bearing test for whether code-and-data-as-one
applies operationally. If the program changes but the old data is
just *abandoned*, the system has cheated. The upgrade must be
*written*, *typed*, and *witnessed by linear discipline*.

### 1.5 No kernel — polycentric, smallest-adequate

> "Houyhnhnm computing systems do not possess a one single Kernel;
> instead they possess as many 'kernels' as there are computing
> subsystems and subsubsystems, each written in as high-level a
> language as makes sense for its purpose; and the set of those
> 'kernels' continually changes as new processes are started,
> modified or stopped." (Ch.6)

The kernel-shaped lump is itself the antipattern. If your system
has one giant invariant-enforcement object that everything funnels
through, you have a Linux/Windows kernel, not a Houyhnhnm
computing system, even if the lump is written in Rust and emits
STARK proofs.

### 1.6 Resources are linear

> "Initial hardware resources... are modeled using linear logic,
> ensuring they have at all times a well-defined owner; and the
> owner is usually some virtual device broker and multiplexer that
> will dynamically and safely link, unlink and relink the device to
> its current users." (Ch.6)

"Linear" here is not decorative. A linear resource has the property
that *the type system makes duplication un-typable*. You cannot
silently mint or burn — the rules of the language refuse to
type-check such a step. Conservation as a runtime check is a
weaker thing; conservation by typing is the Houyhnhnm standard.

### 1.7 No applications, only platform extensions

> "Houyhnhnms don't think in terms of standalone applications;
> they think in terms of platforms that they extend with new
> functionality... In Houyhnhnm computing systems, there are no
> applications and no 'save' buttons." (Ch.7)

An "application" that owns its own state, its own protocol, its
own concept of identity, and only interoperates with the rest of
the platform via byte-shaped APIs — that is a *Human* artifact.
The Houyhnhnm equivalent is a small platform module that exposes
typed methods over typed state and inherits the platform's
persistence, versioning, sandboxing, copy-paste.

### 1.8 Source is canonical; binaries are caches

> "In Houyhnhnm computing systems, the source is the semantic
> state of the system, on which change happens, and from which the
> text is extracted if and when needed." (Ch.3)

The byte stream is a derived artifact. Source is the canonical
form. Treating bytes as the locus of identity (Nock-style) is the
Urbit mistake.

### 1.9 Determinism by construction, not by hope

> "All sources of non-determinism are either eliminated or
> recorded." (Ch.3)

Not "we tested and it was deterministic". *Constructed* so that
non-determinism cannot enter. The persistence log is just the
keystrokes; every byte downstream is reproducible from those
keystrokes plus the program-source. Including by the prover.

### 1.10 Low time-preference: choose tools for their arc

> "In an emergency, you use the best tool at hand, even if the
> best tool at hand is only a piece of cut stone. But if as a
> professional technologist, you find after twenty years of
> practice that your best tool at hand is still cut stone, and
> what more, that you are now a virtuoso at using it — then you
> might not be such a great professional technologist." (Ch.11)

Shipping the "temporary" version into production while telling
yourself you'll fix it later is exactly the High Time-Preference
trap. The right tool is the one that survives the *arc*.

### 1.11 Sub-additive blame

> "We were supposing that blame is distributed amongst
> participants, such that the sum of all shares of the blame add
> up to 100%. Actually, Houyhnhnms well understand that blame is
> subadditive... each participant or set of participants is
> assigned an amount of blame corresponding to the probability
> that a good decision of theirs could have avoided the bad
> outcome; then... the sum of the amounts of blame of the parts
> will be more than the amount of blame of the whole." (Ch.11)

The right question is not "whose fault is it?" but "which
combinations of layers could have caught this, and what would
each layer's degree of culpability be?" When designing a
receipt-and-witness chain, the test is whether *every party who
could have prevented an invariant violation can be identified and
held to a measurable share of culpability*. If two parties can
cooperate to produce an OK-looking receipt and *no one* can be
blamed for the resulting invariant break, the meta-system for
assigning responsibility is itself broken.

### 1.12 The Urbit critique

The most operationally pointed chapter is Ch.10. Its core is:

1. **Fixing a low-level VM forever is not future-proofing**; it is
   future-prohibiting. "If the technology were frozen in time at
   the beginning, as in Urbit, nothing short of retroactive
   agreement using a time machine could improve it."
2. **The "deterministic VM" idea is solving a social problem that
   doesn't exist** unless you have crypto-currency-style mutual
   verification — and Urbit doesn't.
3. **Even when you do have crypto-currency-style mutual
   verification**, the fixed VM is an *impedance mismatch*, not a
   benefit. The real semantics escape into u3 (the C runtime),
   and that's where bugs and lies live.
4. **A fixed VM with escaping semantics is "a sham"**: "at the first
   bug introduced or 'shortcut' taken, the entire Nock VM becomes
   a sham."

This is the test dregg has to pass. `dregg` *does* have
crypto-currency-style mutual verification, so the first defense
doesn't apply. But the third and fourth absolutely do, and we
will see below that dregg flunks them on multiple counts today.

---

## §2 — Lines of attack

Each section below pairs a houyhnhnm citation, a dregg citation
(code or doc), the failure, why it matters, and the smallest fix.
I am not pulling punches; I am citing files.

### 2.1 Code-and-data-as-one-history vs. dregg's binary/source split

**Houyhnhnm (Ch.5):**
> "Houyhnhnm systems, since they remember the history of type
> modifications, require every type modification to be
> accompanied by a well-typed upgrade function, taking an object
> in the old type and returning an object in the new type."

**dregg:** `turn/src/action.rs:524` defines
```rust
SetVerificationKey {
    cell: CellId,
    new_vk: Option<dregg_cell::VerificationKey>,
},
```
The executor handler (`turn/src/executor.rs:7256-7261`) checks
nothing more than the `Action::SetVerificationKey` permission and
swaps a hash. The "old program → new program" transition is
treated identically to "set a flag": you have permission, the
flag is set, end. There is no `migration_fn`, no `old_state →
new_state` mapping required, no per-slot upgrade discipline, no
linear-logic enforcement that old fields are explicitly
dropped-or-renamed-or-preserved. There is not even a *registered
record* of which program the cell used to have.

`NEW-WORLD.md` describes `FactoryDescriptor` as the canonical
creation path, but factories only handle the *birth* of a cell.
The on-going life of a cell whose program has changed is left
unspecified. `HOUYHNHNM-COMPARISON.md §4.4` softens this into "the
Houyhnhnm framing presses on this" — that is too gentle. There is
no upgrade story at all.

**Why it matters:**
The whole shape of dregg — "proof-carrying capability mesh,
WitnessedReceipt chain as the persistence stream" — collapses
silently if the *program* underneath a state can change without
the change itself being a first-class, typed, replayable event.
Tomorrow's verifier replays a turn that fired against `vk_v1` and
sees today's `vk_v2` and the algebra-of-receipts says nothing
about what happened in between. The cell's history has a cliff in
it that the system doesn't see.

This is also dregg's worst Urbit-trap: an attacker who controls
the `SetVerificationKey` capability can re-author the rules of a
cell out from under outstanding capabilities granted against the
old rules. The bearer of an old cap still has an attenuated cap
to a state that obeys *different rules* now — and the cap's VK
doesn't bind the rules it was granted against.

**Smallest fix (3–5 days):**
Add to `cell/src/program.rs` a `ProgramTransition { from_vk:
[u8;32], to_vk: [u8;32], upgrade_witness: WitnessedPredicate,
state_diff_kind: StateDiffKind }` enum. Make `SetVerificationKey`
*require* one of these to be supplied (or `StateDiffKind::Reset {
explicit_drops: Vec<u8> }` for the no-migration case, which
forces the operator to enumerate every slot they are abandoning
— linear-logic-style). Hash the `ProgramTransition` into
`Turn::hash` so receipts cover it. Receipts then record program
lineage; verifiers can refuse to chain across program-transitions
they don't understand.

**Reality check:** This is a *small structural fix* that ports a
critical Houyhnhnm tenet — typed schema upgrade — onto dregg's
existing receipt chain. It costs almost nothing and closes a
class of "old cap exercised after silent program swap" attacks
that the current threat ledger does not enumerate.

---

### 2.2 Persistence as system-wide protocol vs. dregg's "ledger is the log"

**Houyhnhnm (Ch.2):**
> "Houyhnhnm computing systems make data persistence the default,
> at every level of abstraction."

**Ch.4:**
> "Houyhnhnms do not have any library to manage persistence;
> instead, Houyhnhnms have a number of libraries to manage
> transience."

**dregg:** the system that *is* persistent is the
ledger + WitnessedReceipt chain + blocklace DAG. The system that
is *not* persistent includes:

- **CapTP session state.** `wire/` runs sessions in memory. A
  dregg node that crashes mid-session loses all sturdy-ref
  resolutions in flight, all promise-pipelining state, all
  half-completed three-party handoffs.
- **Capability handle tables** inside live processes. The c-list
  on a cell is part of state, fine — but the *handles* held by
  client code in dregg-sdk are not in any log; if a client
  process dies, what it knew about cap-graph reachability is
  gone.
- **Pending intent state.** The trustless intent engine in
  `intent/src/trustless.rs` holds in-flight ciphertexts and
  threshold-decryption shares in memory until t-of-n. A node
  restart loses partially-collected share sets; submitted
  ciphertexts that haven't yet been decrypted are not stably
  persisted at any level of the houyhnhnm-sense persistence
  abstraction.
- **The blocklace mempool.** Gossiped-but-not-yet-included
  events live in volatile gossip layer state. `intent/` has a
  `gossip_filter` — that filter's state is RAM.
- **Studio (the IDE).** Browser session state. WASM heap. A
  browser refresh loses your in-flight editing session because
  the persistence story does not extend through the toolchain.

This is exactly fractal transience as Ch.2 names it: "this
fundamental design difference between Human and Houyhnhnm
computing systems is observable at every level of these systems."
`dregg` has *gotten one layer right* — the on-chain ledger /
receipt chain — and inherited transience everywhere else.

**Why it matters:**
The marketing claim is that WitnessedReceipt is "the persistence
stream" (§2 of `HOUYHNHNM-COMPARISON.md`). But under the
houyhnhnm yardstick, persistence has to extend up *and out* — to
the IDE, to the cclerk handle, to the in-flight intent. If the
persistence story bottoms out at "the chain remembers", then
dregg is *exactly* a fancy database server with crypto — the
shape Ch.2 was savaging.

**Smallest fix (~1 week per layer; pick one):**
Pick a single non-ledger layer and *commit* it to the
WitnessedReceipt persistence stream. The pragmatic candidate is
the **trustless intent engine**: every ciphertext submission,
every decryption-share contribution, and every state transition
of the share-collection state-machine becomes a recorded event,
written into a per-federation event journal (or into the
blocklace itself as a "gossip-meta" event class). Then publish
the *protocol* — say "dregg's persistence stream now covers
intents" — and treat the others as follow-on lanes (CapTP next,
Studio last). Until that's done, do not say "WitnessedReceipt is
*the* persistence layer". Say "WitnessedReceipt is *a*
persistence layer", which is exactly what `HOUYHNHNM-COMPARISON.md
§9.1` raised as a "big open question". The honest writing already
exists in the comparison doc; promote it to the design narrative.

---

### 2.3 Linear logic on resources vs. balance-as-field

**Houyhnhnm (Ch.6):**
> "[Resources] are modeled using linear logic, ensuring they have
> at all times a well-defined owner."

**Ch.5:**
> "The system also uses linear logic to ensure that when writing
> an upgrade operator, you must explicitly drop any data that you
> don't care about anymore."

**dregg:** balance is a `u64` field on `CellState`
(`cell/src/state.rs`). Effects can move it (`Transfer`), create
it (`CreateCell { balance }`, `BridgeMint`), or destroy it
(burns implicit in `BridgeLock`). Conservation is enforced by a
*runtime* sweep (`turn/src/executor.rs:4137`
`compute_balance_delta_from_effects` and
`turn/src/executor.rs:4763` `check_note_conservation`). The AIR
*binds* this delta into the proof
(`turn/src/executor.rs:12503-12516`), but that binding is
**partial**:

- `BridgeMint`, `BridgeLock`, `CreateEscrow` use **30-bit
  truncation** of the value when projecting it into the AIR
  (`CAVEAT-LAYER-COVERAGE.md` lines 245+). The cleartext-side
  conservation sweep is correct *for that runtime*. But the
  algebra in the AIR is *not* — a value above 2^30 only has its
  low 30 bits committed. *The proof does not enforce
  conservation algebraically for those variants*. It enforces
  conservation modulo 2^30. The CAVEAT-LAYER-COVERAGE.md doc
  admits this in plain text: "Above 2^30 a malicious prover
  could re-mint with arbitrary high bits."
- **Note conservation under Pedersen commitments** (the
  `check_committed_conservation` path) is a real algebraic
  check, *if* a range proof is attached. The range proof is
  optional in the effect schema (`NoteCreate.range_proof:
  Option<Vec<u8>>`); the executor enforces presence at runtime
  but the *type* permits absence. A Houyhnhnm would say the
  type system *itself* must refuse the construction of a
  `NoteCreate` with a commitment but no range proof.

Worse: `Effect` is a Rust `enum` whose variants include both
**resource-conserving** moves (`Transfer`, `NoteSpend`,
`NoteCreate` pair), **resource-creating** moves (`CreateCell {
balance }`, `BridgeMint`), and **non-resource** moves
(`SetField`, `EmitEvent`). There is no marker in the type system
distinguishing them. The runtime sweep is the *only* place
conservation is checked. The AIR projects a balance-delta into PI
but, on the truncated variants, lies about it on the high bits.

**Why it matters:**
Linear logic exists precisely so that you can prove "no resource
was duplicated by mistake or omission" *by examining the type*,
not by running the program and seeing whether the runtime sweep
fires. `dregg`'s resource discipline is the *opposite shape*: a
flat enum where every variant has free access to balance fields,
plus a centralized executor sweep that you'd better hope is
complete, plus an AIR that algebraically endorses a truncated
view.

This is also where dregg most directly cheats vs. its
EXECUTOR-HONESTY-AUDIT marketing. T12 in that audit ("Lie about
balance deltas") is marked "closed" because
`compute_balance_delta_from_effects` derives the delta from the
effect list and binds it into the AIR. *But the AIR binds the
truncated value.* So T12 is *not* algebraically closed; it is
closed modulo 2^30, and the threat ledger does not say that.

**Smallest fix (2–3 days for marker; 2–3 weeks for full range
proof):**
1. **Today**: add a `LinearityClass` discriminant on `Effect`
   (`Conserved`, `Bounded`, `Monotonic`, `Free`) and write a
   compile-time test that for every `Conserved` variant, the
   AIR projection covers the full value. Fail the build for any
   variant whose AIR projection is narrower than the field. This
   is `HOUYHNHNM-COMPARISON.md §8.2`'s suggestion, with teeth.
2. **In the medium term**: convert `Option<range_proof>` to a
   type-state where `NoteCreate { committed: CommittedValue<RP>
   }` *cannot be constructed* without the range proof. This is
   the linear-logic move: make the violation un-typable.
3. **Eventually**: replace the 30-bit truncation in
   `BridgeMint/Lock/CreateEscrow` with proper 4-limb (or
   16-bit-per-limb) decomposition under range-check lookup
   arguments. The TODOs are already in
   `circuit/src/effect_vm.rs:2305` and:2326. Until done, *the
   AIR-honesty audit cannot say T12 is closed*.

---

### 2.4 Polycentric kernels vs. the 13,905-line executor

**Houyhnhnm (Ch.6):**
> "Houyhnhnm computing systems do not possess a one single Kernel;
> instead they possess as many 'kernels' as there are computing
> subsystems and subsubsystems, each written in as high-level a
> language as makes sense for its purpose."

**dregg:** `wc -l turn/src/executor.rs` → **13,905 lines**. This
single file contains:

- `TurnExecutor` struct and its associated `impl`
- The classical (executor-trusted) call-forest walker
- The trustless proof-verification branch
- `verify_authorization` (~line 5848)
- The effect-dispatch megamatch in `apply_effect`
  (~line 7380, ~600 lines of `match effect { ... }`)
- Permission deduplication (`required_permissions_for_effects`)
- Note conservation (3 separate functions)
- Cross-cell-conservation in `MixedAtomicTurn`
- Cell-migration manager
- Fast-path eligibility logic
- Sovereign-witness verification orchestration
- Eventual-ref resolution
- Aggregate-bilateral-prover orchestration
- 12+ `match effect { ... }` dispatches at separate lines (3290,
  4140, 7226, 7389, 10534, 10760, 10812, 10891, 10954, 11403,
  11543, 11594, 11883) — *the same enum is re-walked 12 times*
  for different concerns.

`turn/src/lib.rs` itself re-exports 50+ types from 25 sub-modules,
all rooted in this one struct. This is *the kernel*. It is the
single piece of software through which every effect, every
authorization decision, every conservation check, every receipt
emission flows. It is precisely the artifact Ch.6 was savaging:
"every program must either reimplement its own access control
from scratch or become a big security liability whenever it's
exposed to a hostile environment".

`dregg`'s pseudo-polycentrism — multiple "cells" each with
"programs" — is a polycentrism *of state*, not of *enforcement*.
The state lives in many cells; the enforcement lives in one
executor. The same monolith is the only thing that knows how to
walk any effect. A new effect variant requires editing 12 match
statements in one file. A change to authorization touches the
same file. A change to receipt shape touches the same file. A
change to conservation rules touches the same file.

`HOUYHNHNM-COMPARISON.md §3.3` claims dregg achieves
polycentrism: "the executor is a participant, not a kernel; the
cell-programs constrain what may happen; the federation
constrains which history is canonical." This is *partly* true
about run-time enforcement — programs do gate transitions. But
the *implementation* of every program-evaluation, every effect,
every receipt, runs through one Rust crate's one struct. The
runtime model can be polycentric; the codebase is not.

**Why it matters:**
1. **Auditability:** in Ch.6, the entire point of polycentric
   kernels was "the surface of attack for technical defects" is
   minimized "by making such attacks impossible without a
   meta-level intervention". With one giant executor, the
   surface of attack is *the entire executor*. A logic error
   anywhere in 13,905 lines is potentially a
   dregg-mesh-wide soundness break. This was the whole point of
   the Urbit critique: not Nock-the-language-is-bad, but
   Nock-the-formalism-cannot-protect-against-u3's-bugs. `dregg`'s
   AIR-the-formalism cannot protect against the executor's
   bugs. The audit-ledger documents this implicitly by listing
   T1–T15 mostly in terms of *the executor* doing-or-not-doing
   things.
2. **Maintainability:** the dev-philosophy memory note says
   "no quick fixes". Fine — but a 13,905-line file *forces*
   quick fixes because the cognitive load of a structural
   refactor is too high to schedule. The size *itself* is the
   high-time-preference tax.
3. **Composability:** the houyhnhnm vision of "small modules that
   each do one thing well, combined inside a common platform"
   (Ch.7) is exactly negated by the executor. A new turn-shape
   (`AtomicSovereignTurn`, `MixedAtomicTurn`, `ConditionalTurn`,
   `EncryptedTurn`, `ComposedTurn`...) is added by *bolting a
   new method onto the executor*. The proliferation is visible in
   the re-export list at `turn/src/lib.rs:120-170`.

**Smallest fix (~2 weeks of refactor, breaks zero behavior):**
Split `TurnExecutor` along the only real seam dregg has:
*per-effect-family handlers*. The structural move:

- `turn/src/effects/transfer.rs` — owns `Transfer`, `Bridge*`,
  `Note*` (the resource-conserving family)
- `turn/src/effects/capability.rs` — owns `Grant`, `Revoke`,
  `Introduce`, the `Seal*` ops
- `turn/src/effects/state.rs` — owns `SetField`,
  `SetPermissions`, `SetVerificationKey`, `IncrementNonce`
- `turn/src/effects/escrow.rs`, `.../obligation.rs`, `.../queue.rs`
- `TurnExecutor` becomes a *dispatcher*: walks the call-forest,
  delegates each effect to its family handler, collects journal
  entries.

The 12 match-on-effect blocks collapse to one trait method per
family. Conservation, authorization, AIR-projection move *into
each family's module*. The executor itself drops to ~1500 lines
and becomes auditable. This is the houyhnhnm "polycentric
kernel" applied where dregg hasn't.

**Reality-check on the cost:** this is not a soundness change;
it is purely a re-arrangement of code. The four executor-trusted
threats currently parked in T9 / T12-truncation / bridge
proof-to-action / coord BudgetCoordinator (`NEW-WORLD.md` §"What's
not done" items 1–5) become *strictly easier* to close because
each lives in a 200-line module instead of being entangled with
12,000 lines of other code.

---

### 2.5 The "no applications, only platform extensions" tenet vs. starbridge-apps

**Houyhnhnm (Ch.7):**
> "Houyhnhnms don't think in terms of standalone applications;
> they think in terms of platforms that they extend with new
> functionality... In Houyhnhnm computing systems, there are no
> applications and no 'save' buttons."

**dregg:** there's a directory called `starbridge-apps/` with a
plan called `STARBRIDGE-APPS-PLAN.md`. The slop-list (`amm`,
`lending`, `orderbook`, `stablecoin`, `dao-treasury`,
`prediction-market`) was deleted — good. The replacements
(`nameservice`, `identity`, `subscription`, `governed-namespace`,
`bounty-board`, `gallery`, `privacy-voting`, `compute-exchange`)
remain *apps*, by name. `NEW-WORLD.md` says "**No new Effect
variants**", which is a *partial* houyhnhnm move — the apps must
compose what the platform offers. Good.

But: each starbridge-app is still its own Rust crate, with its
own `FactoryDescriptor[]` array, its own turn builders, its own
`pages/` directory with its own web components. They do not
share a *platform-level* presentation of "send a message to a
cell", "subscribe to events from a cell", "render a slot",
"present a credential". Each app reinvents those.

This is the houyhnhnm critique in Ch.7 applied: "In Human computer
systems, programmers have to bundle a finite number of such
components into the package-deal that is an 'application', where
you can't use the component you want without being stuck with
those you don't want."

A user with a nameservice cell who wants to use the *identity
app's* credential-presentation widget on her nameservice slot
data: can she? Without copying-pasting code? The current shape
is "no — those are different apps". The houyhnhnm shape would be
"yes — both are platform extensions exposing typed methods over
typed state; the platform's renderer composes them".

`dregg`'s `dregg-credentials` and `dregg-directory` micro-crates
(promoted from app code, per `NEW-WORLD.md`'s inventory) are
exactly the right direction — promote functionality from
apps-as-silos to platform-extensions. But the *naming* and the
*architectural intent* are still "apps". The plan calls them
apps. The directory is `starbridge-apps`. The Cargo crates are
named `starbridge-apps/<name>`.

**Why it matters:**
This is mostly a *cultural* failure, not a structural one.
`dregg` has the substrate (factories, FactoryDescriptors, the cap
system, the inspector registry hinted at in StarbridgeAppContext)
to be a Houyhnhnm-style platform. But it's been organised under
the wrong noun. The naming will shape the architecture: a
contributor who reads "starbridge-apps/" understands their job
as "build an app". A contributor who reads "starbridge-extensions/"
or "platform-modules/" understands their job as "add a typed
method to the platform's vocabulary".

The slop-list deletion was Houyhnhnmoid; the rename of the
remaining directory would be too.

**Smallest fix (1 hour):**
Rename `starbridge-apps/` → `starbridge-modules/` (or
`platform-extensions/`). Update `STARBRIDGE-APPS-PLAN.md` to
articulate the houyhnhnm framing: "each module declares its
typed extensions to the dregg vocabulary; the platform composes
them; there is no app-shaped silo". Promote the *next two*
reusable surfaces (presentation/inspector? credential-render?)
to micro-crates in `dregg-<thing>/` so the migration pattern
becomes visible. This is a *naming-led architecture change* that
moves a culture, not just a directory.

---

### 2.6 Determinism by construction vs. prover-side non-determinism

**Houyhnhnm (Ch.3):**
> "All sources of non-determinism are either eliminated or
> recorded."

**dregg:** the system claims determinism for the *verifier* —
given the same `(turn, proof, PI)`, the verifier returns the
same accept/reject. That part is real. What's *not* claimed
anywhere clearly: determinism for the *prover*.

Probable non-determinism sources in dregg's prover today,
based on a survey of `circuit/`:

- **FRI commitment blinding** in the STARK backend. The Fiat-Shamir
  transform is deterministic *given a transcript seed*, but the
  generation of blinding factors and the choice of polynomial
  basis representation are typically nonce-randomized in
  optimized provers.
- **Recursion-layer randomness.** Plonky3 recursion (the path
  named in `NEW-WORLD.md` §"Aggregation / Golden Vision") uses
  random folding challenges. Those *should* be Fiat-Shamired,
  but I have not personally audited that every random byte in
  the prover flows from a deterministic transcript.
- **Pedersen commitment blinding factors** in `value_commitment`.
  The blinding `r` *must* be random for hiding. If the random
  source is not recorded somewhere replayable, then *a single
  `NoteCreate` turn cannot be re-proven by anyone else from the
  same witness*.

The houyhnhnm test is: "can a Houyhnhnm re-execute this turn
from its inputs and arrive at exactly the same proof bytes?" If
the answer is no, then the persistence stream is not actually
complete — there are bytes (the random blindings) that exist in
the prover's RAM at moment t but are *not* in any log. Ch.3 is
crisp: "this however, requires that all sources of
non-determinism are either eliminated or recorded — which
Houyhnhnm computing systems do by construction." `dregg`'s claim
to be a verifiable mesh requires the same.

Note this isn't actually a soundness bug for *verification* — the
verifier doesn't care about prover determinism. But it is a
soundness bug for *re-execution-as-audit*, which is the
WitnessedReceipt scope-2 claim. If two honest re-proofs of the
same witness produce different proofs, then "I re-proved this
and got the same answer" is not a *cryptographic* fact, only a
"the verifier accepted both, but they had different bytes" fact.
You cannot deduplicate proofs across re-provers; you cannot say
"this exact byte string is the canonical proof of this turn";
you have created an implicit prover-identity dimension that
participates in identity but is unmodelled.

**Why it matters:**
This shows up the moment anyone wants to:
- Cache proofs across federations ("did anyone else already
  prove this turn? I'll just reuse their proof bytes" — no, you
  can't, because *your* re-prover produces different bytes)
- Build a CRDT-shaped re-proof economy where multiple provers
  can independently re-prove a turn and agree on a canonical
  proof for storage
- Use the proof *itself* as a primary key (it can't be — proofs
  are not canonical functions of witness)
- Apply the houyhnhnm "monitor" pattern (Ch.3): re-execute from
  the persistence log and *expect bit-for-bit identity*

`dregg`'s documents about the prover are silent on this. The
audit ledger is silent. The verifier docs cover their side
correctly but the prover is treated as a black box. The opacity
*itself* is the violation.

**Smallest fix (2–3 days for audit; ongoing for hardening):**
Write a one-page `PROVER-DETERMINISM-AUDIT.md`. Enumerate every
RNG-consuming call site in `circuit/` and `turn/`. For each,
declare whether the randomness derives from a Fiat-Shamir
transcript seeded by the turn hash (Houyhnhnm-acceptable) or is
nondeterministic (a violation to be fixed). Where the
Pedersen-blinding `r` comes from the prover's secret seed, *put
the seed (under encryption to the prover's own future self) in
the WitnessBundle*. The houyhnhnm rule: "all sources of
non-determinism are either *eliminated* or *recorded*". `dregg`
needs to enforce that as a property, with a CI test.

---

### 2.7 Sub-additive blame vs. the threat ledger

**Houyhnhnm (Ch.11):**
> "Blame is subadditive... each participant or set of participants
> is assigned an amount of blame corresponding to the probability
> that a good decision of theirs could have avoided the bad
> outcome."

**dregg:** `EXECUTOR-HONESTY-AUDIT.md` enumerates T1–T15 and
maps each to a defense layer. Look at T9 (skip sovereign-witness
verification):

> (D) AIR: sovereign witness columns exist; the AIR enforces
> the witness verifies before the effect transition takes hold.
> (G) **Open.** Verify sovereign witnesses *algebraically
> constrain* the transition (not just decorate the receipt).

The ledger is structured as "this threat, this defense, gap?". A
single layer is named per threat. There is **no column for
"layer 2 catches it if layer 1 misses"**. The ledger does not
support sub-additive reasoning. When a real incident happens —
say, T9 fires because the sovereign-witness AIR path doesn't
algebraically constrain — the post-mortem will fall straight
into the blame-game trap Ch.11 was warning against.

Two parties can cooperate today to produce a receipt that *looks*
OK and breaks an invariant *with no one being blamable*:

1. **Scenario:** Alice (sovereign-cell holder) and Bob
   (federation executor) collude. Alice supplies a sovereign
   witness whose internal STARK doesn't actually validate the
   state transition. Bob's executor — knowing the AIR doesn't
   algebraically *teeth* the witness — accepts it. The receipt
   chain shows: Alice signed the turn, Bob's federation attested.
   *Both signatures are real.* The verifier verifies them. The
   receipt verifies.
2. **Who's blamable?** Alice did not forge a signature. Bob did
   not forge a signature. Neither did anything algebraically
   inconsistent. They just *cooperated* to push through a state
   transition that no one was *required* to check.

Ch.11's framing of this: "in a joint decision between the two of
us, where either of our strong objection could have had a 80%
chance of averting the bad outcome, then we are each 80% [to
blame] for the outcome, though our joint blame is only 100%."
The dregg threat ledger has no apparatus for representing this.
Sub-additive blame requires *recording who could have caught
it*. The current ledger records *who did catch it*.

**Why it matters:**
1. **Operational:** when (not if) an incident happens, the
   post-mortem will be a single-cause finger-pointing exercise.
   This is the precise failure Ch.11 was diagnosing in human
   computing.
2. **Architectural:** sub-additive blame is also a *design
   principle* — when designing a receipt or a witness, the
   question "if this layer is malicious, which other layer
   *could* catch it?" is the right design question. The current
   ledger structure does not encourage asking it.
3. **Adversarial-tolerance theory:** BFT consensus assumes
   *some* parties are malicious. The receipt system should be
   robust under arbitrary subsets of layers being malicious.
   Sub-additive blame is the language for reasoning about that.

**Smallest fix (2 days):**
Augment `EXECUTOR-HONESTY-AUDIT.md` with two new columns per
threat: `(could-catch)` — a list of all layers that *should* be
able to catch the threat, and `(does-catch)` — a list of layers
that *do* catch it today. Reformulate the audit's central
question from "is each threat closed?" to "for each threat, what
is the minimum coalition of malicious actors required to make it
fire?". This is `HOUYHNHNM-COMPARISON.md §8.4` upgraded with
teeth: not just "caught at" but "could-have-caught".

Then, as a follow-on: ban coalitions of size 1 from succeeding
on any threat. Every threat must require at least 2 colluding
layers to break the invariant. That gives dregg an *algebraic
property* of its blame distribution — every invariant has at
least two independent defenders — which is the natural
sub-additive structural rule.

---

### 2.8 Source as canonical vs. VK as canonical

**Houyhnhnm (Ch.3):**
> "The source is the semantic state of the system, on which
> change happens, and from which the text is extracted if and when
> needed; this is in sharp contrast with typical Human computer
> systems, where the source... is text files that are compiled,
> disconnected from the state of the system."

**dregg:** `VK-AS-RE-EXECUTION-RECIPE.md` (a real doc in the
repo) frames the verification key as "what you need to re-execute
this turn". Combined with the encoder (the function that turns a
program into its AIR shape), the VK + encoder + program-source
*is* the canonical re-execution recipe. This is genuinely
Houyhnhnmoid.

But: in operational practice, *the VK is the identity*. Cells
commit to `vk_hash` (`Effect::SetVerificationKey { new_vk:
Option<VerificationKey> }`); factories commit to `program_vk` in
`FactoryDescriptor`; the registry of `WitnessedPredicateKind`
maps `vk_hash → verifier`. The *source* — the high-level program
description from which the AIR was compiled — is *not* in the
runtime story. There is no canonical mapping from `vk_hash` back
to "here is the source program that produced this VK". The
programmer's mental model is "the VK is the program".

The houyhnhnm form would be: every VK is a *cache* of its
source. The runtime stores source; whenever it needs the VK, it
re-derives it from source. If two re-derivations disagree, that's
a CI failure of the encoder. If a contract has a VK with no
known source, that contract cannot participate in a federation
that requires *understandability*.

This is also the Urbit-test most squarely applied: Ch.10's
"Nock-is-a-sham" argument was *exactly* that Nock VM identity
hashes don't bind the high-level semantics anyone actually
writes. `dregg`'s `vk_hash` is in danger of becoming the same:
identity that doesn't bind source.

**Why it matters:**
- **Source recoverability after vendor death.** A contract
  authored by a vendor that subsequently disappears: dregg
  remembers the `vk_hash`, the federation enforces it, but no
  one alive can re-derive what the program *did*. The contract
  becomes a sham: a hash that everyone enforces but nobody
  understands.
- **Verification-key churn.** Encoder bug-fixes change VKs even
  for *the same program*. If `vk_hash` is identity, then a
  bug-fix in the encoder spuriously breaks existing
  capabilities. If source is identity and VK is cache, the
  encoder can be re-run.
- **`dregg`'s own multi-backend differential testing** is
  *exactly* the encoder-as-cache pattern at the DSL layer
  (`dregg-dsl-differential`). The infrastructure exists for the
  *predicate* sub-language. Promoting that pattern to the
  whole cell-program layer would close this gap.

**Smallest fix (1–2 weeks; really a registry change):**
Add a `dregg-program-registry` crate: a content-addressed store
of source programs, where each program is keyed by *source-hash*
and stores `{source, encoder_version, derived_vk_hash}`.
`FactoryDescriptor` and `Effect::SetVerificationKey` carry the
*source-hash*, not the *vk-hash*. Verifiers derive the vk-hash
on demand. Adopt the same pattern `dregg-dsl-differential`
already uses for the predicate sublanguage. The pattern then
generalizes to the cell-program layer. The Urbit-trap closes:
identity *is* source; vk-hash is a derived view; encoder bugs
fix without invalidating cells.

---

### 2.9 Low time-preference vs. Silver-vs-Golden language

**Houyhnhnm (Ch.11):**
> "Today, however, you must make strategic decisions, that will
> affect the chain of future choices... you will use the best
> information you have here and now, that can help you in all
> this future that you don't know..."

> "Most humans tend to have High Time-Preference, even in the
> long-run choice of evolving technologies, whereas Houyhnhnms
> tend to adopt the principles of Low Time-Preference, and
> embrace the fact that technologies especially will evolve over
> the long run."

**dregg:** `NEW-WORLD.md` opens by *naming* this distinction:

> **Silver Vision** is the *pre-algebraic* form — every component
> integrates, every loop closes, every receipt is signed and
> replayable. **Trust-based by construction (executors are
> presumed honest)**, but the *substrate* required for the next
> step is in place. This is what we're building.

> **Golden Vision** is the *folded mesh* form — recursive
> aggregation collapses the entire DAG of cells' interactions
> into one STARK statement...

This is the credit-card-debt confession in plain English. The
*marketing claim* (everywhere from the tagline "proof-carrying
capability mesh" through the docs) is the Golden Vision: a
trustlessly-verifiable algebraic system. The *thing actually
shipping* is the Silver Vision: a trust-based system with a
proof veneer. The promise is that Silver enables Golden later.

Houyhnhnm's Ch.11 read of this would be: **how long has Silver
been "what's shipping"? How quickly is Golden actually
landing? If Silver becomes the steady state, you have shipped
the temporary version into production.**

Audit of "Silver" and "trust" and "executor-presumed-honest" in
the codebase reveals where the temporary tier is actually load-
bearing:

- `EXECUTOR-HONESTY-AUDIT.md` enumerates **three boundary cuts
  not yet algebraically enforced**: T9 sovereign-witness at AIR
  level, bridge proof-to-action binding, coord BudgetCoordinator
  signature gaps.
- `NEW-WORLD.md` §"What's not done" lists:
  - **9 placeholder Effect VM PI variants** (`QueueAtomicTx`,
    `ValidateHandoff`, `QueueDequeue`, `EnlivenRef`, 5 others)
  - **30-bit value truncations** in BridgeMint/Lock/CreateEscrow
  - **Most StateConstraint variants are executor-side only**
  - **Sovereign-witness AIR teeth — Phase 1 not yet implemented**
  - **Real STARK ProofVerifier for intent fulfillment — still
    MockProofVerifier** (see `intent/src/trustless.rs:682`)
  - **coord::BudgetCoordinator signature verification — two real
    security bugs** (one test literally has the comment "Forged
    signature not verified in rebalance yet")
- `CAVEAT-LAYER-COVERAGE.md` enumerates **placeholder context
  fields** that make multiple `StateConstraint` variants
  always-pass (`sender_epoch_count: 0` hard-coded for
  `RateLimit`; `revealed_preimage: None` always for
  `PreimageGate` so the variant *always errors*; `Witnessed`
  cell programs literally "uncreatable in practice").
- `circuit/src/effect_vm.rs:2305`, :2326 — `TODO(range-checks)`,
  `TODO(underflow)` comments left in the AIR for range proofs
  on balance arithmetic. The AIR is missing range checks today.

These aren't "items that didn't make it into Silver"; these are
*items the system actively lies about*. The `PreimageGate`
constraint *cannot succeed* under the executor's hard-coded
`revealed_preimage: None`, so the variant exists in the type
system as a pure trap: any cell-program that uses it cannot make
a turn. That is *worse than missing*; it is *misleadingly
present*.

**Why it matters:**
The houyhnhnm test of low-time-preference is: "the temporary
version stops shipping the moment the permanent version is
viable." `dregg` has been shipping Silver for some unknown number
of "seasons" (the NEW-WORLD.md uses the word "season" 8+
times). The Golden Vision substrate landed (Plonky3 recursion
Block 1) but the *application* of it to close the executor-
trusted boundary is still pending. Meanwhile the marketing
keeps saying "proof-carrying mesh".

Three operational consequences:

1. **External readers cannot tell which Silver-isms are
   "scheduled to be removed by quarter N" and which are
   "permanent compromises that will never become Golden".** The
   distinction is *meaningful*: a 30-bit value truncation in a
   STARK can be fixed; "executor honest" as the trust foundation
   for bridge proof-to-action binding may not be fixable
   without rebuilding the bridge.
2. **The credit-card-debt accumulates silently.** Each new
   `TODO[block1-bind]` placed in `executor.rs:3373` (literally
   `queue_len: 0, // TODO[block1-bind]`) is another rectangle
   of "we'll do this later" carried in the AIR that nobody
   audits the total of.
3. **When an external auditor or user reads "proof-carrying
   capability mesh", they reasonably take this as a *claim*.**
   Under the houyhnhnm framing — toolsmith-blame is real and
   load-bearing — dregg's authors are *currently* on the hook
   for any incident where a reader trusted that tagline.

**Smallest fix (1 day for the audit; ongoing for the discipline):**
Add a **`SILVER-DEBT.md`** at top level. One row per Silver-tier
compromise, with columns: `(what)`, `(where: file:line)`,
`(why-Silver: shape-question vs. effort vs. dependency)`,
`(planned-Golden-resolution)`, `(can-resolve?: yes/blocked-by-X/never)`.
Make this a **CI-checked artifact**: a new `TODO[block1-bind]`
in the codebase that isn't enumerated in `SILVER-DEBT.md` fails
the build. Make the `NEW-WORLD.md` tagline *aware* of this
debt: instead of "proof-carrying capability mesh", say "a mesh
in motion towards proof-carrying; current trust assumptions in
`SILVER-DEBT.md`". The tagline becomes precise and the toolsmith
exits the blame-trap.

This is exactly the houyhnhnm move: "deletion (as opposed to
mere de-indexing), while possible, gets more expensive as the
data you want to delete gets older" (Ch.2). The *Silver-debt
entries* are data; they should be cheap to add and explicit to
discharge.

---

### 2.10 The Urbit-trap, revisited: does dregg actually escape it?

**Houyhnhnm (Ch.10):**
> "Where Urbit distinguishes itself from other VM-based systems...
> is that the semantics of its virtual machine Nock is forever
> fixed, totally defined, deterministic, and therefore
> future-proof."
>
> "Once you have this platform, you don't need any of the Urbit
> operating system, because you already have a Houyhnhnm computing
> system."
>
> "Unless great care is taken... so that the semantics of the
> Nock code generated indeed implements the actual computations,
> while indeed being implemented by the underlying system, then
> at the first bug introduced or 'shortcut' taken, the entire
> Nock VM becomes a sham."

**dregg:** `HOUYHNHNM-COMPARISON.md §4.15` does the comparison
honestly: dregg's Effect VM AIR is "a particular fixed semantic
encoding" similar in shape to Nock-as-frozen-VM. The mitigation
claimed is *VK versioning + the executor honesty audit*.

Now let's actually test that mitigation under load.

**Test 1: Is VK versioning operationally used?**
Search for VK rotation in code: `grep -rn "vk_version\|vk_v2\|vk_rotation"
cell/ turn/ circuit/`. Result: `vk_v2` exists as a struct
(`cell/src/vk_v2.rs`), but the *only* hosted-cell-program path
is via `Effect::SetVerificationKey { new_vk: Option<...> }`,
which (as §2.1 above documented) has no upgrade-function
discipline. There is *no enumerated lineage* in the runtime.
There is no "this cell has been on the following VKs in
sequence". There is no replay test that verifies a cell still
behaves correctly under a sequence of historical VKs.

**Test 2: When the AIR changes, do existing VKs auto-invalidate?**
Search for VK invalidation: `grep -rn "invalidate.*vk\|deprecat.*vk"
*.rs *.md`. Result: zero matches. There is no protocol-level
notion of an old VK becoming stale. There is no "this VK was
generated against AIR version 1.4.2; the current AIR is 1.5.0;
do not accept new proofs against it" mechanism. The AIR shape
in `circuit/src/effect_vm.rs` is the ground truth, *of one
version*. If the AIR changes, the old VKs are silently
incompatible. The system has no protocol for handling this.

**Test 3: Is the encoder honest?**
The encoder is the function that, given a program, produces the
VK. For dregg's `CellProgram`, this is somewhere in the
`circuit/src/dsl/circuit.rs` layer. `dregg-dsl-differential`
tests *predicates* across encoders. There is *no equivalent test
for the cell-program encoder*. A bug in the encoder — say, a
mis-translation of `Cases([...])` semantics into AIR — would
silently produce a VK that *does* satisfy the AIR but *does
not* implement the source semantics. That is the precise
Urbit-VM-as-sham failure mode.

**Test 4: Is the executor honest?**
The audit *describes itself as* the answer to this. T1–T15
enumerate threats. **Three boundary cuts remain explicitly
executor-trusted today.** And the audit is *only T1–T15*; there
is no enumeration of "threats we didn't think of". The
exhaustiveness claim is by hand. (See `EXECUTOR-HONESTY-AUDIT.md`
explicitly: it says T1–T15, not T1–T∞.)

Verdict on the Urbit-trap: **dregg is walking into it slower
than Urbit, but it is on the same path.** The mitigations
(VK-versioning, honesty audit) *exist as documents and partial
infrastructure*. They are **not enforced in code** and they do
**not bound the trust footprint** the way they would need to to
actually close the Urbit-trap.

The houyhnhnm critique applies almost verbatim: "the apparent
simplicity of Nock only hides the ridiculous complexity of the
layers below (u3) or above (Arvo, Ames)." Replace "Nock" with
"Effect VM AIR", "u3" with "the 13,905-line executor", "Arvo"
with "the federation+blocklace layer". The mapping is direct.

**Why it matters:**
This is the *deepest* failure-mode dregg is exposed to. Every
specific threat above (placeholder PI variants, 30-bit
truncations, executor trust on T9/T12/bridge) is an *instance*
of the Urbit-trap: a fixed formalism that doesn't actually
constrain the semantics it claims to constrain. Each one
individually looks like "we'll fix it in the next sprint". But
the *pattern* — "the semantics escapes the formalism into the
executor" — is the structural problem.

The houyhnhnm test for genuinely escaping the Urbit-trap is:
**can the system survive having its meta-programming
infrastructure manipulate the AIR shape at runtime?** A Houyhnhnm
computing system would be able to upgrade its AIR shape
*without invalidating existing cells* by providing a typed
upgrade function from old-AIR-shape to new-AIR-shape and
replaying old turns through the new shape. `dregg` cannot do this
today. There is no *protocol* for it. There is no AIR-shape
lineage. There is no test that says "any pre-1.5 turn re-proven
under 1.5 produces a receipt compatible with its 1.4 receipt".

**Smallest fix (2 weeks for a real lineage; 1 day for an audit):**
1. **Audit (1 day):** add a section to `EXECUTOR-HONESTY-AUDIT.md`
   that *enumerates the AIR-shape commitments*. Every PI field,
   every effect-variant row encoding, every placeholder, every
   truncation. Make this a **canonical reference**: when the
   AIR changes, this document changes, and the change is the
   *protocol-version-bump* event.
2. **Infrastructure (2 weeks):** add `AirVersion` to PI. Every
   proof carries the version of the AIR shape it was generated
   against. Verifiers check the version against their accepted-
   versions list. When the AIR ships a new version, old proofs
   continue to verify under their old shape (using a stored
   verifier for that shape). New turns must use the current
   shape. This is *literally* the same pattern as Rust edition,
   applied to AIR shape.
3. **Eventually:** add an upgrade function `old_air_pi → new_air_pi`
   for each minor version bump, with a CI test that a corpus
   of historical turns replays correctly. This is the
   houyhnhnm typed-upgrade pattern, applied to AIR shape.

---

## §3 — What dregg believes about itself that isn't true

This section is the most direct one. A list of claims dregg
makes in its own documents that the code doesn't honor.

### 3.1 "Proof-carrying capability mesh"

*Tagline of `NEW-WORLD.md`.*

What's true: dregg ships proofs *for some* turns. The proofs are
real. The verifier is standalone and works (`dregg-verifier` is
real per `NEW-WORLD.md`, demo'd in `SILVER-VISION-E2E-VERIFICATION.md`).

What's not true: "proof-carrying" implies *every authoritative
state transition carries a proof that algebraically attests its
correctness*. `dregg` has:

- Three executor-trusted boundary cuts (T9, bridge proof-to-action,
  BudgetCoordinator).
- Nine Effect VM PI placeholder variants.
- 30-bit truncations on bridge/escrow value commitments.
- `MockProofVerifier` still in use for intent fulfillment.
- The trustless intent engine's `MockProofVerifier` paths (see
  `intent/src/trustless.rs:682`) — yes, the *trustless* intent
  engine has a `MockProofVerifier`. The name "trustless" and the
  presence of `MockProofVerifier` are contradictory.

A more honest tagline: "a capability mesh, in motion toward
proof-carrying; trust boundaries enumerated in `SILVER-DEBT.md`".

### 3.2 "Executor honesty audit closes T1–T15"

*Framing of `EXECUTOR-HONESTY-AUDIT.md` and `NEW-WORLD.md` §"Executor honesty audit".*

What's true: T1–T15 have been *named*, and each has been
*assigned* a defense layer.

What's not true:
- The list is exhaustive. (It isn't — there is no published
  threat model from which T1–T15 are derived.)
- Each threat is closed. (Three remain open by the audit's own
  admission. T12 is closed *modulo 2^30 only*, which the audit
  doesn't say.)
- "Closed at AIR" = "soundly enforced". T10 ("Skip capability
  check") is marked closed at AIR because "per-effect AIR
  enforces the cap-presence check". For 4 CapTP variants this
  cap-presence check is *real Merkle membership* — the audit
  says so. For the *other* effects it is per-variant constraints,
  which may or may not be Merkle membership.

### 3.3 "Federation unified"

*Framing of `FEDERATION-UNIFICATION-DESIGN.md` and `NEW-WORLD.md` §"Federation and consensus".*

What's true: there is now one `Federation` type that subsumes
the previous four disjoint concepts; `federation_id = H(committee_pubkeys)`.

What's not true: the unification is complete. From
`federation/src/lib.rs:84-102`:

> NOTE (FEDERATION-UNIFICATION-DESIGN.md §6 step 6): the Morpheus
> BFT simulator (`node.rs` + `transport.rs`) is **legally dead**
> — `dregg-blocklace` is the live consensus path. The simulator
> survives as in-crate code only because `teasting`, `wasm`, and
> `demo/sdc-consensus` still import it.

The simulator is re-exported as `MorpheusFederation`. The
"unification" describes the *intended* state; the *code* still
contains the old shape, marked "legally dead" but compiled in.
The next reader (human or LLM) sees two `Federation`s and is
confused. Houyhnhnm's deletion discipline would have *deleted
the dead code* even at the cost of breaking `teasting/`, then
let `teasting/` migrate. Carrying the dead code as a placeholder
is the same anti-pattern as the SILVER-DEBT debt above: the
"temporary" version is shipped.

### 3.4 "Storage primitives are cell-program patterns, not new Effects"

*Framing of `STORAGE-AS-CELL-PROGRAMS.md` and `NEW-WORLD.md` §"Storage as cell-programs".*

What's true: the *intent* is that primitives like `CapInbox`,
`ProgrammableQueue`, `PubSubTopic` should compose existing
Effects under cell programs with slot caveats.

What's not true: this has happened in code. `NEW-WORLD.md` itself
lists in §"What's not done" item 6:
> Storage primitive migrations — Phase 1 (ProgrammableQueue →
> cell-program) and Phase 2 (CapInbox → cell-program) bring the
> design's thesis into code.

So the thesis is *not yet in code*. The current state is that
`storage/programmable/*` exists as a separate concept. The
slot-caveat vocabulary exists. The migration is pending.

This is a familiar pattern: a design doc declares the architecture,
the code lags. The houyhnhnm critique: don't ship the *intent*
as if it's the architecture. The architecture is what the code
does today.

### 3.5 "The same predicate vocabulary serves slot caveats and authorization"

*Framing of `NEW-WORLD.md` §"Predicates everywhere — one vocabulary".*

What's true: there is a unified `WitnessedPredicate` type that
maps to a kind registry; `Authorization::Custom { predicate:
WitnessedPredicate }` exists; `StateConstraint::Witnessed(WitnessedPredicate)`
exists.

What's not true: this unification is *operationally complete*.
`CAVEAT-LAYER-COVERAGE.md` line 95 says:
> `Witnessed { wp: WitnessedPredicate }`: **exec REJECTS
> unconditionally** — cell evaluator returns
> `Err(WitnessedPredicateRequiresExecutor { kind_name })`. The
> `WitnessedPredicateRegistry` exists in `cell/src/predicate.rs:412-490`
> with stubs (`with_stubs()`) and a `register_builtin` /
> `register_custom` shape, but **the executor's call site at
> executor.rs:4343-4393 does not consult any registry** — the
> sentinel just propagates to `TurnError::ProgramViolation`. So
> `Witnessed` cell programs are uncreatable in practice.

So the unified vocabulary exists in the *type system*, but the
*runtime path through it is broken*. The marketing claim and
the code are not aligned. This is exactly the houyhnhnm
"unenforced abstraction" critique from Ch.6: an abstraction that
the runtime doesn't actually honor.

### 3.6 "Slop-list deleted"

*Framing of `NEW-WORLD.md` §"Starbridge — dregg's IDE/runtime".*

This one is actually mostly true. `amm`, `lending`, `orderbook`,
`stablecoin`, `dao-treasury`, `prediction-market` — all gone.
This is genuinely Houyhnhnmoid. But: the remaining
`apps/` directory *still exists alongside* `starbridge-apps/`
("The legacy `apps/` retires as starbridge-apps replace each one").
This is the same dual-shipping pattern as Federation: the new
thing is announced, the old thing lingers. Either delete or
declare a date.

### 3.7 "The 14-boundary vocabulary"

*Framing of `BOUNDARIES.md` and `NEW-WORLD.md` §"Boundary discipline".*

What's true: there is a useful taxonomy
(`cleartext-inside / commitment-inside / acceptance-inside / out-of-band`).

What's not true: "the vocabulary is enforced". `NEW-WORLD.md`
itself says: "The doc names nine inconsistencies (e.g.,
`FieldVisibility::Committed` hides from external readers but NOT
from the host executor; sovereign cells *intended* to hide from
host, implementation does not yet algebraically enforce). The
vocabulary is a *rustdoc convention*, not a new type system."

So nine documented inconsistencies, and the discipline is by
*convention*, not by *type*. The honest framing: dregg has a
*vocabulary* for thinking about boundaries; the *enforcement* is
nine items short.

This is *not bad* — it's better than not having the vocabulary —
but the marketing should not say "discipline" if it means
"convention with nine documented exceptions".

---

## §4 — Where dregg is genuinely Houyhnhnmoid

Fairness section. `dregg` does meet, and in some places exceed,
the houyhnhnm bar.

### 4.1 Capability-secure substrate

OCapN-lineage capability transport with sturdy refs, three-party
handoff (CapTP `HandoffCertificate`), bearer caps, sealed caps,
faceted caps — this is the houyhnhnm "linear-logic resource
discipline" (Ch.6) realized through the capability paradigm. Not
the *same* discipline, but a recognizable extensional cousin:
authority moves; nothing is ambient; the system tracks who can
exercise what against whom.

Houyhnhnm would approve. Ch.7's "implicit communication" and
Ch.6's "proxies and handles" are reasonable mappings to caps.

### 4.2 WitnessedReceipt chain as persistence stream

For the layer it covers (state transitions on the ledger),
WitnessedReceipt does what Ch.2's orthogonal persistence
prescribes: every state-changing event is in a log; the log is
replayable; the log carries cryptographic provenance. The fact
that dregg arrived at this from cryptographic-correctness
requirements while Houyhnhnms arrived at it from ergonomic
requirements is the *convergence-as-validation* that
HOUYHNHNM-COMPARISON.md correctly names.

### 4.3 Multi-backend differential testing

`dregg-dsl-differential` (40 cases × 5 voting backends; 2
lint-only) is *exactly* the houyhnhnm "if you have an
implementation strategy, it must preserve the semantics of the
high-level language" pattern from Ch.4 — automated and tested.
This is *more* than Ann would have demanded; she would have
considered it a *minimum* but dregg has *built* it. Promote
this pattern to the cell-program layer (see §2.8) and dregg is
ahead of the bar in that dimension.

### 4.4 Determinism of the verifier

The verifier is genuinely deterministic and standalone
(`dregg-verifier` binary). Anyone holding the public information
about a federation can verify a third party's claim. This is the
Houyhnhnm test for "is this part of a computing system or just
a vendor's database?". `dregg` passes for this slice.

### 4.5 Federation-bypass via `peer_exchange`

The ability for two sovereign cells to interact without a
federation in the trust path — `cell::peer_exchange::PeerExchange`
— is *exactly* Ch.10's "Houyhnhnms each... want to ensure the
persistence of their own data and that data only". `dregg`
realises this in code. This is excellent.

### 4.6 Honesty about the gap

The very *existence* of `EXECUTOR-HONESTY-AUDIT.md`,
`CAVEAT-LAYER-COVERAGE.md`, `SILVER-VISION-E2E-VERIFICATION.md`,
the `NEW-WORLD.md` §"What's not done" section, and the GPT
session's `PROTOCOL-CATEGORICAL-ANALYSIS.md` — these documents
demonstrate a culture of writing down what's broken. Houyhnhnm's
Ch.11 anti-blame-game posture *requires* this kind of honest
inventory. `dregg` has it; many systems don't. The §3 ("what dregg
believes about itself that isn't true") above is *only possible
to write* because the system has documented its own
inconsistencies enough that they can be found. That itself is a
houyhnhnm achievement.

### 4.7 The slop-list deletion

Six apps deleted as the wrong shape (amm, lending, orderbook,
stablecoin, dao-treasury, prediction-market) is *exactly* the
houyhnhnm deletion discipline from Ch.2: "Deletion (as opposed
to mere de-indexing), while possible, gets more expensive as
the data you want to delete gets older". `dregg` paid the cost
*early* on these. Most projects never do. Houyhnhnms would
respect this.

### 4.8 `dregg-dsl` as a real DSL discipline

`dregg` actually has a DSL (`dregg-dsl`) with seven backends and
differential testing. Per Ch.10's critique of Urbit's
DSL-rejection ("Martians officially rejects abstraction... they
designed languages that superficially allow any random...
enthusiast to understand each of the steps of the program, by
making those steps very simple, minute and detailed"), dregg's
*acceptance* of DSL is a houyhnhnm move. The cross-backend
differential test is the test Ann would demand.

### 4.9 Persvati / remote-build pattern

The `ssh persvati` / `git push persvati main` pattern (per the
agent-memory note) — offloading workspace-scale verification to
a Linux box, keeping single-crate checks local — is a real
implementation of "use the right tool for the scale of the
problem". Houyhnhnm-aligned.

### 4.10 Trust-vs-data-flow separation in the trustless intent engine

Despite the `MockProofVerifier` parking, the *protocol* of
threshold-encrypted intents — Shamir-shared ChaCha20 key,
per-validator share with MAC, t-of-n combine, decrypt to real
Intent — is genuinely cryptographically sound and matches the
houyhnhnm "no party should learn what they don't need to know"
posture. The trust model is named; the deviations from it are
audited (`HOUYHNHNM-COMPARISON.md §4.1`).

---

## §5 — The credit-card-debt: Silver-as-shipping

This is the most operationally important section. Below is a
concrete enumeration of *every place* dregg ships the "Silver"
(trust-based) version into production while *labelling* the
result as if it were the "Golden" (algebraically-attested) one.

**Tier A: Marketing/code lies.** Things where the name doesn't
match the implementation.

| Where | What it claims | What it does |
|---|---|---|
| `intent/src/trustless.rs:682` | `MockProofVerifier` is used in the *trustless* intent engine | Mock acceptance of any proof of the expected size |
| `NEW-WORLD.md` tagline | "proof-carrying capability mesh" | Three executor-trusted boundary cuts; nine PI placeholders; MockProofVerifier in trustless path |
| `cell/src/program.rs:1014-1022` | `HashKind::Poseidon2` in `PreimageGate` | "stub that BLAKE3-hashes a tagged buffer rather than calling Poseidon2" (per CAVEAT-LAYER-COVERAGE.md) |
| `StateConstraint::Witnessed` | First-class predicate kind | "exec REJECTS unconditionally" (per CAVEAT-LAYER-COVERAGE.md line 95) |
| `EXECUTOR-HONESTY-AUDIT.md` T12 | Closed | Closed modulo 2^30 (the truncation is not disclosed in the audit ledger) |
| `federation/src/lib.rs:84` | "Federation unified" | Two `Federation` types still in tree (`Federation` + `MorpheusFederation`) |
| `BOUNDARIES.md` | "14-boundary vocabulary discipline" | "rustdoc convention, not a new type system" + nine documented inconsistencies |

**Tier B: Acknowledged debt.** Things explicitly marked in code
as `TODO[block1-bind]` or similar. Counted from `executor.rs`
alone: at least 12 `TODO[block1-bind]` instances. Each is a place
where the AIR projects a *placeholder value* (often `0`) instead
of the real value the AIR purports to bind. Each is a place where
a malicious prover with the right placement could produce an
accepted proof that doesn't reflect the actual transition.

| Where | What's TODO'd |
|---|---|
| `executor.rs:3373` | `queue_len: 0, // TODO[block1-bind]` — AIR binds zero, not actual queue length |
| `executor.rs:3374` | `program_vk: BabyBear::ZERO` — AIR binds zero, not the program VK |
| `executor.rs:3423` | `old_capacity: 0` — placeholder |
| `executor.rs:3392-3394` | "the actual head hash... runtime executor (TODO[block1-bind])" |
| `executor.rs:3486` | "Source new root = hash(source_old, message) — use a deterministic placeholder" |
| `executor.rs:3548` | "pair_id as a placeholder. Stage 2 reworks the..." |
| `executor.rs:3952-3957` | "remain placeholders because the runtime [...] TODO[block1-bind]" |
| `executor.rs:3999-4031` | "placeholder; the AIR's `refcount > 0` check..." |
| `executor.rs:4066` | "(TODO[block1-bind]) carries them through the..." |
| `circuit/src/effect_vm.rs:2305` | `TODO(range-checks)` for lookup arguments |
| `circuit/src/effect_vm.rs:2326` | `TODO(underflow)` for non-negative range proof |
| `circuit/src/effect_vm.rs:835` | "30-bit value-truncation fix" — opt-in 4-limb path, but the legacy 30-bit path is still alive |

**Tier C: Architectural debt.** Things that aren't TODOs but are
fundamental shape-bets that haven't yet been delivered:

| What | Where named | Status |
|---|---|---|
| Effect VM as one large AIR (vs. per-family AIRs joined by recursion) | `HOUYHNHNM-COMPARISON.md §9.6`; `KIMCHI-SURVEY.md`; `STAGE-7-GAMMA-2-PI-DESIGN.md` | Open structural question. Per-family AIRs would close §2.4's monolithic-executor problem too. |
| AIR shape versioning protocol | (this doc, §2.10) | Does not exist |
| Source-as-canonical for cell programs | (this doc, §2.8) | Does not exist; identity is VK-hash |
| Typed upgrade function for program changes | (this doc, §2.1) | Does not exist |
| Sub-additive blame model in audit ledger | (this doc, §2.7) | Does not exist |
| Persistence stream beyond ledger | (this doc, §2.2; HOUYHNHNM-COMPARISON §9.1) | Does not exist |
| Sovereign-witness AIR teeth Phase 1 | `NEW-WORLD.md` §"What's not done" item 3 | Designed, not implemented |
| Sovereign-witness AIR teeth Phase 2 | Same | Designed, blocked on plonky3 recursion |
| Bridge proof-to-action binding in circuit (not executor comments) | `EXECUTOR-HONESTY-AUDIT.md`; `NEW-WORLD.md` | Lives in executor comments today |
| `coord::BudgetCoordinator` signature verification | `NEW-WORLD.md`; threat-test with comment "Forged signature not verified in rebalance yet" | Two real security bugs, parked |
| Storage primitive migrations Phase 1-2 | `NEW-WORLD.md` §"What's not done" item 6 | Designed, not implemented |
| Morpheus retirement Block 6 (physical deletion) | `NEW-WORLD.md` §"What's not done" item 7 | Dead code 2515 LOC still in tree |
| Token caveat modernization | `NEW-WORLD.md` §"What's not done" item 9 | "Discard the 12 ancient caveat types"; still in tree |

**The total picture:** dregg is at the moment a *demo of the
Silver Vision* (correctly per its own description) that is being
*written about as if it were the Golden Vision*. The houyhnhnm
test from Ch.11 — *what tool would you choose for the long run
if you knew the long run was coming?* — sharpens this. Silver
is the right tool for *demonstrating the substrate is in place*.
It is *not* the right tool for *shipping to external auditors
who will trust the tagline*. The choice of which mode dregg is
currently in needs to be louder.

---

## §6 — Five sharpest actionable improvements, prioritized

These are the changes I would make first if I had a free week.
Each one is concrete, bounded, and addresses a structural
houyhnhnm-test failure above. Ranked by *expected
information-per-effort* — meaning, by how much the change
reduces ambiguity in the system's actual trust footprint.

### #1 — Write `SILVER-DEBT.md` and make it CI-checked (1 day; massive value)

*Addresses §2.9 (low time-preference) and §3 (claims vs. code).*

One markdown file at the top level. Three sections:
- **Tier A (Marketing/code lies):** name-implementation
  mismatches. Each entry has `(claim)`, `(claim-source: file)`,
  `(actual-behavior: file:line)`, `(plan: resolution path)`,
  `(can-it-be-Golden?: yes/blocked-by-X/never)`. Start with the
  table in §5 Tier A above.
- **Tier B (Acknowledged debt):** every `TODO[block1-bind]`,
  every `TODO(range-checks)`, every `TODO(underflow)`. CI script
  greps for these markers; fails the build if any TODO isn't
  enumerated in `SILVER-DEBT.md`.
- **Tier C (Architectural debt):** structural bets that haven't
  delivered yet. Each entry has `(what)`, `(named-where)`,
  `(would-close-which-houyhnhnm-test)`, `(rough-effort)`.

This *one document* lets external readers — and the next agent
that lands on this codebase — understand the trust footprint
without having to spelunk. It is the *minimum* low-time-preference
move.

### #2 — Add a `LinearityClass` to every Effect variant + a CI test for AIR-projection-faithfulness (3 days; structural)

*Addresses §2.3 (linear-logic on resources) and §2.10 (the Urbit-trap).*

Add `#[linearity = "Conserved"]` (or similar) annotation on each
`Effect` variant. Write a build-time test: for every `Conserved`
variant, the AIR projection must cover the full field value (no
30-bit truncation, no zero placeholder, no slot-only hashing).
Fail the build if not.

The result: it becomes *impossible* to merge a new `Conserved`
effect whose AIR projection lies. Existing violations
(`BridgeMint/Lock/CreateEscrow` 30-bit truncation) become red
in CI. They must either be fixed or explicitly re-classified as
`Free` (with a comment explaining why this is acceptable). Most
will get fixed.

This is the houyhnhnm "type-level enforcement" move applied to a
specific load-bearing class of effects.

### #3 — Split `turn/src/executor.rs` into per-effect-family modules (2 weeks; foundational refactor)

*Addresses §2.4 (polycentric kernels) and as a side effect §2.10 (Urbit-trap on the runtime side).*

13,905-line single file → ~10 files of 500–1500 lines each.
No behavior change. After the split:

- A new effect variant is a new file, not a 12-match-statement
  audit.
- Each closure of a Silver-tier debt (the 9 placeholder PI
  variants in NEW-WORLD §"What's not done" item 1) becomes a
  PR against one file.
- The cognitive cost of further refactors drops dramatically.

This is the *enabler* for #4 and several other improvements.
Do this once, and a year's worth of follow-on refactoring
becomes possible. Don't do this, and every refactor is blocked
by the 13,905-line file.

### #4 — Introduce `AirVersion` into PI, with a `dregg-air-registry` of accepted versions (2 weeks; closes the Urbit-trap)

*Addresses §2.10 (the Urbit-trap) and §3.4 (architectural debt on AIR shape evolution).*

Every PI gains a `air_version: u32` field. Verifiers carry a set
of accepted versions. New turns must use the current version.
When the AIR shape changes (new effect variant, new placeholder
gets resolved, new range-check gadget), the version bumps. Old
proofs continue to verify under the stored old verifier.

This is the protocol layer that *makes dregg's AIR shape
evolvable without invalidating cells*. Without it, every AIR
change is a wreck. With it, AIR evolution is a normal protocol
event. This is the difference between the houyhnhnm answer and
the Urbit answer.

(In parallel, write the *first* upgrade: `air_v1 → air_v2` is
the trivial one. Use this to validate the upgrade-function
discipline before any actual incompatible shape lands.)

### #5 — Add `ProgramTransition` with typed upgrade function (3 days for the type + 1 week for migration tooling)

*Addresses §2.1 (code-and-data-as-one-history).*

`SetVerificationKey` becomes `SetVerificationKey {
program_transition: ProgramTransition }` where `ProgramTransition
= { from_vk, to_vk, upgrade_witness: WitnessedPredicate,
state_diff_kind: StateDiffKind }`. Receipts cover it. A new
`dregg-program-lineage` micro-crate tracks the lineage of each
cell's program changes.

This is the closest dregg can come to Ch.5's "every type
modification is accompanied by a well-typed upgrade function"
without rebuilding the whole runtime. It costs almost nothing
and removes the "silent program swap" attack surface entirely.

---

## Closing

The three deepest things wrong with dregg, viewed from
houyhnhnm:

1. **The 13,905-line executor is the kernel, full stop.** Every
   houyhnhnm-test about polycentric kernels, about
   meta-programming, about the Urbit-trap, fails immediately at
   the size of this file. The dregg runtime model is
   *polycentric*; the dregg implementation is monolithic. The
   gap is not a documentation flaw; it is a structural one.

2. **The Silver-vs-Golden distinction is doing too much work.**
   It is currently absorbing the burden of "the system claims X
   but does Y" without naming it as such. The tagline
   "proof-carrying capability mesh" promises Golden. The shipping
   reality is Silver-with-placeholders. External readers cannot
   tell the difference because the placeholders are scattered
   across 12+ source files with `TODO[block1-bind]` markers and
   no central inventory. This is the credit-card-debt model from
   Ch.11 applied to a soundness budget.

3. **Identity is the VK, but the VK is not source.** This is
   the Urbit-trap, walking. `dregg` arrived at the same shape
   Urbit did (a fixed semantic encoding with identity rooted in
   the encoded artifact, not the source) and the same failure
   modes are starting to accrue (encoder bugs are catastrophic;
   no upgrade story; no lineage; no AIR-version protocol). The
   mitigation dregg claims (VK-versioning + honesty audit) is
   *named* but *not enforced*; the threat is real.

The one thing dregg genuinely got right that Ann would respect:
**the honesty inventory itself.** The fact that
`EXECUTOR-HONESTY-AUDIT.md` and `CAVEAT-LAYER-COVERAGE.md` and
`SILVER-VISION-E2E-VERIFICATION.md` and `NEW-WORLD.md` §"What's
not done" *all exist* means dregg has the *culture* required to
fix the structural failures. Ann would not have written this
critique about a project that didn't already have those
inventory documents to draw from.

The single sharpest improvement to make first: **#1 above —
write `SILVER-DEBT.md` and make it CI-checked, today.** Until
the trust footprint is documented in one place, every other
improvement is invisible to the next reader. Once it is, the
priority of the remaining improvements becomes obvious to
everyone — including the toolsmith, who under Ch.11 is the only
one with the standing and the duty to fix the tools.

> "When a casual user mistake causes a tool to fail
> catastrophically, fools blame the user who operated the tool;
> wise men blame the toolsmiths who built the tool."

The toolsmith — dregg itself, plural — has a window of low cost
to fix this now, before any external user is in a position to
be hurt by the gap between the tagline and the implementation.
After that window, the blame-game from Ch.11 becomes operational.
