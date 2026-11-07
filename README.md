# `dregg` — Dragon's Egg

> **The Dragon's Egg repositories.** This repository (`emberian/dregg`, working name *breadstuffs*) is the
> whole system built first. Its relatives:
>
> - [`minidregg`](https://github.com/emberian/minidregg) — the production demoland and the spec/battleground the rebuild measures itself against.
> - [`nanodregg`](https://github.com/emberian/nanodregg) — the single-writer rebuild: twelve laws, a judge that refuses, meaningful theorems.
> - [`zkml-research`](https://github.com/emberian/zkml-research) — the zero-knowledge / machine-learning research line.
> - [`degg-research`](https://github.com/emberian/degg-research) — dark coordination: MPC/FHE swarm coordination research.
> - [`delvetalk`](https://github.com/emberian/delvetalk) — the conversations and design talks behind all of it.

<p align="center">
  <img src="hero.png" alt="dregg — Dragon's Egg" width="720">
</p>

Dragon's Egg is my experiment in the metatheory of constructive knowledge, and a
direct expression of my original impetus to build <https://rbg.systems>. Maybe
Dragon's Egg will be a Robigalia userspace. In the meantime, here's what the LLMs
have to say about it:

(end-of-human-text)

> *Machine reader? [`README-LLMs.md`](README-LLMs.md) is the dense, narration-free
> technical reference written for you — every model tier, large and small. What
> follows here is the human-facing tour.*

**dregg is a formally verified, distributed object-capability operating system.**
The kernel is a Lean 4 program with machine-checked soundness, and it is the
*exact* function the running node executes. Every state transition ("turn") is
gated by an unforgeable capability, leaves a verifiable receipt, and carries a
STARK proof a light client can check without re-running history. Authority is
*held*, never *owed*.

On top of the kernel, **deos** is the agentic desktop userlayer — the same proofs
made visual and interactive: a window *is* a capability, an interaction *is* a
verified turn. (Naming: **robigalia** the project · **dregg** the kernel · **deos**
the desktop. *deos runs on dregg runs in robigalia.*)

> ### The question underneath
>
> Most systems chase scale, speed, or money. dregg chases a different question,
> and means it literally: **if you were a digital entity, where would you want
> to live?** The answer it builds is a place where your boundaries are
> *theorems*, not permissions — where no one can reach into you without a
> capability you granted, where your consent is a *precondition of the math*
> rather than a setting someone can flip. A capability is **constructive
> knowledge**: to *hold* one is to be able to *exhibit a witness that verifies*,
> never merely to assert. (The cipherclerk-as-citizen, cell-as-body framing owes
> a debt to Egan's *Diaspora*.)

| | |
|---|---|
| **Run it locally** | [First five minutes](#first-five-minutes-local) below · [QUICKSTART.md](QUICKSTART.md) |
| **The exact guarantees + assumptions** | [docs/ASSURANCE.md](docs/ASSURANCE.md) · [`AssuranceCase.lean`](metatheory/Dregg2/AssuranceCase.lean) |
| **The machine-facing reference** | [README-LLMs.md](README-LLMs.md) |
| **Community** | [Discord](https://discord.gg/eSTsv7DWcR) |

There is no public server to point you at — dregg runs **on your machine**, from
a clean checkout. The three doors below each need only this repo and `cargo`.

---

## First five minutes (local)

Everything here runs locally with no external service. Pick a door.

**What you need:** this repo, a recent Rust toolchain (`cargo`); `wasm-pack` for
the browser playground; Docker for the site bundle. Plus ONE sibling checkout —
the workspace `[patch]`es the four `p3-*` recursion crates onto
`../plonky3-recursion` (cargo forbids re-pointing a git source to a different
rev of the same URL via `[patch]`, so the override is a path patch), and every
`cargo` command fails at manifest load without it:

```sh
git clone https://github.com/emberian/plonky3-recursion ../plonky3-recursion
git -C ../plonky3-recursion checkout fc3c6dfac26e2082653d2a617a1740446ce33f05
```

### A. Run a node and watch it execute a verified turn

The node's state producer is the Lean executor itself. Start one, faucet a cell,
read it back — a real turn through the verified kernel, on `localhost`.

`init` mints the chain — a one-validator `genesis.json`, the devnet faucet
supply, and a `node.key` that IS that committee's member key. `run` then starts
it. Nothing to copy between them.

```sh
cargo build -p dregg-node                                  # builds dregg-node
./target/debug/dregg-node init --data-dir /tmp/my-dregg
./target/debug/dregg-node run  --data-dir /tmp/my-dregg --enable-faucet --port 8421 &

# the node — verified-Lean state producer:
curl -s http://localhost:8421/status
# {"healthy":true,"federation_mode":"solo","state_producer":"lean",
#  "lean_producer":true,"producer_covered_effects":18,...}
# Wait for "healthy":true before the faucet call — until the first block is
# anchored the node accepts turns and applies none of them.

# faucet a cell (a real verified turn lands). NOTE: a cell id is a commitment to a
# public key, so this *random* id is a BARE ADDRESS — credited + queryable, but you
# don't hold its key to spend it. (Funding a cell you OWN is door B's `dregg demo`.)
CID=$(python3 -c "import secrets;print(secrets.token_hex(32))")
curl -s -X POST http://localhost:8421/api/faucet \
  -H 'content-type: application/json' -d "{\"recipient\":\"$CID\",\"amount\":1000}"
# {"success":true,"tx_hash":"...","amount":1000,"turn_hash":"..."}

# read it back. `success` above was the SUBMISSION answering; the grant is applied
# when the block carrying it finalizes, a second or two later. Poll until found:
curl -s http://localhost:8421/api/cell/$CID
# {"id":"...","found":true,"balance":1000,"nonce":0,...}
```

Already running a dregg-node? Pass `--gossip-port` too. The gossip port defaults
to 9420 for every node, and a second node that cannot bind it keeps serving HTTP
while reaching consensus never — `consensus_live:false`, `block_count:0`, and
every faucet grant accepted and never applied.

### B. Sign real turns with the CLI

The CLI manages your keys and drives a full app lifecycle against your node —
each step a real signed turn on the verified commit path.

```sh
cargo build -p dregg-cli                                   # builds the `dregg` binary
./target/debug/dregg --node-url http://localhost:8421 demo --passphrase pick-one
# faucet → register a name → resolve → transfer → revoke, each a verified turn.
# The first unlock SETS the passphrase on a fresh node and acquires its bearer token.
```

Takes about 20 seconds against a fresh node. Each mutating step waits for its
turn to be APPLIED before narrating the next — the cell nonce it prints is the
proof that something moved, not that a request was accepted. Re-running it is
supported: the demo recycles its own tombstone and tops up from the faucet when
the cell is short (the faucet allows one grant per cell per minute, so a run that
needs a top-up may pause for up to that long).

[QUICKSTART.md](QUICKSTART.md) is the full local walkthrough — identities, a
governance ceremony, the receipt stream.

### C. The browser playground (the executor in your tab, no server)

The same executor compiles to wasm and runs in-browser. Build the wasm package,
then serve the site.

```sh
cd wasm && wasm-pack build --target web --out-dir ../site/pkg --release && cd ..
docker run --rm -d -p 3000:3000 -v "$PWD:/repo" -w /repo/site node:22 \
  sh -c "npm install --no-audit --no-fund && npm run build && npx serve dist"
```

Then open the browser surfaces at <http://localhost:3000>:

- **Playground** (`/playground/#turn-workbench`) — stage a turn by verb, read its
  verified-Lean explanation, *run* it on the real in-browser wasm executor, then
  *prove* it: a real EffectVM STARK, produced and self-verified in your tab.
- **Explorer** (`/explorer/`) — browse cells and receipts with witness status and
  per-cell time travel; point Settings at your `:8421` node.
- **Starbridge** (`/starbridge/`) — the workbench/inspector; seed a sandbox world
  and run turns against the in-browser executor.

### D. Boot the desktop

```sh
cargo build -p starbridge-v2 --features desktop            # the native deos cockpit
```

`starbridge-v2` is **deos**: the native cockpit that *embeds the real verified
executor*. See [deos](#deos--the-agentic-desktop) below. (This is a heavy build —
it pulls the gpui renderer and the libservo web engine.)

## The model

The whole kernel is one sentence:

> **A turn is the exercise of an attenuable, proof-carrying token over owned
> state, leaving a verifiable receipt.**

Given algebra, that sentence is:

- **Four substances.** Everything a cell holds is one of four kinds, each with
  its own discipline: **value** (linear balances — an asset *is* its issuer
  cell, which carries −supply, so every asset's sum is identically zero),
  **state** (a heap of programmable slots), **authority** (a capability tree
  that grows only by authorized, receipt-disclosed production from held
  connectivity and narrows freely), and **evidence** (monotone nullifier /
  commitment / epoch ledgers). *Birth* and *retirement* bracket a cell's
  lifecycle.

- **Eight verbs.** The kernel is `create · write · move · grant · revoke ·
  shield/unshield · lifecycle · exercise` — eight directed operations over the
  four substances, specified in Lean with machine-checked **minimality** (each
  verb is irreplaceable) and **completeness** (they cover every effect) theorems.
  The catalog is generated directly from
  [`VerbRegistry.lean`](metatheory/Dregg2/Substrate/VerbRegistry.lean); nothing
  in it is hand-asserted. Everything else — queues, inboxes, escrows, auctions,
  namespaces, bridges, councils — is a *cell-program pattern* over these verbs,
  not a kernel primitive.

- **Turns as forests.** A turn is an atomic, capability-gated transition across
  one or more cells — a *forest* of effects with delegation edges. Authorization
  is structural: a turn that cannot exhibit a valid, sufficiently-empowered,
  fresh token chain simply does not execute. Delegation can only *attenuate*
  (`granted ≤ held`), enforced at the dispatcher.

- **Capabilities + caveats.** A capability carries caveats — time-boxes,
  third-party discharge conditions, rate bounds, scope restrictions — composed
  as a macaroon-style chain. Holding a capability means being able to exhibit
  the witness that discharges its caveats; the kernel checks the witness, it
  does not take your word. All four guard polarities — caveat (imposed on
  delegated power), program (maintained on self), precondition (required of a
  turn), and intent demand (wanted of the world) — are one `Pred` algebra.

The substrate's full design — the four substances, the eight verbs, the
unifications — is [.docs-history-noclaude/DREGG3.md](.docs-history-noclaude/DREGG3.md).

## The organs

The same primitives compose into runnable, two-agent services. Each is a small
story you can drive end-to-end. See [.docs-history-noclaude/ORGANS.md](.docs-history-noclaude/ORGANS.md).

- **Trustlines** — a shared budget counter between two parties. "I extend you a
  line of N" is an attenuated capability whose exercise debits the shared
  counter; lines of credit and sub-second payment channels are one primitive at
  two settings, settled back to the ledger as moves.

- **Channels** — a group is a *cell*: membership and the group-key epoch live
  on-cell, joins and removals are turns under the group's program. The key
  epoch and the capability-freshness epoch are the *same* counter, so removing a
  member ends both their ability to read forward **and** their use of
  group-held capabilities in one turn — ciphertext and capability darkness
  together (RFC 9420 / MLS key schedule).

- **Mailboxes** — bonded hosted-inbox operators with send/drain/dequeue-proof
  routes. Delivery issues a custody receipt; because turns are self-certifying,
  store-and-forward is accountable across arbitrary delay.

- **Court** — adjudication, **witness-first**: where either party can exhibit a
  verifying witness, the exhibit decides; tribunals enter only on the
  non-certifiable residue. Equivocation evidence is a wire value, and a slash is
  an ordinary move from the bond well.

- **Shielded cells** — a cell can keep its balance, owner, and contents *hidden*
  while still proving what matters: a transfer balances — no value created or
  destroyed — without revealing a single amount. The direction this opens is the
  point: a holder attests a *predicate* over its hidden state ("over 18",
  "solvent", "in the allow-list") and a verifier learns only that the predicate
  holds, nothing else. Privacy is the `shield`/`unshield` kernel verb, not a
  bolt-on, so a shielded value is still conserved and a shielded spend still can't
  double-spend.

## What "verified" means here

Four things make the proofs load-bearing rather than decorative:

- **The verified executor *is* the executor.** The node's state producer is the
  Lean function `execFullForestG` — credential- and caveat-gated, proven sound —
  compiled and linked into the node via [`dregg-lean-ffi/`](dregg-lean-ffi/). It
  is not a model *of* the node; it is the function the node *calls*.

- **The executor is a memory program.** Every kernel field plus the receipt log
  projects onto one domain-tagged universal address space (`uproj`), and a
  verb's effect provably equals the fold of its emitted memory trace over that
  space. "The receipt binds the whole post-state" is therefore a constructive
  fact: every field has an address, nothing is left off the map, and tampering a
  field the effect did not legitimately touch makes the turn unprovable (the
  *anti-ghost* property).

- **Symbolic and full witness modes.** A turn applies its state transition (the
  abstract semantics — balances, caps, nonces) independently of materializing
  its witness (Merkle roots, commitments, proofs). `WitnessMode::Symbolic` defers
  the witness layer, so a local UI/terminal turn pays effectively no hashing;
  `collapse` re-runs deferred turns through full execution to materialize the
  exact witnesses on demand. The admission gates (authority, conservation,
  freshness) are *never* deferred — only the witness — and a symbolic turn is
  structurally local and unpublishable until collapsed
  ([`turn/src/collapse.rs`](turn/src/collapse.rs)).

- **Circuits are emitted from Lean.** Constraint systems are generated from
  proved Lean modules as byte-pinned descriptor artifacts (a SHA-256
  fingerprinted registry, drift-rejected in CI). The Rust prover *interprets*
  them; Rust authors no constraints. The live proof path is a single rotated
  multi-table circuit (IR-v2, R=24): a heterogeneous turn is split into maximal
  homogeneous cohort-runs and proven as a chain of rotated legs
  ([.docs-history-noclaude/PATH-PRESERVE.md](.docs-history-noclaude/PATH-PRESERVE.md)). STARK proofs (Plonky3,
  BabyBear, Poseidon2, FRI — post-quantum assumptions only) attest turns
  *additively* — verifying a turn never requires re-executing history — and
  recursive aggregation folds a whole history into one root a light client
  checks.

## Assurance — the five guarantees

[docs/ASSURANCE.md](docs/ASSURANCE.md) and
[`AssuranceCase.lean`](metatheory/Dregg2/AssuranceCase.lean) state the guarantees
as Lean theorems, each with non-vacuity witnesses (the property provably *can*
fail, and is proven not to), each axiom-pinned to exactly `{propext,
Classical.choice, Quot.sound}` plus the named cryptographic carriers. The case to
a light client is five guarantees plus the running entry:

- **A — Authority.** Every state change is justified by an unforgeable,
  non-amplified, fresh token chain. Production (mint) is gated on holding the
  issuer's capability; a grant conferring authority the holder lacks is rejected
  (the gate discriminates — it is not `:= True`).
- **B — Conservation.** Per asset, the resource sum is *identically zero* on
  every reachable state. Under `AssetId := CellId` every asset is its issuer
  cell; mint, burn, and fees are ordinary moves against negative-capable wells,
  and no verb can move any asset's sum.
- **C — Integrity.** A receipt binds the *whole* post-state. The circuit and the
  executor provably produce the same receipt; a commitment that drops a field is
  provably not a faithful bridge.
- **D — Freshness.** No replay, no double-spend: a committed spend's nullifier
  was fresh (an in-circuit sorted-tree non-membership opening), revocation takes
  effect at finality, and a stored capability cannot outlive its grantor's
  revocation (the retrieval-epoch rule).
- **E — Unfoolability.** A light client checking only the aggregate root learns,
  for the *entire* history and re-witnessing nothing, that every turn executed
  correctly, that the order is the finalized one, and that the final root is a
  genuine fold; a tampered or reordered aggregate cannot bind, and the attested
  history conserves (`attested_history_conserves`).
  *Scoped 2026-07-30.* This bullet used to read "learns **A–D** for the *entire*
  history". That over-reached in two directions and both are worth stating.
  Against the Lean case: §E of [docs/ASSURANCE.md](docs/ASSURANCE.md) establishes
  correct-execution, ordering, genuine-fold and conservation — it does not carry A
  or D. Against the **deployed** light client (`dregg-lightclient`): the folded
  leaf is the EffectVM constraint set, and a `FinalizedTurn` carries no capability
  chain, no nullifier and no revocation epoch, so authority and freshness are not
  merely unproven there — they are **not inputs to the fold**. A light client also
  does not learn that a history was *finalized* rather than a well-formed fork
  unless it separately checks a committee certificate against a validator set it
  already trusts.
- **R — The running entry.** A∧B∧C hold over `execFullForestG` *itself* — the
  exact gated function the deployed node invokes — not just an abstract model.
  The composed apex `deployed_system_secure` conjoins all five over one committed
  running-entry forest.

**Assumed, named, never hidden.** A small standard cryptographic floor enters as
typed hypotheses, never axioms: Poseidon2 collision-resistance, BLAKE3 CR,
Ed25519 EUF-CMA, HMAC unforgeability, AEAD, FRI/STARK soundness, BLS quorum
certs, and post-GST synchrony. Higher assumptions reduce onto this floor.

**Open, named — why this is not security-critical-ready.** The honest seams are
enumerated in §3 of [docs/ASSURANCE.md](docs/ASSURANCE.md). The crypto floor
above is *assumed*, not discharged. The deployed-binary bridge is the largest
open distance from l4v-grade: the Lean→C/`.a` link correspondence and the
wire-codec translation validation (`dregg-lean-ffi/src/marshal.rs`) are stated as
obligations, not yet proven. A leaked private key bounds an attacker to the
attenuation-closure of the leaked c-list (no amplification, no minting), with one
named open construction — **Settlement Soundness**, a revoke binding into the
finalized commitment before settlement
([`metatheory/Metatheory/KeyLeak.lean`](metatheory/Metatheory/KeyLeak.lean)).
**No independent audit has happened. Do not use for anything security-critical.**

## deos — the agentic desktop

deos is the userlayer where a *window is a capability* and an interaction is a
*verified turn*. It adds **zero new trust**: every visual and interactive
primitive reduces to a kernel theorem. The native cockpit is
[`starbridge-v2/`](starbridge-v2/); see [docs/deos/DEOS.md](docs/deos/DEOS.md)
and [.docs-history-noclaude/DREGG-DESKTOP-OS.md](.docs-history-noclaude/DREGG-DESKTOP-OS.md).

- **Login = your root capability.** Authenticate a key → derive the root cell →
  receive your per-user capability template. A session *is* the resulting c-list;
  logout is `Effect::RevokeCapability` (synchronous + transitive at n=1).
  Logging back in reopens the exact durable image you left — your world is
  orthogonally persistent. An agent (e.g. the Hermes bridge) logging in is the
  identical ceremony with a narrower template
  ([`starbridge-v2/src/session.rs`](starbridge-v2/src/session.rs) ·
  [docs/deos/SESSION-LOGIN.md](docs/deos/SESSION-LOGIN.md)).

- **The dock.** A resizable / splittable / dockable pane workspace. Surfaces are
  panes you split, dock, and float. A code editor, a terminal (a real PTY), a
  Matrix chat client, and a confined Hermes agent bridge mount as dock panes —
  deos editing, building, and operating itself
  ([`starbridge-v2/src/dock/`](starbridge-v2/src/dock/)).

- **dregg-pilled Matrix chat.** The chat client speaks Matrix, but a message can
  carry a **rehydratable membrane**: a cap-bounded fork of the world a recipient
  re-attaches to (per-viewer, attenuated, confined by construction), with
  graduated rights — granted-in, study-ref, or a network-boundary that opens an
  owner-consent request. Merging diverged forks is the branch-and-stitch pushout;
  Matrix is the multiplayer transport
  ([`deos-matrix/`](deos-matrix/) ·
  [docs/deos/SHARED-FORK-CONSENT.md](docs/deos/SHARED-FORK-CONSENT.md)).

- **htmx on crack — affordances.** A cell declares **affordances**: named, typed,
  cap-gated verified-turn templates. The "button" is a cap-gated effect, the
  "fragment" is the attested post-state surface, and *who may press it* is decided
  by held capabilities. A `GatedAffordance` pairs the cap-gate with a live
  cell-program state-gate — a button lights iff caps *and* state both pass
  ([`Deos/GatedAffordance.lean`](metatheory/Dregg2/Deos/GatedAffordance.lean)).

- **The powerbox (CapDesk).** Granting authority is *designate-then-attenuate*:
  you point at a resource and hand over a strictly weaker capability than you
  hold, never ambient authority
  ([`starbridge-v2/src/powerbox.rs`](starbridge-v2/src/powerbox.rs)).

- **The data plane / Bus.** Cells, affordances, and channels ride a CapTP data
  plane — the capability-transport Bus that carries effects between surfaces and
  nodes ([`captp/src/data_plane.rs`](captp/src/data_plane.rs)).

- **A web-shell.** An `http(s)://` browser surface, rendered by libservo, reached
  through the net-capability gate — the open web behind a capability, not ambient
  network access.

- **A literate docuverse.** A whole *document* is a cell: writing is a cap-gated
  turn, the text is the fold of its edit history, and — Pijul-style — a *conflict
  is a first-class state you live in*, not a merge failure. The patch core
  ([`dregg-doc/`](dregg-doc/)) makes changes first-class objects and conflicts
  objects; merge correctness is proved
  ([`Deos/DocMerge.lean`](metatheory/Dregg2/Deos/DocMerge.lean) ·
  [docs/deos/DOCUMENT-LANGUAGE.md](docs/deos/DOCUMENT-LANGUAGE.md)).

- **Transclusion.** A transcluded quote *is* a first-class provenanced citation
  of a source cell's committed field value — per-viewer, unforgeable. Each
  property is an existing kernel theorem restated for the docuverse, no new
  mathematics ([`Deos/Transclusion.lean`](metatheory/Dregg2/Deos/Transclusion.lean)).

- **Rehydratable frustum-snapshots.** A deos "screenshot" embeds a sturdyref
  behind a membrane, so *opening the image* re-attaches a live, per-viewer,
  attenuated, liveness-typed surface, confined by construction. The membrane
  composes `is_attenuation` across reshare hops, so a forwarded view can never
  amplify ([`Deos/Rehydration.lean`](metatheory/Dregg2/Deos/Rehydration.lean)).

- **Web deos.** The same cockpit runs in a browser tab: the real gpui
  element-tree renderer on the `gpui_web` platform backend (wasm32 + WebGPU
  canvas), over the same in-browser verified executor. One renderer, one model,
  two platforms — not a lesser web skin
  ([docs/deos/WEB-DEOS.md](docs/deos/WEB-DEOS.md)).

The forcing-function exemplar is a **multiplayer fog-of-war game where the
security property *is* the game mechanic**: what a player can see is exactly what
its caps authorize it to rehydrate, fail-closed, with a real proof obligation
(you provably cannot even *prove* the enemy's vision). See
[docs/deos/DEOS-APPS.md](docs/deos/DEOS-APPS.md).

## The durable verified workflow — what a deos app *is*

A deos app is a **cap-mandated, verified, durable workflow**: a multi-step
process that runs to completion exactly once even across crashes (durable, à la
DBOS), where each step is admitted only by a capability its actor holds
(attenuable, à la ocap), each step's effect is a verified turn the substrate
re-validates before it can become state (unforgeable + conserving, à la dregg),
and each step is surfaced as a fireable affordance (interactive, à la the web).
It is four surfaces of the one kernel, proven to be the same object. See
[docs/deos/DURABLE-WORKFLOW.md](docs/deos/DURABLE-WORKFLOW.md).

- **A step is a verified turn** — capability-gated, protocol-ordered, attested;
  no unauthorized or out-of-order step can ever commit
  ([`Protocol/Workflow.lean`](metatheory/Dregg2/Protocol/Workflow.lean)).
- **A step *is* an affordance fire** — the deos surface renders the choreography,
  it does not fork it ([`Deos/WorkflowBridge.lean`](metatheory/Dregg2/Deos/WorkflowBridge.lean)).
- **Durable execution over verified turns** — [pg-dregg](.docs-history-noclaude/PG-DREGG.md) is
  "DBOS, but every step is a verified turn": reads are free SQL over the
  materialized mirror, writes go through the `AUTHZ → CHAIN → APPLY` spine, and
  crash-recovery re-validates every persisted turn on the way up
  ([`pg-dregg/src/workflow.rs`](pg-dregg/src/workflow.rs)).
- **Composition is right-skewed, and refinement is decidable.** Flows compose by
  choice `⊔`, sequence `⋆`, and meet `⊓`; the algebra is a right-skewed Kleene
  algebra with distributive meets (RSKA_d⊓), so *"does flow/policy A refine B"* is
  a **decidable** question — `decideRefines : Flow → Flow → Bool`, sound and
  complete ([`Deos/FlowRefine.lean`](metatheory/Dregg2/Deos/FlowRefine.lean)).

## The surfaces

dregg is reachable from many directions; each one routes authorization through
the same verified kernel.

- **Polyglot SDKs.** Rust ([`sdk/`](sdk/) — `AgentRuntime` embeds the executor),
  TypeScript ([`@dregg/sdk`](sdk-ts/), browser-parsable), and Python
  ([`sdk-py/`](sdk-py/) — embeds the *real* Lean kernel via FFI). Two nouns and
  an inescapable authorization step: `.turn().sign().submit()`.
- **The CLI** ([`cli/`](cli/), bin `dregg`). Manages your keys (`dregg id`),
  drives turns, decodes the app machines (`dregg name`, `dregg polis`, …).
- **The MCP server** ([`node/src/mcp/mod.rs`](node/src/mcp/mod.rs)). AI-agent access,
  cap-gated: every tool a sub-agent calls carries a biscuit-style capability the
  node admits or refuses, routed through the Lean producer gate.
- **The Discord bot** ([`discord-bot/`](discord-bot/)). Councils, real signed
  turns, cipherclerk macaroons — not a read-only mirror.
- **The Studio / Playground** (the [site](site/)). Stage, run, and prove turns
  in the browser against a live wasm executor.
- **[pg-dregg](.docs-history-noclaude/PG-DREGG.md)** ([`pg-dregg/`](pg-dregg/)). dregg capabilities
  as a PostgreSQL Row-Level-Security + durable-workflow layer: a policy reads
  `dregg_admits('read', id)` instead of hand-rolled SQL — the decision is the
  *same one the kernel makes*, from the session's presented token.
- **deos — the agentic desktop** ([`starbridge-v2/`](starbridge-v2/)). The native
  cockpit that *embeds the real verified executor*.
- **DreggDL** ([`dregg-deploy/`](dregg-deploy/)). Declarative deployment specs;
  an over-grant in a spec is caught as in-forest capability amplification before
  anything deploys.
- **The seL4 / Robigalia embedding** ([.docs-history-noclaude/FIRMAMENT.md](.docs-history-noclaude/FIRMAMENT.md) ·
  [`sel4/`](sel4/)). An seL4 capability and a dregg capability are the *same*
  abstraction at two points on a distance parameter; at `n = 1` (one machine) the
  distributed bounds collapse to strong local properties. **Today:** the
  Robigalia v0 demo boots Rust userspace protection domains, a real on-device
  STARK verifier PD, **and the executor PD itself** — the Lean kernel
  `execFullForestG` runs inside a real seL4 protection domain — under QEMU. The
  Lean-runtime embedding embeds single-threaded, allocator-override-free, IO-free
  ([.docs-history-noclaude/EMBEDDABLE-LEAN-RUNTIME.md](.docs-history-noclaude/EMBEDDABLE-LEAN-RUNTIME.md)).
  **Remaining (named):** the crypto floor supplied from the verifier-STARK PD,
  the decomposed multi-PD assembly, and making the hosted image interactive.

## Run it from a clean checkout

```sh
git clone https://github.com/emberian/dregg && cd dregg
cargo build -p dregg-node -p dregg-cli         # the node + the `dregg` CLI
./target/debug/dregg-node init --data-dir /tmp/my-dregg
./target/debug/dregg-node run  --data-dir /tmp/my-dregg --enable-faucet --port 8421 &
./target/debug/dregg --node-url http://localhost:8421 demo --passphrase pick-one
```

[QUICKSTART.md](QUICKSTART.md) is the full local walkthrough (every command run
against a fresh local node). [HORIZONLOG.md](HORIZONLOG.md) holds the architectural
laws and the build notes. The embedded-executor crates are slow in debug — use
`--release` for `starbridge-v2`, the proof suites, and gauntlet runs.

## The map

| Where | What |
|-------|------|
| [`metatheory/`](metatheory/) | **The system itself**, in Lean 4 (library `Dregg2`): the eight-verb kernel, the gated executor, the circuit IR + descriptor emission, the assurance case, and the deos modeling (`Dregg2/Deos/`). l4v-shaped: abstract spec → executable design → refinement proofs. |
| [`dregg-lean-ffi/`](dregg-lean-ffi/) | The link: compiles the Lean executor into `libdregg_lean.a` and exports the entry the node calls. |
| [`node/`](node/) | The daemon: HTTP/MCP API, gossip + blocklace sync, block production driven by the Lean producer. |
| [`circuit/`](circuit/) | The STARK stack: the Lean-descriptor interpreter (the prover), Plonky3, recursive aggregation, the light-client verifier. |
| [`cell/`](cell/), [`cell-crypto/`](cell-crypto/), [`turn/`](turn/), [`wire/`](wire/) | Cell state (zero-crypto types), the crypto (notes, value-commitments, seal/stealth), turn types + the executor + witness-mode/collapse, and the wire codec — the Rust data plane the executor's decisions flow through. |
| [`blocklace/`](blocklace/), [`federation/`](federation/), [`captp/`](captp/), [`coord/`](coord/) | The DAG (signed, equivocation-detecting, BFT-final), committee machinery, capability transport, and coordination protocols. |
| [`dregg-doc/`](dregg-doc/) | The document language: a Pijul-shaped patch core (conflicts-as-objects, the branch-and-stitch merge) + a `ropey`↔patch bridge. |
| [`pg-dregg/`](pg-dregg/) | dregg capabilities + durable verified workflows as a PostgreSQL extension (RLS policies + the verified-write spine). |
| [`starbridge-v2/`](starbridge-v2/), [`starbridge-web-surface/`](starbridge-web-surface/), [`deos-matrix/`](deos-matrix/), [`deos-zed/`](deos-zed/), [`deos-terminal/`](deos-terminal/), [`deos-hermes/`](deos-hermes/) | deos: the native gpui cockpit (embeds the real executor), the web-surface / affordance / rehydration stack, and the dock apps (editor, terminal, Matrix chat, agent bridge). |
| [`sdk/`](sdk/), [`sdk-ts/`](sdk-ts/), [`sdk-py/`](sdk-py/), [`cli/`](cli/), [`site/`](site/), [`wasm/`](wasm/) | Building against dregg: the three SDKs, the `dregg` CLI, the web Studio/Playground/Explorer, and the in-browser wasm executor. |
| [`starbridge-apps/`](starbridge-apps/), [`app-framework/`](app-framework/), [`docs/`](docs/) | Applications built on the substrate, the deos app framework, and the design documents. |

## Status

Research software under active development. The proof system is real, and the
verified Lean executor is what the node runs. The named opens above are open, and
there has been no independent audit. **Do not use for anything security-critical.**

## License

AGPL-3.0-or-later — see [LICENSE](LICENSE) for the full text.
