# PyanaScript — design and exploration

A directory for design notes, explorations, and prototypes of the
behavior/protocol language for pyana app authoring. **Not yet a language;
not yet code.** This directory captures the design conversation that
precedes the language.

## The two-language model

pyana has two distinct surface languages serving different layers:

1. **`pyana-dsl`** (exists today) — *caveat predicate language*.
   Descended from macaroons/biscuits. Row-shaped, constraint-shaped,
   multi-backend (gen_air, gen_plonky3, gen_kimchi, gen_sp1, gen_midnight,
   gen_datalog, gen_rust). Stays sparse. Used for: token caveats, cell
   program predicates over field slots, anywhere a "this proposition
   over data must hold" check is needed.

2. **`pyanascript`** (this directory's subject) — *behavior / protocol
   language*. Targets: cell behaviors (how a cell responds to messages
   and capability exercises), inter-cell composition (CapTP-shaped),
   app-framework primitives (escrow, auction, voting), capability
   composition with attenuation. Compiles down to: typestate-ActionBuilder
   calls, cell program declarations (which themselves may emit pyana-dsl
   predicates), CapTP wire protocols.

The two languages **compose**: pyanascript invokes pyana-dsl when it needs
a caveat predicate. They don't compete.

## Design discipline (the bottom-up principle)

The discipline that produced this directory:

> Before designing the surface language, imagine the **runtime API** it
> would compile to. Implement (or design) every primitive as an ugly
> Rust method-chain. If the chain is awkward, the awkwardness is real
> and identifies what's missing in the SDK/runtime. Macro the chains
> once they work. Only then consider what the surface language should
> look like.

Macro layer closes the ergonomic gap; language closes the grammatical
gap. We don't need the language until we know what the grammar must
support — and the only way to know is to live in the macro layer.

## Open questions

### Q1. What's the runtime API surface?

What do these look like as plain Rust method chains, written in
`pyana-sdk` or a new `pyana-cell` crate?

```rust
let cell = Cell::new(wallet)
    .with_state(MyState::default())
    .with_behavior(handler);

cell.send(target_cap, MsgKind::Bid { amount: 100 })?;
let response = cell.exercise(cap, args).await?;
let attenuated = cell.attenuate_cap(cap, narrower_permissions)?;
cell.spawn_child_with_behavior(child_spec)?;
cell.on_receive(|state, msg, caps| { ... });
```

How much of this exists today? How much would we have to add to the
SDK to make it expressible? The audit of "what's missing in the SDK
to support this method-chain shape" is the prerequisite for any
language work.

### Q2. PureCake or CakeML as compile target?

Two concrete candidates the user has flagged for exploration. The
prior wording of this section named PureScript and called it "compiles
to JavaScript" — that was wrong. `~/dev/pure` is **PureCake**, not
PureScript. Corrected descriptions follow; see
[`exploration-pure-and-cakeml.md`](exploration-pure-and-cakeml.md)
for the full investigation.

- **PureCake / PureLang** (`~/dev/pure`) — a **HOL4-verified
  compiler** for a small, **Haskell-like, lazy** functional language.
  PureLang has Haskell-shaped syntax (`data`, `case ... of`,
  do-notation, `[a]`, `:` cons) and is **lazy by default**, with
  verified demand analysis. **It targets CakeML**, not JavaScript:
  PureCake lowers PureLang through verified intermediate languages
  (ThunkLang, StateLang, …) into CakeML source, which CakeML then
  compiles to native machine code. Developed in HOL4 by the cakeml
  organization. Status: active, modest pace (~200 commits/year).
  Limitations: no type classes in the mainline compiler yet (an
  in-progress `typeclass/` branch is wiring dictionary translation);
  no import system; type signatures parsed but ignored.

- **CakeML** (`~/dev/CakeML`) — verified ML implementation, HOL-derived
  semantics, verified compiler chain **all the way down to machine
  code** (x86-64, ARMv8, MIPS, RISC-V). **Strict / call-by-value**.
  ML surface with Haskell-curried constructors and a few divergences
  from SML (no let-polymorphism, no equality types, RTL evaluation).
  FFI is C-shaped: programs compile to `.S` files exposing `cml_main`,
  linked against a `basis_ffi.c` shim — Rust can speak to it via
  `extern "C"`. Bonus payloads: **Candle** (a verified HOL Light
  *inside* CakeML), **Pancake** (verified C-like systems language),
  **`translator/`** (proof-producing HOL→CakeML), **`cv_translator/`**.
  Status: very active (~3900 commits/year, last commit 2026-05-11).
  Genuinely compelling for the svenvs integration story: svenvs's
  HOL theorems can reach into CakeML-compiled pyanascript through
  the verified compiler theorem.

Neither commitment is necessary up front. Both are research-grade,
not "drop-in 2026-Q3 backend." Leading verdict: **CakeML is the more
credible target**; PureCake is interesting-but-speculative; the right
near-term experiment is a 1-page proof-of-life (hand-write one cell
behavior in CakeML, link to CapTP via FFI, measure pain). Possible
outcome: neither — the FFI seam doesn't carry three-party CapTP
handoffs cleanly — and pyanascript gets its own implementation,
likely on Lean 4.

### Q3. What semantics?

- Process algebra (π-calculus, CSP) — clean compositional semantics
  for capability-secure systems (caps as channels). Mathematically
  beautiful, hard to author in.
- Actor model — familiar "this is what I do when I receive X" mental
  model. Less precise semantics, easier to author in.
- Session types — `Cap<Bid → Settlement → Receipt>` would make
  cross-cell protocols statically checkable. Compose with both above.
- Effect handlers (Eff / Koka / OCaml 5) — "I declare what effects
  this behavior can produce; the compiler ensures none escape." Maps
  naturally onto the pyana Effect enum.
- Refinement types — `Cap<Transfer> ⊑ Cap<TransferAtMost(100)>`
  checkable at compile time. Capability attenuation as a type-system
  property, not a runtime check.

Probably some hybrid. Probably actor-shaped surface, π-calculus-
derived semantics, session-typed cap exchanges, refinement-typed
attenuation.

### Q4. Lineage and references

Pyana's design lineage already names many points:

- **E language / Goblins / OCapN** — ocap semantics (the user's
  philosophy doc names this as direct ancestry)
- **Mina zkApp model** — cells-as-accounts, recursive proofs
- **Fly.io macaroons** — attenuable bearer tokens (pyana-dsl's origin)
- **seL4 / L4.verified** — formal capability discipline
- **Greg Egan's Polis** — software citizens
- **svenvs** — verified safety envelopes

References worth studying for pyanascript specifically:
- **Hash / Unison** — content-addressed code, distributed composition
- **discord-bot's DiscordCapability** — the "capability + adapter"
  userspace pattern already in pyana
- **OCapN protocol** — formal capability transport that pyana's CapTP
  draws on
- **biscuit-rs** — caveat-language ancestry, may inform pyana-dsl
  evolution

## Status

- README.md (this file) — captures the design conversation
- No code, no grammar, no compiler
- Next concrete step: **audit the SDK surface** to identify what's
  missing for the "ugly Rust method chain" form to work for a real
  app (e.g., a re-implementation of nameservice or escrow using
  hypothetical method chains, identifying every API gap)

## Cross-references

- `dev-philosophy/01-north-star.md` — what pyana is for
- `STAGE-7-PLUS-DESIGN.md` — the proof-system trajectory pyanascript
  compiles into
- `STAGE-7-GAMMA-AGGREGATION-DESIGN.md` — cross-cell aggregation
  semantics pyanascript will eventually surface
- `WITNESSED-RECEIPT-CHAIN-DESIGN.md` — the replay semantics
  pyanascript's runtime must produce
- `DSL-TO-EFFECT-VM-FEASIBILITY-STUDY.md` — why pyana-dsl stays at
  the caveat layer and doesn't grow into EffectVM territory
