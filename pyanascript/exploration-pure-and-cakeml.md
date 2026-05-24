# PureCake and CakeML as pyanascript compile targets — exploration

Field notes from reading `~/dev/pure` and `~/dev/CakeML`. The README in
this directory previously named `~/dev/pure` as "PureScript — compiles to
JavaScript." That is wrong on every axis. This document replaces that
sketch with what these projects actually are and evaluates them as
backends for pyanascript.

## What `~/dev/pure` actually is — PureCake / PureLang

`~/dev/pure` is **PureCake**, a verified compiler for a small,
Haskell-like lazy functional language called **PureLang**. It is not
PureScript and it does not target JavaScript.

- **Language family**: Haskell-shaped. Source files are written `.hs`
  and use Haskell-style syntax: `data Tree a = Leaf | Branch ...`,
  `case ... of`, do-notation, list `:` cons, `[a]` lists, top-level
  mutual recursion, `let` (mutually recursive, reorderable), pattern
  matching that must be exhaustive, lambdas.
- **Semantics**: **Lazy / non-strict by default**, matching Haskell.
  PureCake's meta-theory directory contains a formalization of
  *demands* (a strictness analysis) precisely because laziness is the
  default. The compiler's ThunkLang IR exists to express thunking and
  forcing explicitly; passes like `mk_delay`, `dlam`, `let_force` are
  laziness-aware optimizations. So: lazy by default, with verified
  demand analysis driving optional strictification.
- **Surface gaps from Haskell**: no type-class system in the
  mainline compiler yet — type signatures are *parsed but ignored*
  (`id :: a -> a` is a comment to the typechecker); a separate
  in-progress `typeclass/` subtree is wiring Wadler/Blott dictionary
  translation in but type inferencing, parsing, and the soundness
  proof for `NestedCase` are still TODO. No import system (the
  `examples/prelude` is "building blocks you paste in"). Constructors
  must be fully applied. No `<=`/`>=` on integers yet. Strings are
  packed-bytes (Haskell `Text`), not `[Char]`. Built-ins are exposed
  via `#(__Concat)` / `#(stdout)` / `#(cline_arg)` syntax.
- **Compilation target**: **CakeML**. PureCake compiles PureLang
  through a sequence of verified IRs (PureLang → ThunkLang → StateLang
  → ...) down to CakeML source, which CakeML then compiles to native
  machine code. So PureCake is parasitic on CakeML; the laziness story
  ultimately runs as strict ML with explicit thunks.
- **Author/lineage**: developed at Chalmers / UNSW (cakeml org on
  GitHub), same community as CakeML. HOL4 throughout.
- **Status**: **active maintenance, modest pace**. The repo had ~200
  commits since 2024 (vs. CakeML's ~3,900 in the same window). Last
  commit on `main` is a COPYING update dated 2026-01-01. Recent merged
  PRs include "cake-thunks" and a `check_thm` top-level correctness
  theorem. Bootstrapped compiler binary builds. Examples compile and
  run via `make foo.exe`. The project is a serious research artifact
  but not at CakeML's velocity.
- **What's *verified***: a refinement from PureLang's denotational
  semantics down to CakeML source, composed with CakeML's own
  verification chain to machine code. Equational/observational
  equivalence is proved; alpha and beta soundness are proved;
  coincidence with contextual equivalence is proved. Type
  soundness for the in-progress typeclass elaboration is proved
  except for `NestedCase`.

In one sentence: **PureCake is a HOL4-verified Haskell-subset → CakeML
compiler, lazy by default, that piggybacks on CakeML's verified path
to native machine code.**

## What `~/dev/CakeML` actually is

This is the project the wider verification community already knows:
**CakeML**, a verified implementation of a significant subset of
**Standard ML**, developed in HOL4.

- **Language family**: Standard ML with curated departures. CakeML
  has Haskell-curried constructor syntax (constructors must be
  capitalised, fully applied), capital `True`/`False`/`Ref`, no
  let-polymorphism, no equality types (all closures are equal),
  right-to-left evaluation order, no functors/records/open at
  present. Otherwise it's recognizable ML: `fun`, `val`, `case`,
  `structure`, `datatype`, `exception`, references, arrays, vectors,
  Word64, bignum `int`, polymorphic equality, exceptions with
  `handle`.
- **Semantics**: **strict / call-by-value**, well-defined
  right-to-left evaluation order. The semantics directory provides
  big-step (functional and relational), small-step, FFI, and type
  system definitions, all in HOL4 .sml files.
- **Compilation target**: **native machine code** (x86-64, ARMv8,
  MIPS, RISC-V, etc.) via a verified compiler chain — lexing → PEG
  parsing → type inference → AST → multiple IRs → ASM assembly → bytes.
  Verification ceiling: **machine code**. The proof composes through
  every pass, including register allocation and code generation. This
  is the project's headline claim.
- **FFI story**: CakeML programs are compiled to `.S` files that
  expose `cml_main` and friends; a small `basis_ffi.c` shim connects
  CakeML's basis library to system calls. FFI calls in CakeML go
  through named entry points (e.g. `#(stdout)` in PureLang maps to a
  C function `ffistdout`). Calling **into** CakeML from Rust is a
  matter of linking `cake.S` + `basis_ffi.o`, then calling
  `cml_main`. Calling **out** to Rust means writing C wrappers that
  Rust exposes via `extern "C"`. There is no idiomatic Rust binding
  layer; everything goes through C-ABI FFI strings.
- **Bonus payloads**:
  - **Candle**: a verified HOL Light theorem prover *implemented in
    CakeML* — meaning CakeML can host a kernel-verified prover.
  - **Pancake**: a C-like systems language using CakeML's lower
    backend, target for low-level verified code.
  - **`translator/`**: a proof-producing translator that turns HOL
    functions into CakeML automatically. This is the secret weapon
    for connecting HOL-proven properties to executable artifacts.
  - **`cv_translator/`**: translates to the `cv` type for
    `cv_compute` (HOL's primitive-recursive evaluator).
- **Status**: **very active**. ~3,900 commits since 2024, last
  commit 2026-05-11. Used in production research at NICTA/Trustworthy
  Systems, Chalmers, UNSW. The 2017 PLDI/ICFP tutorial is still in
  the repo. The `version1` and `version2` tags exist for stability.

In one sentence: **CakeML is the gold-standard verified ML — a
strict/call-by-value language with a HOL4-verified compiler chain
from source to assembly, an FFI through C, and tooling (translator,
Candle, Pancake) for building proof-bearing native binaries.**

## Integration story: pyanascript → PureCake

### What it would look like

pyanascript → desugar to PureLang surface (Haskell-subset). Cell
behaviors become `IO ()`-typed top-level functions; capability
exercises map to `Act #(captp_exercise) cap_id args`-style FFI calls;
state becomes an `IORef`-equivalent via `Array a` (PureLang already
has `Array` and `Alloc/Deref/Update`). The actor mailbox shape from
pyanascript Q3 maps reasonably onto a lazy `IO` event loop.

Concretely: write a backend `gen_purelang` alongside the existing
pyana-dsl `gen_*` backends. It would emit `.hs` files that the
PureCake compiler then turns into CakeML, which CakeML turns into
machine code linked against a Rust-provided `basis_ffi.o`
implementing the CapTP/cell primitives.

### How it interacts with svenvs (verified safety envelopes)

PureCake's verification chain is *itself* a HOL4 theorem.
svenvs's HOL-proven properties about the cell model (capability
confinement, effect-VM soundness) could in principle be **composed**
with PureCake's compilation theorem to yield: "this compiled binary,
running on this CakeML runtime, preserves the cap-confinement
property svenvs proved." That composition is non-trivial — svenvs
would need to state its properties over PureLang/CakeML semantics,
not over an opaque Rust runtime — but it is *possible*, which is
not true of any other backend in the pyana stack.

### Verdict

**Interesting but speculative.** The laziness story is a feature for
some pyanascript shapes (lazy infinite event streams; demand-driven
cap exercise) and an obstacle for others (auditing "what runs when"
becomes harder; resource accounting against laziness is famously
painful). The lack of type classes means dictionary-passing must be
done manually or via the in-progress `typeclass/` elaboration, which
is not yet shippable. The lack of an import system means everything
ends up in one file. The killer point in PureCake's favor is the
svenvs composition story; the killer point against is that you are
adopting **two** verified compilers (PureCake *and* CakeML) and
need to track both.

**Cost**: 6–12 months for a researcher comfortable with HOL4 to
build a credible pyanascript→PureLang emitter; another 6–12 months
to make svenvs talk to PureCake/CakeML semantics in a way that
actually composes. **Year-scale.**

## Integration story: pyanascript → CakeML

### What it would look like

pyanascript → desugar to CakeML surface. Cells become `structure`s
with state held in refs; capabilities become abstract types with FFI
constructors; the actor loop is a `fun loop () = ...` over an FFI
inbox. `datatype` covers all the sum-type needs; pattern matching is
nested and full-featured. Effect tracking has to be done manually
(no effect system in the language) but can lean on the type-driven
discipline of capability-abstract types.

A backend `gen_cakeml` would emit `.cml` files compiled by `cake.S`
to native machine code, linked to a Rust-provided `basis_ffi.o`.

### How it interacts with svenvs

CakeML is the bedrock. svenvs already speaks HOL4. Any pyanascript
property phrased over CakeML's semantics can in principle be lifted
through the verified compiler to a property of the produced
machine code. The `translator/` lets you take HOL functions and
produce executable CakeML *with a proof* that the executable
matches the HOL spec — this is the cleanest "spec-to-binary" path
in the open-source verified-systems world.

### Verdict

**Most credible verified target available.** Strict semantics
match Rust's mental model and pyana's existing turn/receipt
discipline. FFI is C-shaped and Rust can speak C. CakeML is
under heavy active development. Pancake provides a low-level
escape valve. Candle proves CakeML can host real verification work.

**Pain points**: no let-polymorphism makes some generic code
painful; no functors/modules-as-first-class limits how cells can
be parameterized; equality semantics differ from Rust (closures
are equal); the basis library is small and you'll write a lot of
plumbing. No type classes — discipline-by-convention. Build times
for the full bootstrap are *hours*.

**Cost**: 3–9 months for a credible pyanascript→CakeML emitter
that handles the cell behavior subset. 6–12 additional months to
build a svenvs ↔ CakeML semantic bridge (i.e., state pyana cell
invariants over CakeML's small-step semantics, lift through the
compiler theorem). **Year-scale, but the year buys you a verified
binary.**

## Honest comparison

|                          | PureCake/PureLang      | CakeML                    |
| ------------------------ | ---------------------- | ------------------------- |
| Semantics                | lazy, demand-analyzed  | strict, RTL eval order    |
| Surface                  | Haskell-subset         | SML with Haskell touches  |
| Target                   | CakeML (→ machine code)| machine code              |
| Verification ceiling     | machine code (via Cake)| **machine code**          |
| Type classes             | WIP, not shippable     | none                      |
| FFI                      | through CakeML's       | C-ABI via `basis_ffi.c`   |
| Activity (commits/yr)    | ~200                   | ~3900                     |
| HOL→exe translator       | no                     | **yes** (`translator/`)   |
| Mental fit for pyana     | speculative            | natural                   |

## Verdict

**CakeML is the credible verified backend.** It is the more
actively maintained, more thoroughly verified, more
mentally-aligned-with-pyana option. The strict semantics match
Rust and match pyana's turn-by-turn discipline. The `translator/`
gives you a real path from HOL specs of cell behavior to running
binaries. Candle proves the substrate can host a kernel
verifier — exactly the shape svenvs needs.

**PureCake is a research curiosity worth tracking** but
adopting it now means betting on the in-progress typeclass branch
and on laziness as a fit for actor-shaped behavior, neither of
which has been demonstrated for systems work at pyana's scale.
Revisit in 2–3 years if PureCake's typeclass elaboration ships
and someone publishes a non-trivial systems program in PureLang.

**Neither is right *yet*** for production pyana work. The honest
near-term answer is: **stay in Rust**, use the existing
typestate-ActionBuilder and svenvs-as-meta-prover discipline,
and treat CakeML as a 12–24 month research direction rather than a
2026-Q3 backend. The right artifact in that direction is a
**1-page proof-of-life**: hand-write a single pyana cell behavior
(maybe `nameservice`) in CakeML, link it to the existing CapTP
crate via FFI, and measure how painful the FFI surface is. That
experiment costs a week and answers the only question that
matters: does the C-ABI seam between CakeML cells and the Rust
substrate carry the message shapes pyana actually needs, or does
it collapse on the first three-party handoff?

If CakeML's FFI cannot represent CapTP introductions cleanly,
the answer is **neither, and pyanascript gets its own
implementation** — probably hosted on top of MLIR or
[Lean 4](https://lean-lang.org/) (whose compiler is moving toward
self-verification and whose `#eval`/native compile story is
maturing fast). Lean 4 is the most likely "if not CakeML, then
what" alternative; it has a real systems-language ambition, a
real proof story, and a real Rust-interop conversation
happening in 2025–2026.
