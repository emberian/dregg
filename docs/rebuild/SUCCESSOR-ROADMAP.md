# dregg2 → real dregg1 SUCCESSOR — the gear-shift roadmap

> **Honest status (2026-05-29, end of the big session).** What exists is a **verified
> micro-core + the right architecture + a working cascade mechanism** — NOT a verified
> distributed OS, and NOT yet a dregg1 successor. This doc is the plan to make it one.
> Reads with `DREGG1-TO-DREGG2.md` (crate fates), `ROADMAP.md`, `dregg2.md`.

## What's REAL today (machine-checked, no inflation)
- A Lean4 project that compiles: **31 modules, ~2979 jobs, 0 errors, 19 honest `sorry`**.
- A **toy kernel core**: `KernelState = Finset accounts + bal : CellId→ℤ + cap list`;
  `exec`/`step` does ONE of {transfer, mint, burn, grant/revoke cap}. PROVED for it:
  conservation, fail-closed authorization, **step-completeness** (`Exec/StepComplete.cexec_attests`
  — all 4 `StepInv` conjuncts), and a **circuit bridge** (`Circuit.bridge :
  satisfied kernelCircuit ↔ fullStepInv`, both directions) from which `CryptoKernel.verify`'s
  §8 law is DERIVED.
- The **portals** `CryptoKernel`/`World` (uninterpreted Lean⟷Rust interface).
- A **working FFI** (`dregg-lean-ffi/`): Rust hosts the compiled kernel; **10k/10k
  golden-oracle differential** vs a Rust reference.
- Honest classification of the 19 `sorry`: interface obligations (portal laws) + genuine
  open theorems (Byzantine quorum-intersection, GST-liveness, family joint-soundness).

## The toy→real gap (what "successor" actually requires)
| Layer | Toy now | Real dregg1-successor needs |
|---|---|---|
| **Cell/state** | accounts + ℤ balances + cap list | a sovereign **cell** = data-model value + multi-asset resources + slot-table + a `CellProgram` (the real `cell/`); the camera resource model deployed |
| **Turn** | one transfer/mint/burn/cap-op | the real **call-forest / effect tree**, predicates+caveats, the 6-clause auth-in-proof chain, partial turns / WitnessedReceipts |
| **Authority** | `actor == src` or a cap in a list | real cap **derivation/attenuation/revocation** kernel + the l4v integrity proof over IT (not abstract) |
| **Multi-cell** | `JointBinding` as hypothesis (proved sound) | the executable **JointTurn** = γ.2 bilateral aggregation; reuse the existing `circuit::bilateral_aggregation_air` |
| **Consensus/finality** | tier lattice + abstract `committed` + `World` stub | a real protocol (blocklace / Cordial-Miners) discharging `World`; the Byzantine theorems |
| **Privacy** | algebraic tier proved over `CryptoKernel` | real Pedersen/stealth/nullifier/ZK as the `CryptoKernel` Rust impl |
| **Circuit** | 4 scalar ℤ-equations | the real field-AIR; the `chainOk`→Poseidon-digest binding; extract `kernelCircuit` to the prover |
| **CapTP/GC** | caps model + GC laws/impossibilities | the transport protocol + an executable collector |

## Phased plan to BE the successor (not a demo)
**Phase A — grow the verified kernel core to dregg1's real shape.** Replace the toy
`KernelState`/`Turn` with the real cell (multi-asset camera resources, slot-table, a
`CellProgram` interpreter), keeping every law (`exec_conserves`/`cexec_attests`/`bridge`)
proved as it grows. This is the heart: make the *verified* kernel cover what dregg1's
`turn`/`cell` crates actually do.

**Phase B — execute the cascade (DREGG1-TO-DREGG2.md), oracle-first.** For each
REPLACE-BY-LEAN crate (`turn`, `cell`, `coord`): (1) extend the differential harness to
the crate's real conservation+authority+predicate checks, (2) drive Lean≡Rust to 100% on
its real inputs, (3) re-seat the Rust check onto the FFI'd Lean kernel. Frozen v1 stays
until its check is oracle-equal. Real `CryptoKernel`/`World` Rust impls (Poseidon/Pedersen/
WHIR; net/clock) are the contract.

**Phase C — close the metatheory.** Find remaining mis-stated theorems (the
abstract-parameter risk — 4 found so far), close the deep opens (or pin them as named
assumptions), grow the circuit to the real AIR, totalise `CellProgram→TurnCoalg`.

**Phase D — reorg + polish.** Move flat Abstract files → `Metatheory/Spec/Abstract/`;
the `Spec/Exec/Proof/Foundation/Protocol` layout; slim the heavy `import Mathlib.Tactic`.

## Robigalia relationship (scope)
rbg (Robigalia) is the seL4-based OS; **dregg is a *component* of it**, not the OS. We do
NOT boot, integrate seL4, or own the kernel-on-metal — `~/dev/sel4` + the rust-in-seL4
frameworks are rbg's job. dregg2 earns inclusion in rbg by being a good enough verified
distributed-object/capability layer. So "dregg2 should be bootable" is a non-goal; "dregg2
is a real, verified dregg1 successor that rbg can host" is the goal.

## The discipline that got us here (keep it)
Spec-first, every claim compiler-checked; NO fake-to-pass (honest `sorry` with PRIMITIVE/
OPEN notes, never `axiom`/`admit`/`native_decide` cheats); race-free parallel via
`lake env lean`; the portals keep crypto out of the trusted Lean; the differential harness
keeps Rust ≡ the Lean golden oracle.
