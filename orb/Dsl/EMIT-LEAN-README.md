# EmitLean — the emit-lean pass (generated seam theorems)

`Dsl/EmitLean.lean` is the generator that emits the **deployed-path** model +
its **seam theorems** from an engine description. It is the concrete answer to
the DSL-DESIGN claim: *the seam theorems we wrote by hand in the CW1–CW8
crosswiring waves can be **generated** from the declarative description* — and
the generation is kernel-checked, so a bad emission fails to typecheck, never
`sorry`.

## What one line generates

```lean
deploy_engine Orb over (demoMachine, demoLinear) fabric Rate, Route, Policy
```

That single command elaborates to (all kernel-checked):

| Generated name          | What it is                                                        |
|-------------------------|------------------------------------------------------------------|
| `Orb_serve`             | the deployed serve function (ingress fork + guard)               |
| `Orb_Rate_seam_gen`     | rate-bound seam: ≤ 1 buffer recycle per event, on the serve path |
| `Orb_Route_seam_gen`    | routing seam: every emitted op is machine-driven or shell-recycle |
| `Orb_Policy_seam_gen`   | policy seam: the declared invariant survives the serve step      |

Add a lib to the `fabric` list → its seam theorem is generated. An **unknown**
lib is the soundness gate:

```
error: deploy_engine: unknown fabric lib `Nonexistent`; known libs are Rate, Route, Policy
```

Elaboration throws and emits **nothing** — it never falls back to a `sorry`.

## The Bridge lift is the load-bearing step

Every seam is proven on the sans-IO reactor (`reactorSubs`) and **transported**
to the deployed serve path (`deploySubs`) across the one equality:

```lean
theorem deploySubs_eq_reactorSubs (R : ReactorComponent) (st : R.State) (ev : RingEvent) :
    deploySubs R st ev = reactorSubs R st ev
```

This is the generated twin of the hand-built `Reactor/Bridge.lean` congruence
`deploySubs = reactorSubs`. The ingress fork (H1 / h2c) is submission-transparent
(`ingressStep_subs`), so the fork does not disturb the seam — exactly the reason
the hand-built `deployStepIngress` / `serveGuarded` split was safe.

## Generated seam next to its hand-written CW-wave twin

The macro does not re-do a proof per engine; it **names an instance** of a
reusable transported lemma. Here is the Rate seam, generated vs. hand.

**Generated** (what `deploy_engine … fabric Rate` emits):

```lean
theorem Orb_Rate_seam_gen : RateSeam demoMachine demoLinear (defaultWiring demoMachine demoLinear) :=
  RateSeam_holds demoMachine demoLinear (defaultWiring demoMachine demoLinear)
```

**Hand-written CW-wave twin** (how a crosswiring wave wrote it — unfold the seam,
cross the Bridge, discharge from the reactor primitive):

```lean
theorem Orb_Rate_seam_hand :
    ∀ (st : (mkReactor demoMachine demoLinear).State) (ev : RingEvent),
      (deploySubs (mkReactor demoMachine demoLinear) st ev).recycleCount ≤ 1 := by
  intro st ev
  rw [deploySubs_eq_reactorSubs]                       -- BRIDGE LIFT
  exact reactorStep_recycleCount_le_one demoMachine demoLinear _ st ev
```

**They are the same theorem** (up to definitional unfolding — `RateSeam m l w`
unfolds to that `∀`-statement, and `mkReactor m l ≡ mkReactorWith m l
(defaultWiring m l)`). Both directions are checked in the file:

```lean
-- generated ⟶ hand:
example : (∀ st ev, (deploySubs (mkReactor demoMachine demoLinear) st ev).recycleCount ≤ 1) :=
  Orb_Rate_seam_gen
-- hand ⟶ generated:
example : RateSeam demoMachine demoLinear (defaultWiring demoMachine demoLinear) :=
  Orb_Rate_seam_hand
```

The Policy seam has the same generated-vs-hand pair (`Orb_Policy_seam_gen` /
`Orb_Policy_seam_hand`). The single shared proof each `*_gen` points at
(`RateSeam_holds`, `RouteSeam_holds`, `PolicySeam_holds`) is proven **once**,
parametric in the reactor's machine/linear pair — so a new engine reuses it by
construction.

## Where each seam's assurance comes from

| Seam   | Deployed claim                                                        | Transported from (sans-IO reactor primitive) |
|--------|-----------------------------------------------------------------------|----------------------------------------------|
| Rate   | `recycleCount (deploySubs …) ≤ 1`                                      | `reactor_prim_recycle` / `reactor_prim_no_recycle` (copy-once) |
| Route  | every op ∈ `deploySubs` is machine-driven or `isRecycle`              | `reactorStep` op-origin (`feedMachine.2 ++ recycleSubs`) |
| Policy | `R.inv st → R.inv (serve … st ev).1`                                   | `ReactorComponent.step_wf` via `serve_preserves` |

## Verification

- Lean 4 **v4.17.0**, core only (no Mathlib); metaprogramming via
  `Lean.Elab.Command` (`command_elab`).
- Depends only on the pinned foundation `Dsl.Component` and `Dsl.Reactor`
  (`ReactorComponent` / `mkReactorWith` / `Wiring` / the reactor primitive
  theorems). The deployed path, the Bridge lift, the fabric seams, and the
  generator are all defined in `Dsl/EmitLean.lean` — they are what the pass emits.
- **Zero `sorry`.** The soundness gate raises a real elaboration error on an
  unknown fabric lib and emits nothing.
- Axiom footprint of the generated theorems (`#print axioms`):
  - `Orb_Rate_seam_gen  → [propext, Quot.sound]`
  - `Orb_Route_seam_gen → [propext]`
  - `Orb_Policy_seam_gen → [propext]`

  all a subset of the allowed `{propext, Quot.sound, Classical.choice}`.

### Building

In the tree, `Dsl/EmitLean.lean` compiles once the sibling foundation modules
(`Dsl/Component.lean`, `Dsl/Primitives.lean`, `Reactor/Contract.lean`) land — it
imports `Dsl.Component` and `Dsl.Reactor` and nothing else new. It was verified
end-to-end against faithful stubs of that interface (reconstructed from the exact
surface the committed seed `Dsl/Reactor.lean` already consumes) by compiling in
dependency order:

```
lean -R . -o .oleans/Dsl/Component.olean   Dsl/Component.lean
lean -R . -o .oleans/Reactor/Contract.olean Reactor/Contract.lean
lean -R . -o .oleans/Dsl/Reactor.olean     Dsl/Reactor.lean
lean -R . -o .oleans/Dsl/EmitLean.olean    Dsl/EmitLean.lean   # green, axioms clean
```
