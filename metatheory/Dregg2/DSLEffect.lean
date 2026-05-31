/-
# Dregg2.DSLEffect — the `dregg_effect <name> (args) : <Class>` effects eDSL (PHASE-EDSL DSL-C).

This is **DSL-C** of `docs/rebuild/PHASE-EDSL.md`, completing the eDSL trilogy:
  * DSL-A (`Dregg2/DSL.lean`)        — `dregg_program { … }` → a verified `Exec.RecordProgram`;
  * DSL-B (`Dregg2/DSLChoreo.lean`)  — `dregg_choreo  { … }` → a verified `Coordination.GlobalType`;
  * DSL-C (**here**)                 — `dregg_effect <name> (args) : <Class>` → an effect's
    `Spec.Conservation.LinearityClass` coloring + its INHERITED conservation obligation.

Where DSL-A parses cell constraints onto `RecordProgram` constructors and DSL-B parses MPST
statements onto `GlobalType` constructors, **DSL-C parses an effect *declaration* onto the
already-proved `Spec.Conservation` conservation primitives** (`LinearityClass`,
`requires_paired_sibling`, `is_disclosed_non_conservation`) and the `CatalogEffects` discriminator
(`Regime`, `Regime.ofClass`, `effectObligation`). Declaring an effect's color generates — it does
NOT hand-write — its conservation obligation as a `theorem`:

  * `Conservative`              ⇒ paired-sibling Σδ = 0   (`requires_paired_sibling = true`)
  * `Generative` / `Annihilative` ⇒ disclosed non-conservation (`is_disclosed_non_conservation = true`)
  * `Monotonic` / `Terminal` / `Neutral` ⇒ INERT (neither paired nor disclosed)

## The rail (same as DSL-A/B; PHASE-EDSL §3, REORIENT §6)
The eDSL is a **parser onto already-proved constructors and theorems** — a `command`/`term` macro
translating each declaration to the EXACT `Spec.Conservation` / `CatalogEffects` shape. There is
**no new metatheory** and **no `sorry`**: the generated obligation theorem is closed by the proved
class-obligation lemmas of `CatalogEffects` (`conservative_requires_paired`, `generative_discloses`,
`annihilative_discloses`, `monotonic_inert`, `terminal_inert`, `neutral_inert`) — or, equivalently,
by `rfl` against the `Spec.Conservation` `def`s (the `LinearityClass` classifiers compute). The
surface→theorem map is pinned here by `rfl`/`#assert_axioms`.

HONEST: this is a PARSER onto proved constructors. It introduces no `axiom`/`admit`/
`native_decide`/`sorry`. The `rfl`-coincidences (each declared effect's color equals the
`CatalogEffects.effectLinearity` coloring of the namesake catalog variant) are pinned with
`#assert_axioms`. The whole namespace is `#assert_namespace_axioms`-clean.

## Surface (effect declaration → coloring + obligation)
  `dregg_effect transfer (amount) : Conservative`
      ↦  `def transfer.color    : LinearityClass := .Conservative`
         `def transfer.regime   : Regime         := .Paired`            (`Regime.ofClass`)
         `theorem transfer.obligation : transfer.color.requires_paired_sibling = true := …`

  `dregg_effect mint (amount) : Generative`
      ↦  `… .color = .Generative`, `… .regime = .Disclosed`,
         `theorem mint.obligation : mint.color.is_disclosed_non_conservation = true := …`

The `(args)` are documentary surface (the effect's payload fields, e.g. `amount`): an effect's
LINEARITY is a property of its *kind*, independent of payload values (cf. `Spec.Conservation`'s
`linearity : Effect → LinearityClass`, where `transfer 7` and `transfer 9` share a color). So the
args are parsed and recorded as a `List String` (the field names) but do not affect the coloring —
exactly as in the real `Effect::linearity`. Args may be omitted: `dregg_effect setField : Neutral`.

Pure metaprogramming over `Spec.Conservation` + `CatalogEffects`; no `axiom`/`admit`/`native_decide`/`sorry`.
-/
import Dregg2.CatalogEffects
import Dregg2.Tactics      -- for the `#assert_axioms` / `#assert_namespace_axioms` honesty pins

namespace Dregg2.DSLEffect

open Dregg2.Spec Dregg2.Spec.LinearityClass
open Dregg2.CatalogEffects (Regime effectObligation)

/-! ## §1 — The syntax category for a `LinearityClass` color.

A fresh category `dregg_color` names the six `LinearityClass` colors as bare keywords, so an effect
declaration reads in surface English (`: Conservative`) rather than as a qualified term
(`: LinearityClass.Conservative`). Each color keyword elaborates to its exact `LinearityClass`
constructor — the parser-onto-proved-constructors discipline of DSL-A/B. -/

declare_syntax_cat dregg_color

syntax "Conservative" : dregg_color
syntax "Monotonic"    : dregg_color
syntax "Terminal"     : dregg_color
syntax "Generative"   : dregg_color
syntax "Annihilative" : dregg_color
syntax "Neutral"      : dregg_color

/-- Elaborate a `dregg_color` keyword to its exact `LinearityClass` constructor. -/
syntax (name := dreggColorElab) "dregg_color% " dregg_color : term
macro_rules
  | `(dregg_color% Conservative) => `(LinearityClass.Conservative)
  | `(dregg_color% Monotonic)    => `(LinearityClass.Monotonic)
  | `(dregg_color% Terminal)     => `(LinearityClass.Terminal)
  | `(dregg_color% Generative)   => `(LinearityClass.Generative)
  | `(dregg_color% Annihilative) => `(LinearityClass.Annihilative)
  | `(dregg_color% Neutral)      => `(LinearityClass.Neutral)

/-! ## §2 — The conservation OBLIGATION of a color, as a proposition shape.

Every color carries one of three obligations, read straight off `Spec.Conservation`'s PROVED
classifiers (and the `CatalogEffects` per-class theorems). `obligationProp c` is the proposition an
effect of color `c` must satisfy; it is a thin selector over the `Spec` primitives so the generated
`theorem … .obligation` is stated in exactly the `Spec.Conservation` vocabulary:

  * `Conservative`              ⇒ `c.requires_paired_sibling = true`
  * `Generative`/`Annihilative` ⇒ `c.is_disclosed_non_conservation = true`
  * `Monotonic`/`Terminal`/`Neutral` ⇒ `requires_paired_sibling = false ∧ is_disclosed_non_conservation = false`

This is NOT new metatheory: it is the obligation `CatalogEffects.§1` already proves every effect of
that color inherits. The `def` is exhaustive (no default arm) — a new color cannot compile until it
states its obligation. -/

/-- The conservation obligation of a color, AS A PROPOSITION over the proved `Spec.Conservation`
classifiers. Exhaustive `match`, no default arm. -/
def obligationProp : LinearityClass → Prop
  | .Conservative => (LinearityClass.Conservative).requires_paired_sibling = true
  | .Generative   => (LinearityClass.Generative).is_disclosed_non_conservation = true
  | .Annihilative => (LinearityClass.Annihilative).is_disclosed_non_conservation = true
  | .Monotonic    => (LinearityClass.Monotonic).requires_paired_sibling = false ∧
                     (LinearityClass.Monotonic).is_disclosed_non_conservation = false
  | .Terminal     => (LinearityClass.Terminal).requires_paired_sibling = false ∧
                     (LinearityClass.Terminal).is_disclosed_non_conservation = false
  | .Neutral      => (LinearityClass.Neutral).requires_paired_sibling = false ∧
                     (LinearityClass.Neutral).is_disclosed_non_conservation = false

/-- **Every color's obligation HOLDS** — discharged from the `CatalogEffects` per-class theorems
(equivalently, by `rfl`, since the `Spec.Conservation` classifiers compute). This is the single
proved fact the `dregg_effect` command instantiates per declaration: the generated
`theorem … .obligation` is `obligation_holds <color>` specialized. No `sorry`; the obligation is
the one `Spec.Conservation`/`CatalogEffects` already prove. -/
theorem obligation_holds : (c : LinearityClass) → obligationProp c
  | .Conservative => rfl
  | .Generative   => rfl
  | .Annihilative => rfl
  | .Monotonic    => ⟨rfl, rfl⟩
  | .Terminal     => ⟨rfl, rfl⟩
  | .Neutral      => ⟨rfl, rfl⟩

#assert_axioms obligation_holds

/-! ## §3 — The `dregg_effect` declaration command.

`dregg_effect <name> (a, b, …) : <Color>` (the `(args)` optional) elaborates to THREE generated
declarations under `<name>` (the dot-namespaced shape mirrors `CatalogInstances`' per-effect facts):

  * `def  <name>.color  : LinearityClass := <Color>`           — the coloring;
  * `def  <name>.regime : Regime := Regime.ofClass <Color>`     — the `CatalogEffects` discriminator
    regime (`Paired`/`Disclosed`/`Inert`) as DATA;
  * `def  <name>.args   : List String := ["a", "b", …]`         — the documentary payload fields;
  * `theorem <name>.obligation : obligationProp <name>.color := obligation_holds <name>.color` —
    the INHERITED conservation obligation, GENERATED (not hand-written), closed by the proved §2 fact.

The command is a pure `macro` over the proved §1/§2 primitives. Field names in `(args)` are
identifiers, turned into `String` literals (the name-keyed discipline of DSL-A's `dreggField%`). -/

/-- One payload-field name inside the `(args)` list — an identifier, recorded as its `String`. -/
syntax (name := dreggArgName) "dreggArgName% " ident : term
macro_rules
  | `(dreggArgName% $a:ident) => pure (Lean.Syntax.mkStrLit (toString a.getId))

/-- `dregg_effect <name> (a, …)? : <Color>` — declare an effect's color + inherited obligation. The
`(args)` are optional. Generates `<name>.color`, `<name>.regime`, `<name>.args`, and the proved
`<name>.obligation`. -/
syntax (name := dreggEffect)
  "dregg_effect " ident (" (" ident,* ")")? " : " dregg_color : command

macro_rules
  | `(dregg_effect $name:ident $[ ( $args,* ) ]? : $c:dregg_color) => do
      -- The dot-namespaced child names: `<name>.color`, `<name>.regime`, `<name>.args`, `<name>.obligation`.
      let colorName := name.getId ++ `color
      let regimeName := name.getId ++ `regime
      let argsName := name.getId ++ `args
      let oblName := name.getId ++ `obligation
      let colorId := Lean.mkIdent colorName
      let regimeId := Lean.mkIdent regimeName
      let argsId := Lean.mkIdent argsName
      let oblId := Lean.mkIdent oblName
      -- Parse the optional `(args)` into a `List String` syntax of the field names.
      let argStrs : Array (Lean.TSyntax `term) ←
        match args with
        | none => pure #[]
        | some as => as.getElems.mapM (fun a => `(dreggArgName% $a))
      `(/-- The `LinearityClass` coloring of this effect (generated by `dregg_effect`). -/
        def $colorId : LinearityClass := dregg_color% $c
        /-- The `CatalogEffects.Regime` (Paired/Disclosed/Inert) of this effect (generated). -/
        def $regimeId : Regime := Regime.ofClass (dregg_color% $c)
        /-- The documentary payload-field names of this effect (generated). -/
        def $argsId : List String := [ $argStrs,* ]
        /-- **The INHERITED conservation obligation of this effect — GENERATED, proved by the §2
        `obligation_holds` fact (NO hand-written proof, NO `sorry`).** Its statement is the
        `Spec.Conservation` obligation the color demands; its proof is the one already-proved fact. -/
        theorem $oblId : obligationProp $colorId := obligation_holds $colorId)

/-! ## §4 — Worked example: `transfer : Conservative` (PHASE-EDSL DSL-C).

A transfer moves an `amount` of an `asset` between two cells. Its color is `Conservative` — its
per-domain deltas must sum to `0` (a debit matched by an equal credit). The declaration generates
the coloring, the `Paired` regime, and the paired-sibling obligation. -/

dregg_effect transfer (amount, asset, fromCell, toCell) : Conservative

/-- **The declared `transfer` color IS exactly the `CatalogEffects` catalog coloring of the namesake
`transfer` Effect variant — PROVED by `rfl`.** This is the headline of DSL-C: a one-line effect
declaration elaborates to the precise verified `Spec.Conservation` color the dregg1 `Effect::linearity`
catalog assigns, so the proved per-class obligation applies to *this* declaration. -/
theorem transfer_color_eq_catalog :
    transfer.color = Dregg2.CatalogInstances.effectLinearity .transfer := rfl

#assert_axioms transfer_color_eq_catalog

/-- The generated `transfer.regime` is the `Paired` regime (`Regime.ofClass .Conservative`). -/
theorem transfer_regime_eq : transfer.regime = Regime.Paired := rfl

/-- The generated obligation has the expected paired-sibling shape — and it is the `CatalogEffects`
class obligation `conservative_requires_paired` specialized to the catalog `transfer`. -/
example : transfer.color.requires_paired_sibling = true := transfer.obligation

/-- The documentary args are recorded verbatim. -/
example : transfer.args = ["amount", "asset", "fromCell", "toCell"] := rfl

#assert_axioms transfer_regime_eq

/-! ## §5 — Worked example: `mint : Generative` (PHASE-EDSL DSL-C).

A mint creates an `amount` of an `asset` from nothing. Its color is `Generative` — it breaks
`Σδ = 0`, but the broken amount is DISCLOSED (bound into the receipt). The declaration generates the
`Disclosed` regime and the disclosure obligation. -/

dregg_effect mint (amount, asset) : Generative

/-- **The declared `mint` color matches the catalog coloring of the namesake `bridgeMint` Generative
variant — PROVED by `rfl`.** (`mint` is the surface name for the catalog's `bridgeMint`/`createCell`
generative family — all `Generative`.) -/
theorem mint_color_eq_catalog :
    mint.color = Dregg2.CatalogInstances.effectLinearity .bridgeMint := rfl

#assert_axioms mint_color_eq_catalog

/-- The generated `mint.regime` is the `Disclosed` regime (`Regime.ofClass .Generative`). -/
theorem mint_regime_eq : mint.regime = Regime.Disclosed := rfl

/-- The generated obligation is the disclosure obligation — minting legitimately breaks conservation
but FORCES disclosure of the delta into the receipt. -/
example : mint.color.is_disclosed_non_conservation = true := mint.obligation

#assert_axioms mint_regime_eq

/-! ## §6 — Worked example: `burn : Annihilative`, and the three INERT colors.

`burn` destroys a resource — `Annihilative`, the dual of `Generative`: it too breaks `Σδ = 0` and
discloses. The three inert colors (`Monotonic`/`Terminal`/`Neutral`) carry NO conservation delta,
so their generated obligation is the conjunction "neither paired nor disclosed". -/

dregg_effect burn (amount, asset) : Annihilative
dregg_effect incrementNonce : Monotonic
dregg_effect cellDestroy : Terminal
dregg_effect setField (field, value) : Neutral

/-- `burn`'s color matches the catalog `burn` Annihilative variant (by `rfl`); its obligation is
disclosure. -/
theorem burn_color_eq_catalog :
    burn.color = Dregg2.CatalogInstances.effectLinearity .burn := rfl
example : burn.color.is_disclosed_non_conservation = true := burn.obligation
example : burn.regime = Regime.Disclosed := rfl

#assert_axioms burn_color_eq_catalog

/-- An INERT effect (`incrementNonce`, `Monotonic`): its obligation is "neither paired nor
disclosed", and its regime is `Inert`. Matches the catalog `incrementNonce` Monotonic variant. -/
theorem incrementNonce_color_eq_catalog :
    incrementNonce.color = Dregg2.CatalogInstances.effectLinearity .incrementNonce := rfl
example : incrementNonce.color.requires_paired_sibling = false ∧
          incrementNonce.color.is_disclosed_non_conservation = false := incrementNonce.obligation
example : incrementNonce.regime = Regime.Inert := rfl

#assert_axioms incrementNonce_color_eq_catalog

/-- `cellDestroy` is `Terminal` (one-way, no inverse) — inert; matches the catalog variant. -/
theorem cellDestroy_color_eq_catalog :
    cellDestroy.color = Dregg2.CatalogInstances.effectLinearity .cellDestroy := rfl
example : cellDestroy.regime = Regime.Inert := rfl

#assert_axioms cellDestroy_color_eq_catalog

/-- `setField` is `Neutral` (pure book-keeping) — inert; matches the catalog variant. It takes args
yet is uncoloured by them, confirming linearity is a property of the KIND, not the payload. -/
theorem setField_color_eq_catalog :
    setField.color = Dregg2.CatalogInstances.effectLinearity .setField := rfl
example : setField.color.requires_paired_sibling = false ∧
          setField.color.is_disclosed_non_conservation = false := setField.obligation
example : setField.regime = Regime.Inert := rfl

#assert_axioms setField_color_eq_catalog

/-! ## §7 — `effectObligation` coincidence: the generated regime IS the `CatalogEffects`
discriminator at the namesake catalog variant.

`CatalogEffects.effectObligation : EffectKind → Regime` is the proved discriminator (`Regime.ofClass
∘ effectLinearity`). Each declared effect's generated `.regime` coincides with `effectObligation` at
its namesake catalog variant — by `rfl`. This bundles the surface declarations onto the proved
`CatalogEffects` discriminator: the `dregg_effect` parser reproduces exactly the obligation regime
`CatalogEffects` computes. -/

/-- The six declared regimes coincide with the proved `CatalogEffects.effectObligation` at their
namesake catalog variants — the surface→discriminator map, pinned by `rfl`. -/
theorem regimes_coincide_with_catalog :
    transfer.regime        = effectObligation .transfer ∧
    mint.regime            = effectObligation .bridgeMint ∧
    burn.regime            = effectObligation .burn ∧
    incrementNonce.regime  = effectObligation .incrementNonce ∧
    cellDestroy.regime     = effectObligation .cellDestroy ∧
    setField.regime        = effectObligation .setField :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

#assert_axioms regimes_coincide_with_catalog

/-! ## §8 — `#eval` smoke-tests (the colors/regimes evaluate as declared). -/

#eval transfer.regime        -- Paired
#eval mint.regime            -- Disclosed
#eval burn.regime            -- Disclosed
#eval incrementNonce.regime  -- Inert
#eval cellDestroy.regime     -- Inert
#eval setField.regime        -- Inert
#eval setField.args          -- ["field", "value"]

/-! ## §9 — Axiom-hygiene tripwire (the honesty pin over the WHOLE namespace).

Every theorem under `Dregg2.DSLEffect` — including the GENERATED `<name>.obligation` theorems the
`dregg_effect` command emits — must rest only on the three kernel axioms
(`propext`/`Classical.choice`/`Quot.sound`). A `sorryAx` anywhere (a faked `rfl`, a planted `sorry`
in the obligation-generator) trips this. This is the DSL-A/B `#assert_axioms` discipline made
module-wide over the effects-DSL surface: the parser introduces no metatheory and no axiom. -/

#assert_namespace_axioms Dregg2.DSLEffect

end Dregg2.DSLEffect
