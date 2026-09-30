/-
# Finite POAG1 tables — the EVALUATION, out of the crypto archive's build

`FiniteTables.lean` sits in the `Dregg2.FFI` closure (the crypto archive's build root), and
until 2026-08-08 it ran fourteen `native_decide` pins at elaboration — every relay board's
closure and every one of the ninety salvage machines — so a game-fixture regression was a
hard failure of every Rust proving target in the workspace (the compilation-unit coupling
the stale-fixture outage measured).  The STATEMENTS remain in `FiniteTables.lean` as
evaluation-free `check_* : Bool` definitions, beside the closure machinery they are about;
THIS module is where they are RUN.  It is rooted in the `PathOfAngelsGuards` library and
reachable from `Dregg2.FFI` by NOTHING, so:

  * a plain `lake build` still evaluates every pin — no loss of checking;
  * `lake build Dregg2.FFI` (what `dregg-lean-ffi/build.rs` and the seed scripts run) never
    does — a red pin here can no longer take the archive down.

Each theorem keeps the name the in-module `#assert_compiled` census used, so the
fully-qualified names are unchanged.  ⚠ The eight relay statements were `∀ i : Fin 8`; they
are now `(List.finRange 8).all` Bools, which range over the same eight boards.

No construction proof lives in this module's parent: `FiniteTables` builds no
proof-carrying `Config`, so there is no residue and every pin moved.
-/
import Dregg2.Games.PathOfAngels.FiniteTables

namespace Dregg2.Games.PathOfAngels.FiniteTables

set_option autoImplicit false

/-! ## Relay Repair — the whole board family -/

theorem relayTable_closed : check_relayTable_closed = true := by native_decide

theorem relayStates_nodup : check_relayStates_nodup = true := by native_decide

theorem relayRefusalReasons_complete :
    check_relayRefusalReasons_complete = true := by native_decide

theorem relayRefusalReasons_live_per_board :
    check_relayRefusalReasons_live_per_board = true := by native_decide

theorem relayRefusalReasons_family_live :
    check_relayRefusalReasons_family_live = true := by native_decide

theorem relayRefusalReasons_declared :
    check_relayRefusalReasons_declared = true := by native_decide

theorem relayStateIds_unique : check_relayStateIds_unique = true := by native_decide

theorem relayStateCounts_pinned : check_relayStateCounts_pinned = true := by native_decide

/-! ## Salvage Lock — the parametric machine -/

theorem salvage_machine_shape_is_seed_independent :
    check_salvage_machine_shape_is_seed_independent () = true := by native_decide

theorem salvage_parametric_table_is_the_kernel :
    check_salvage_parametric_table_is_the_kernel () = true := by native_decide

theorem salvage_parametric_table_is_well_formed :
    check_salvage_parametric_table_is_well_formed () = true := by native_decide

theorem salvageParametricStates_count :
    check_salvageParametricStates_count () = true := by native_decide

theorem salvageParametricTransitions_count :
    check_salvageParametricTransitions_count () = true := by native_decide

theorem parametric_closure_covers_every_board :
    check_parametric_closure_covers_every_board () = true := by native_decide

#assert_compiled relayTable_closed
#assert_compiled relayStates_nodup
#assert_compiled relayRefusalReasons_complete
#assert_compiled relayRefusalReasons_live_per_board
#assert_compiled relayRefusalReasons_family_live
#assert_compiled relayRefusalReasons_declared
#assert_compiled relayStateIds_unique
#assert_compiled relayStateCounts_pinned
#assert_compiled salvage_machine_shape_is_seed_independent
#assert_compiled salvage_parametric_table_is_the_kernel
#assert_compiled salvage_parametric_table_is_well_formed
#assert_compiled salvageParametricStates_count
#assert_compiled salvageParametricTransitions_count
#assert_compiled parametric_closure_covers_every_board

end Dregg2.Games.PathOfAngels.FiniteTables
