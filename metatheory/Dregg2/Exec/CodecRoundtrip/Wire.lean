import Dregg2.Exec.CodecRoundtrip.Leaves
import Dregg2.Exec.CodecRoundtrip.SideTables
import Dregg2.Exec.CodecRoundtrip.Forest

/-!
Submodule of `Dregg2.Exec.CodecRoundtrip` — split for parallel compilation.
-/

namespace Dregg2.Exec.CodecRoundtrip

open Dregg2.Exec
open Dregg2.Exec.FFI
open Dregg2.Exec.FFI.Wide

/-! ## §14 — the WIDE STATE record (`parseWState`) roundtrip — THE STATE DECODER (the differential's
core). The 11-field `do`-block assembling every side-table proved above: cells (§12), caps (§13),
bal (§10), escrows (§11), nullifiers/commitments/revoked (§9), queues (§11b), swiss (§11c), and the
per-cell-commitment side-tables lifecycle/deathCert (§10b). Strict on field ORDER + the closing `}`.
Carries one `Wf` hypothesis (`WfCells w.cells`, the §1 value boundary on the cell payloads); every other
field is a total-codec side-table. Fuel-adequate whenever the outer fuel exceeds the encoded width (the
`parseWWire` caller passes the whole-input length). -/

/-- `some a >>= f = f a` by `rfl` — a PURE rewrite (no `whnf` on the bind scrutinee), so cascading it
with `lit_append` reduces a long `do`-chain by repeated beta rather than by `match`-reduction on the
whole term. Keeps the 11-field `parseWState` decode well under the heartbeat budget. -/
private theorem some_bind {α β : Type} (a : α) (f : α → Option β) : (some a) >>= f = f a := rfl

set_option maxHeartbeats 2000000 in
/-- **FILL J production (the STATE DECODER): the WIDE STATE record roundtrip**
(`parseWState ∘ encodeWState = id`) — the post-state object the differential re-decodes. Composes the
eleven side-table roundtrips through the `do`-block: each `lit ",\"field\":"` is a clean literal consume;
each field arm is its proved leaf; the cells loop's outer fuel is met by the width hypothesis. This
removes the STATE codec — the heart of the wholesale-swap differential — from the Lean-side TCB. -/
theorem parseWState_encode (w : WState) (rest : PState) (hwf : WfCells w.cells) (fuel : Nat)
    (hf : ((encodeWState w).toList ++ rest).length ≤ fuel) :
    parseWState fuel ((encodeWState w).toList ++ rest) = some (w, rest) := by
  obtain ⟨cells, caps, bal, escrows, nullifiers, commitments, queues, swiss, revoked, lifecycle, deathCert⟩ := w
  unfold parseWState
  -- unfold `encodeWState` in BOTH `hf` and the goal (so the width hypothesis expands to the SAME
  -- field-length sum the per-field fuel obligations reference; `unfold` alone misses `hf`).
  -- v4.35: `simp only [encodeWState]` runs past the heartbeat budget in `whnf` (the string-literal
  -- appends); unfolding first and then simplifying the `toList` is instant.
  unfold encodeWState at hf ⊢
  simp only [String.toList_append, List.append_assoc] at hf ⊢
  -- open `{"cells":`, then the cells store (the ONLY fuel-dependent leaf; outer fuel ≥ width).
  rw [lit_append, some_bind, parseCellsW_encode cells _ hwf fuel (by
    -- the cells-leaf width is `hf`'s sum MINUS the leading `{"cells":` literal, so it follows by
    -- `G ≤ k + G ≤ fuel` — a pure `Nat.le_add_left`/`le_trans` (NO `omega`: omega would try to
    -- whnf-evaluate the ~11 concrete `,"field":` string literals' `.toList.length`, which blows the
    -- heartbeat budget on the 11-field sum).
    simp only [List.length_append] at hf ⊢
    exact Nat.le_trans (Nat.le_add_left _ _) hf)]
  -- the remaining 10 fields are each an unconditional `,"field":` literal + its proved total-codec
  -- leaf; cascade `lit_append` (each literal → `some tail`) with `some_bind` (the PURE `some _ >>= f`
  -- beta — no `whnf` on the whole chain) and every leaf in ONE simp fixpoint. The reconstructed
  -- record is the destructured `w` definitionally, so the final `some (·, rest)` closes by `rfl`.
  simp only [some_bind, lit_append,
    parseCapsEntries_encode, parseBal_encode, parseEscrows_encode, parseNats_encode,
    parseQueues_encode, parseSwissTable_encode, parseCellNats_encode]

/-! ## §16 — the complete-turn ENVELOPE (`parseWTurn`/`parseWWire`) roundtrip — the OUTER WIRE
(the last FILL-J leaf). The Turn envelope `{"agent":N,"nonce":N,"fee":Z,"valid_until":N,"prev":"H64",
"root":NODE}` carries the dregg1 outer fields (`parseNat`/`parseInt`/`parseHex32` leaves, §0) wrapping the
recursive action-tree root (§15 `parseForestW_roundtrip`); the wire `{"state":STATEW,"turn":TURNW}` then
composes the §14 wide-state decoder with this envelope, requiring the WHOLE input consumed (`lit "}"` must
yield `some []` — fail-closed on trailing bytes). This removes the OUTERMOST codec layer — the envelope the
wholesale swap actually hands the C entry point — from the Lean-side TCB.

### §16a — the structural-fuel ADEQUACY bridge: `forestSize f ≤ (encodeForestW f).length`. The envelope
parser funds the tree recursion with `cs.length + 1` (the whole-input length); since the encoded tree is a
SUBSTRING of the input, this bound dominates `forestSize`. The bound itself: every `+1`/`+2` charge in the
size measure is paid by ≥1 literal byte the encoder emits (the credential by its `{…}` body, each edge by
its `{"holder":…}` body). Mutual over auth / auth-list / auth-tail / forest / children. -/
/-! ### §16b — the Turn ENVELOPE roundtrip (a fixed-field `do`-block; the tree via §15). -/

/-- Well-formed Turn: the `prev` digest fits the `[u8;32]` width (`< 2^256`, else `parseHex32` wraps) and
the root tree is well-formed (§15a). The `agent`/`nonce`/`valid_until` are `Nat`, `fee` an `Int` — total. -/
def WfTurn (t : WTurn) : Prop := t.prevHash < 2 ^ 256 ∧ WfForest t.root

set_option maxHeartbeats 1000000 in
/-- **FILL J production (the ENVELOPE): the Turn-envelope roundtrip** (`parseWTurn ∘ encodeWTurn = id`).
The dregg1 outer fields (`agent`/`nonce`/`fee`/`valid_until`/`prev`) walk their `parseNat`/`parseInt`/
`parseHex32` leaves (§0), the `prev` digest losslessly under the `< 2^256` boundary, then the action-tree
root via §15's `parseForestW_roundtrip` (fuel `≥ forestSize root`). Strict on field ORDER + the closing
`}`. The wire-envelope decoder the wholesale swap hands the C entry point — out of the Lean TCB. -/
theorem parseWTurn_encode (t : WTurn) (rest : PState) (hwf : WfTurn t) (fuel : Nat)
    (hfuel : forestSize t.root ≤ fuel) (hblock : t.blockHeight = 0) :
    parseWTurn fuel ((encodeWTurn t).toList ++ rest) = some (t, rest) := by
  obtain ⟨agent, nonce, fee, validUntil, blockHeight, prevHash, root⟩ := t
  have hblock' : blockHeight = 0 := hblock
  obtain ⟨hprev, hroot⟩ : prevHash < 2 ^ 256 ∧ WfForest root := hwf
  unfold parseWTurn
  -- rebracket the `++` chain into the right-associated field sequence the parser steps consume.
  rw [show (encodeWTurn ⟨agent, nonce, fee, validUntil, blockHeight, prevHash, root⟩).toList ++ rest
        = ("{\"agent\":":String).toList ++ ((toString agent).toList
            ++ ((",\"nonce\":":String).toList ++ ((toString nonce).toList
            ++ ((",\"fee\":":String).toList ++ ((toString fee).toList
            ++ ((",\"valid_until\":":String).toList ++ ((toString validUntil).toList
            ++ ((",\"prev\":\"":String).toList ++ ((toHex32 prevHash).toList
            ++ (("\",\"root\":":String).toList ++ ((encodeForestW root).toList
            ++ ('}' :: rest)))))))))))) from by
        show (encodeWTurn ⟨agent, nonce, fee, validUntil, blockHeight, prevHash, root⟩).toList ++ rest = _
        unfold encodeWTurn
        have hbh : encodeBlockHeightW blockHeight = "" := by
          simp [encodeBlockHeightW, hblock']
        simp only [hbh, String.toList_append, show ("" : String).toList = ([] : List Char) from rfl,
          show ("}":String).toList = ['}'] from by decide,
          show ("\",\"root\":":String).toList = ("\"":String).toList ++ (",\"root\":":String).toList from by decide,
          List.append_assoc, List.cons_append, List.nil_append]]
  rw [lit_append]; simp only [Option.bind_eq_bind, Option.bind]
  rw [parseNat_toString agent _ (Or.inr ⟨',', _, by
        rw [show (",\"nonce\":":String).toList = ',' :: ("\"nonce\":":String).toList from by decide]; rfl, by decide⟩)]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [lit_append]; simp only [Option.bind_eq_bind, Option.bind]
  rw [parseNat_toString nonce _ (Or.inr ⟨',', _, by
        rw [show (",\"fee\":":String).toList = ',' :: ("\"fee\":":String).toList from by decide]; rfl, by decide⟩)]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [lit_append]; simp only [Option.bind_eq_bind, Option.bind]
  rw [parseInt_toString fee _ (Or.inr ⟨',', _, by
        rw [show (",\"valid_until\":":String).toList = ',' :: ("\"valid_until\":":String).toList from by decide]; rfl, by decide⟩)]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [lit_append]; simp only [Option.bind_eq_bind, Option.bind]
  rw [parseNat_toString validUntil _ (Or.inr ⟨',', _, by
        rw [show (",\"prev\":\"":String).toList = ',' :: ("\"prev\":\"":String).toList from by decide]; rfl, by decide⟩)]
  simp only [Option.bind_eq_bind, Option.bind]
  have hskip : parseBlockHeightW ((",\"prev\":\"":String).toList ++ ((toHex32 prevHash).toList
            ++ (("\",\"root\":":String).toList ++ ((encodeForestW root).toList
            ++ ('}' :: rest))))) = some (0, (",\"prev\":\"":String).toList ++ ((toHex32 prevHash).toList
            ++ (("\",\"root\":":String).toList ++ ((encodeForestW root).toList
            ++ ('}' :: rest))))) := by
    have hnone : litGo (",\"block_height\":":String).toList
        ((",\"prev\":\"":String).toList ++ ((toHex32 prevHash).toList
          ++ (("\",\"root\":":String).toList ++ ((encodeForestW root).toList ++ ('}' :: rest))))) = none := by
      set tail := ((toHex32 prevHash).toList
        ++ (("\",\"root\":":String).toList ++ ((encodeForestW root).toList ++ ('}' :: rest)))) with htail
      rw [show (",\"block_height\":":String).toList =
            ',' :: '"' :: 'b' :: 'l' :: 'o' :: 'c' :: 'k' :: '_' :: 'h' :: 'e' :: 'i' :: 'g' :: 'h' :: 't' :: '"' :: ':' :: []
          from by decide,
          show (",\"prev\":\"":String).toList =
            ',' :: '"' :: 'p' :: 'r' :: 'e' :: 'v' :: '"' :: ':' :: '"' :: [] from by decide,
          htail, List.cons_append]
      rw [@litGo_cons_match ',']
      rw [show (['"', 'p', 'r', 'e', 'v', '"', ':', '"'] : List Char) ++ tail =
            '"' :: 'p' :: 'r' :: 'e' :: 'v' :: '"' :: ':' :: '"' :: tail from by simp [List.cons_append]]
      rw [@litGo_cons_match '"']
      rw [show (['b', 'l', 'o', 'c', 'k', '_', 'h', 'e', 'i', 'g', 'h', 't', '"', ':'] : List Char) =
            'b' :: 'l' :: 'o' :: 'c' :: 'k' :: '_' :: 'h' :: 'e' :: 'i' :: 'g' :: 'h' :: 't' :: '"' :: ':' :: [] from rfl]
      exact litGo_ne_head 'b' _ 'p' _ (by decide)
    have hlit : lit ",\"block_height\":" ((",\"prev\":\"":String).toList ++ ((toHex32 prevHash).toList
          ++ (("\",\"root\":":String).toList ++ ((encodeForestW root).toList ++ ('}' :: rest))))) = none := by
      dsimp only [lit]; exact hnone
    dsimp only [parseBlockHeightW]
    rw [hlit]
  rw [hskip]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [lit_append]; simp only [Option.bind_eq_bind, Option.bind]
  rw [parseHex32_toHex32 prevHash _, Nat.mod_eq_of_lt hprev]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [lit_append]; simp only [Option.bind_eq_bind, Option.bind]
  rw [parseForestW_roundtrip root _ hroot fuel hfuel]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [show lit "}" ('}' :: rest) = some rest from by
        rw [show ('}' :: rest) = ("}":String).toList ++ rest from rfl, lit_append]]
  simp only [hblock']

/-! ### §16c — the complete-turn WIRE roundtrip (state §14 ∘ envelope §16b; the WHOLE input consumed). -/

/-- The complete-turn wire ENCODER (the inline `{"host":HOST,"state":STATEW,"turn":TURNW}` the C entry
point reads — matching `wideDemoInput`/`execFullForestAuthStep`'s input shape, host-prefixed for the
boundary-P1 bug-1 NODE-fed admission seam). -/
def encodeWWire (w : WWire) : String :=
  "{\"host\":" ++ encodeWHostCtx w.host ++ ",\"state\":" ++ encodeWState w.state
    ++ ",\"turn\":" ++ encodeWTurn w.turn ++ "}"

set_option maxHeartbeats 1000000 in
/-! ### §16b-host — the HOST-CONTEXT roundtrip (`parseWHostCtx ∘ encodeWHostCtx = id`), the
boundary-P1 (bug 1) NODE-fed admission seam prepended to the wire. Five `Nat` fields in a fixed
`do`-block; each `parseNat` is fed a `,`/`}` non-digit follower. -/

/-- **The HOST-CONTEXT roundtrip**: `parseWHostCtx ∘ encodeWHostCtx = id` on any trailing `rest`. -/
theorem parseWHostCtx_encode (hc : WHostCtx) (rest : PState) :
    parseWHostCtx ((encodeWHostCtx hc).toList ++ rest) = some (hc, rest) := by
  obtain ⟨now, blockHeight, frozen, storedHead, budget⟩ := hc
  unfold parseWHostCtx
  -- Rebracket the encoder's `++` chain into the right-associated field sequence the parser consumes,
  -- keeping each `,"field":` literal as one chunk (so `lit_append` consumes it directly).
  rw [show (encodeWHostCtx ⟨now, blockHeight, frozen, storedHead, budget⟩).toList ++ rest
        = ("{\"now\":":String).toList ++ ((toString now).toList
            ++ ((",\"block_height\":":String).toList ++ ((toString blockHeight).toList
            ++ ((",\"frozen\":":String).toList ++ ((encodeNatsW frozen).toList
            ++ ((",\"stored_head\":":String).toList ++ ((toString storedHead).toList
            ++ ((",\"budget\":":String).toList ++ ((toString budget).toList
            ++ ('}' :: rest)))))))))) from by
        show (encodeWHostCtx ⟨now, blockHeight, frozen, storedHead, budget⟩).toList ++ rest = _
        unfold encodeWHostCtx
        simp only [String.toList_append, List.append_assoc,
          show ("}":String).toList = ['}'] from by decide, List.cons_append, List.nil_append]]
  rw [lit_append]; simp only [Option.bind_eq_bind, Option.bind]
  -- now (followed by `,` of ",\"block_height\":")
  rw [parseNat_toString now _ (Or.inr ⟨',', _, by
        rw [show (",\"block_height\":":String).toList = ',' :: ("\"block_height\":":String).toList from by decide]; rfl, by decide⟩)]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [lit_append]; simp only [Option.bind_eq_bind, Option.bind]
  -- block_height (followed by `,` of ",\"frozen\":")
  rw [parseNat_toString blockHeight _ (Or.inr ⟨',', _, by
        rw [show (",\"frozen\":":String).toList = ',' :: ("\"frozen\":":String).toList from by decide]; rfl, by decide⟩)]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [lit_append]; simp only [Option.bind_eq_bind, Option.bind]
  -- frozen (NATSW array)
  rw [parseNatsW_encode frozen _]; simp only [Option.bind_eq_bind, Option.bind]
  rw [lit_append]; simp only [Option.bind_eq_bind, Option.bind]
  -- stored_head (followed by `,` of ",\"budget\":")
  rw [parseNat_toString storedHead _ (Or.inr ⟨',', _, by
        rw [show (",\"budget\":":String).toList = ',' :: ("\"budget\":":String).toList from by decide]; rfl, by decide⟩)]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [lit_append]; simp only [Option.bind_eq_bind, Option.bind]
  -- budget (followed by the closing `}`)
  rw [parseNat_toString budget _ (Or.inr ⟨'}', rest, rfl, by decide⟩)]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [show lit "}" ('}' :: rest) = some rest from by
        rw [show ('}' :: rest) = ("}":String).toList ++ rest from rfl, lit_append]]

/-- **FILL J production (the OUTERMOST WIRE): the complete-turn wire roundtrip**
(`parseWWire ∘ encodeWWire = id`). Composes the §16b-host context decoder, the §14 wide-state decoder
and the §16b envelope, then requires the WHOLE input consumed (`lit "}"` yields `some []` — trailing
bytes fail-closed). The fuel (`input.length + 1`) dominates both the state width and `forestSize root`.
This removes the OUTERMOST codec — the host-fed envelope the wholesale swap hands the C entry — from
the Lean-side TCB; with §14/§15/§16b-host the wire codec is FULLY out. -/
theorem parseWWire_encode (w : WWire) (hcells : WfCells w.state.cells) (hturn : WfTurn w.turn)
    (hblock : w.turn.blockHeight = 0) :
    parseWWire (encodeWWire w) = some w := by
  obtain ⟨host, state, turn⟩ := w
  have hwire : (encodeWWire ⟨host, state, turn⟩).toList
      = ("{\"host\":":String).toList ++ ((encodeWHostCtx host).toList
          ++ ((",\"state\":":String).toList ++ ((encodeWState state).toList
          ++ ((",\"turn\":":String).toList ++ ((encodeWTurn turn).toList ++ "}".toList))))) := by
    show (encodeWWire ⟨host, state, turn⟩).toList = _
    unfold encodeWWire
    simp only [String.toList_append, List.append_assoc]
  unfold parseWWire
  simp only []
  set fuel := (encodeWWire ⟨host, state, turn⟩).toList.length + 1 with hfueldef
  rw [hwire]
  -- {"host": then the host context
  rw [show lit "{\"host\":" (("{\"host\":":String).toList ++ _)
        = some ((encodeWHostCtx host).toList ++ ((",\"state\":":String).toList
            ++ ((encodeWState state).toList ++ ((",\"turn\":":String).toList
            ++ ((encodeWTurn turn).toList ++ "}".toList))))) from lit_append "{\"host\":" _]
  simp only []
  rw [parseWHostCtx_encode host _]
  simp only []
  -- ,"state": then the wide state
  rw [show lit ",\"state\":" ((",\"state\":":String).toList ++ ((encodeWState state).toList
          ++ ((",\"turn\":":String).toList ++ ((encodeWTurn turn).toList ++ "}".toList))))
        = some ((encodeWState state).toList ++ ((",\"turn\":":String).toList
            ++ ((encodeWTurn turn).toList ++ "}".toList))) from lit_append ",\"state\":" _]
  simp only []
  rw [parseWState_encode state (((",\"turn\":":String).toList ++ ((encodeWTurn turn).toList ++ "}".toList)))
        hcells fuel (by
        rw [hfueldef, hwire]
        simp only [List.length_append]
        omega)]
  dsimp only
  rw [show lit ",\"turn\":" ((",\"turn\":":String).toList ++ ((encodeWTurn turn).toList ++ "}".toList))
        = some ((encodeWTurn turn).toList ++ "}".toList) from lit_append ",\"turn\":" _]
  simp only []
  rw [parseWTurn_encode turn "}".toList hturn fuel (by
        have hbridge := forestSize_le_encode turn.root
        rw [hfueldef, hwire]
        have hsub : (encodeForestW turn.root).toList.length ≤ (encodeWTurn turn).toList.length := by
          obtain ⟨agent, nonce, fee, validUntil, blockHeight, prevHash, root⟩ := turn
          show (encodeForestW root).toList.length ≤ (encodeWTurn ⟨agent, nonce, fee, validUntil, blockHeight, prevHash, root⟩).toList.length
          rw [show (encodeWTurn ⟨agent, nonce, fee, validUntil, blockHeight, prevHash, root⟩)
                = "{\"agent\":" ++ toString agent ++ ",\"nonce\":" ++ toString nonce ++ ",\"fee\":" ++ toString fee
                    ++ ",\"valid_until\":" ++ toString validUntil ++ encodeBlockHeightW blockHeight
                    ++ ",\"prev\":\"" ++ toHex32 prevHash ++ "\""
                    ++ ",\"root\":" ++ encodeForestW root ++ "}" from rfl]
          simp only [String.toList_append, List.length_append]
          omega
        simp only [List.length_append]
        omega) hblock]
  dsimp only
  rw [show lit "}" "}".toList = some [] from by
        rw [show ("}":String).toList = ("}":String).toList ++ ([] : PState) from by simp, lit_append]]

/-! ### §16d — NON-VACUITY: a complete wire WITH a delegation edge round-trips (the recursion + the
envelope + every state field are real). -/

/-- A real multi-node turn: the root credential bears a delegation EDGE (`keep`/`cap`/`sub`), so the wire
exercises the §15 children recursion, not just a leaf root; wrapped in a populated wide state — including
NON-EMPTY `lifecycle`/`deathCert` per-cell tables (cell 0 Destroyed `=3` with a death-cert hash), so the
§10b arms are exercised on real data, not their `[]` defaults. -/
private def wireWitness : WWire :=
  { state := { cells := [(0, .record [("balance", .int 100)])], caps := [(9, [.node 0])], bal := [(0, 0, 100)],
               escrows := [], nullifiers := [], commitments := [], queues := [], swiss := [],
               lifecycle := [(0, 3)], deathCert := [(0, 42)] }
    turn  := { agent := 0, nonce := 1, fee := 2, validUntil := 9, prevHash := 7
               root := ⟨ .signature 3 3, [{ tier := 0, cell := 0, asset := 0, min := 1 }],
                         .balanceA { actor := 0, src := 0, dst := 1, amt := 10 } 0,
                         [⟨1, [.read], .node 0, ⟨.unchecked, [], .revoke 0 0, []⟩⟩] ⟩ } }

/-- The witness state's cells are well-formed (the one digest-free `int` balance). -/
private theorem wireWitness_cells_wf : WfCells wireWitness.state.cells := by
  show WfCells [(0, .record [("balance", .int 100)])]
  exact ⟨⟨by decide, trivial, trivial⟩, trivial⟩

/-- The witness turn is well-formed: `prev = 7 < 2^256`, root credential `signature 3 < 2^256`, the one
caveat tier `0 ≤ 3`, every action `simple`/total, and the one delegation edge's sub-tree well-formed. -/
private theorem wireWitness_turn_wf : WfTurn wireWitness.turn := by
  refine ⟨by decide, ?_⟩
  show WfForest ⟨ .signature 3 3, [{ tier := 0, cell := 0, asset := 0, min := 1 }],
                  .balanceA { actor := 0, src := 0, dst := 1, amt := 10 } 0,
                  [⟨1, [.read], .node 0, ⟨.unchecked, [], .revoke 0 0, []⟩⟩] ⟩
  -- the sub-tree's credential is `.unchecked` (`WfAuth = True`), its caveats/action/children all trivial.
  exact ⟨show (3:Nat) < 2^256 by norm_num, ⟨by unfold WfCaveat; decide, trivial⟩, trivial,
    ⟨⟨trivial, trivial, trivial, trivial⟩, trivial⟩⟩

-- The WHOLE wire — populated state + a delegation-bearing tree + NON-EMPTY lifecycle/deathCert tables
-- — round-trips through `parseWWire`:
example : parseWWire (encodeWWire wireWitness) = some wireWitness :=
  parseWWire_encode wireWitness wireWitness_cells_wf wireWitness_turn_wf rfl

-- NON-VACUITY for the §10b leaf: a MULTI-entry per-cell-Nat table (a Sealed cell `1` and a Destroyed
-- cell `3`) round-trips with a trailing `rest` — so `parseCellNats_encode` inverts the
-- `lifecycle`/`deathCert` codec on populated data, not just `[]`.
example : parseCellNats ((encodeCellNats [(0, 1), (7, 3)]).toList ++ "Z".toList)
    = some ([(0, 1), (7, 3)], "Z".toList) :=
  parseCellNats_encode [(0, 1), (7, 3)] "Z".toList

end Dregg2.Exec.CodecRoundtrip
