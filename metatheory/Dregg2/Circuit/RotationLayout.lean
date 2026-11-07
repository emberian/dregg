/-
# Dregg2.Circuit.RotationLayout — THE ROTATED COMMITMENT LAYOUT (the one VK epoch's state shape).

The Lean expression of `.docs-history-noclaude/UNIVERSAL-MAP-ROTATION.md` §2.1/§2.4/§2.6 — the flag-day
commitment layout. Written and PROVEN here BEFORE the wire flip (`.docs-history-noclaude/ROTATION-CUTOVER.md`),
⛑ **AND THE FLIP HAPPENED**: post-G4 the live chained commit IS the rotated wide commitment
(`Lightclient/NonOmissionAttack.lean:32-35` — `circuit/src/effect_vm/trace_rotated.rs`,
`B_IROOT = 37`, `state_commit = hash_many [d, iroot]`, and `turn/src/executor/proof_verify.rs:349`
"iroot … absorbed INTO the v9 commitment, which the proof binds"), and this module's
`rotatedCommit` is pinned against the ACTUALLY-PUBLISHED Rust commit by
`Circuit/RotatedCommitDifferential.lean:3-13`. There is no untouched live v1 path left to protect;
what the layout IS:

  * **registers 8 → 16** (§2.1): sixteen NAMED register limbs, direct in the commitment (the one
    state structure that is correctly NOT a map — `.docs-history-noclaude/EPOCH-DESIGN.md` §"Per-structure choices").
    `resolve` is the `FactoryDescriptor.fields` name-declaration semantics: a declared field name
    resolves to a register index, first-match, total on declared names (≤ 16) and injective on
    resolved indices (`resolve_total` / `resolve_inj`) — compilation resolves indices, the
    commitment binds the values (`rotatedCommit_binds_named_field`).
  * **the limb order** (`.docs-history-noclaude/EPOCH-DESIGN.md` §"The commitment layout", reconciled): cells root ·
    the 16 registers · the map roots ADJACENT AND UNIFORM (cap_root, nullifier_root, heap_root —
    the §2.4 `heap_root` limb) · lifecycle · epoch · committed height · the receipt-index root
    **literally LAST**. The index root is last because the NAMED obligations
    (`AttestedQuery.CommitBindsIndex`, `MMR.CommitBindsMMR`) pin the shape
    `commit = hash (limbs ++ [iroot])` — `rotatedCommit_binds_mmr` discharges `CommitBindsMMR`
    **by `rfl`** (the whole point of the layout). EPOCH-DESIGN's prose order placed
    lifecycle/epoch/height after the index root; the obligation's shape wins (dated note there).
  * **the committed-height limb** (§2.6, PI v3): `committed_height_not_prover_chosen` — two PI
    vectors bound to the same commitment agree on the height; the temporal gate's
    prover-chosen-height note closes at the flag-day by THIS pin. `PiV3` declares the v3 tail
    (committed-height column + rateBound/challengeWindow caveat tags) appended after the frozen
    v2 prefix (`V2_BASE_COUNT = 202` — drift-guarded by the Rust twin test
    `pi_v3_offsets_match_lean` in `circuit/src/effect_vm/pi.rs`).
  * **the anti-ghost keystone** (`rotatedCommit_binds`): under the ONE named CR floor, equal
    commits force equal limb structures AND equal receipt logs — tampering ANY limb (a register
    beyond the old 8, the heap root, the height) or ANY log position (truncate/extend/reorder,
    via the MMR root binding) moves the commit. Witnessed executably both polarities (§5).

The four map-root limbs are DERIVED boundary views under the universal-memory restructure
(`Crypto/UniversalMemory.boundary_root_derived`, `Exec/UniversalBridge.cap_leaf_value_codec` /
`index_boundary_mroot_derived`) — derivation changes where they are computed, never what they
commit to; THIS module pins what the commitment absorbs.

Axiom hygiene: `#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; crypto only as the
named `Poseidon2SpongeCR` hypothesis.

⚠ **WHAT DEPLOYMENT TOOK FROM THIS MODULE IS THE SHAPE, NOT THE ROSTER — do not read a column
count off this file.** The `hash (limbs ++ [iroot])` shape and its `CommitBindsMMR` discharge are
the deployed ones (above). The limb ENUMERATION below is the design-stage model and the deployed
geometry has moved past it in three independent ways; the single source for any actual column is
`Emit/RotatedLayout.rotated196` (`Emit/RotatedLayout.lean:153,157`) — see
`RotatedLimbs.toList_length` (§1) for the reconciliation.
-/
import Dregg2.Lightclient.MMR
import Dregg2.Substrate.Heap
import Dregg2.Tactics

namespace Dregg2.Circuit.RotationLayout

open Dregg2.Lightclient.MMR (mroot mroot_binds_or_collides CommitBindsMMR demoLog)
open Dregg2.Substrate.Heap (refSponge)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)

/-! ## §1 — the sixteen named registers (8 → 16, the rotation's widening). -/

/-- The rotated register-file width. 8 was cramped (`REORIENT.md:73`); the rotation is the only
time widening is free — after it, new state kinds are domain tags, never new limbs. -/
abbrev NUM_REGISTERS : Nat := 16

/-- **`RotatedLimbs`** — the commitment payload: every absorbed limb, NAMED. The sixteen
registers `r0..r15` are direct limbs (not a map); the three map roots sit ADJACENT AND UNIFORM
(the universal-map forward-shape: a future collection is a new domain id, never a new limb);
lifecycle/epoch/committedHeight close the scalar context. The receipt-index root is NOT a field
here — it is absorbed LAST from the log itself (`rotatedCommit`), which is what discharges
`CommitBindsMMR` by construction. -/
structure RotatedLimbs where
  cellsRoot : ℤ
  r0 : ℤ
  r1 : ℤ
  r2 : ℤ
  r3 : ℤ
  r4 : ℤ
  r5 : ℤ
  r6 : ℤ
  r7 : ℤ
  r8 : ℤ
  r9 : ℤ
  r10 : ℤ
  r11 : ℤ
  r12 : ℤ
  r13 : ℤ
  r14 : ℤ
  r15 : ℤ
  capRoot : ℤ
  nullifierRoot : ℤ
  heapRoot : ℤ
  lifecycle : ℤ
  epoch : ℤ
  committedHeight : ℤ
deriving Repr, DecidableEq

/-- The register file as a list (declaration order). -/
def RotatedLimbs.regList (s : RotatedLimbs) : List ℤ :=
  [ s.r0, s.r1, s.r2, s.r3, s.r4, s.r5, s.r6, s.r7
  , s.r8, s.r9, s.r10, s.r11, s.r12, s.r13, s.r14, s.r15 ]

/-- The register file as an indexed lookup (the `FactoryDescriptor.fields` resolution target). -/
def RotatedLimbs.reg (s : RotatedLimbs) (i : Fin NUM_REGISTERS) : ℤ :=
  s.regList[i.val]'(by simp [RotatedLimbs.regList])

/-- **The absorbed limb list, in the rotation's canonical order**: cells root · 16 registers ·
map roots adjacent (cap, nullifier, heap) · lifecycle · epoch · committed height. (The
receipt-index root is appended LAST by `rotatedCommit`, completing the layout.) -/
def RotatedLimbs.toList (s : RotatedLimbs) : List ℤ :=
  [ s.cellsRoot
  , s.r0, s.r1, s.r2, s.r3, s.r4, s.r5, s.r6, s.r7
  , s.r8, s.r9, s.r10, s.r11, s.r12, s.r13, s.r14, s.r15
  , s.capRoot, s.nullifierRoot, s.heapRoot
  , s.lifecycle, s.epoch, s.committedHeight ]

/-- 1 cells root + 16 registers + 3 map roots + 3 scalars = 23 limbs (24 with the index root).

⚠ **23 IS THE DESIGN-STAGE ROSTER, NOT A DEPLOYED COLUMN COUNT, and the two are not related by a
single conversion factor** — a reader who needs a number must take it from
`Emit/RotatedLayout.rotated196`, whose `rotatedNumPreLimbs = 187`
(`Emit/RotatedLayout.lean:153,157`). The deployed geometry differs from this list in THREE
independent ways, only the third of which is a semantic-vs-wire widening:

  1. **The register file is `r0..r23`, not `r0..r15`.** `r23` carries the authority residue that no
     named limb holds — permissions / VK / lifecycle-payload / delegate / delegation / program /
     mode / token_id / visibility / commitments / proved_state / side-table roots / fields[8..16] —
     at limb-list index 24 (`RotatedCommitDifferential.lean:18-19`; `rotated196`'s `.authority`
     group has lane0 = 24). So `NUM_REGISTERS = 16` here is a count this file's own
     `resolve` totality is stated against, NOT the deployed register count.
  2. **There are FOUR map roots**, `commitments_root` joining cap/nullifier/heap
     (`rotated196.groups`), beside the perms / vk / fields / revoked / cells groups the same
     enumeration commits.
  3. **Each faithful root is an 8-felt GROUP, not a scalar limb** (lane 0 + seven completion
     columns), and each `fields[slot]` and each 32-byte carrier is a **9-lane NONET** after the
     2026-07-31 fields-nonet and 2026-08-01 key-nonet flag days — one scalar limb here is up to
     nine columns there.

The intermediate object, for orientation: the differential states the published commitment over a
**32**-element scalar limb list `[cells_root, r0..r23, cap_root, nullifier_root, commitments_root,
heap_root, lifecycle, epoch, committed_height]` (`RotatedCommitDifferential.lean:11-13`) — this
roster with (1) and (2) applied. `187` is the COLUMN TILING once (3) is applied on top, plus the
scalars neither list names (`disc`, `mode`) and the perms / vk / revoked groups; `rotated196` is a
complete tiling of `0..186` with no pads, so it is the only count that is checked. -/
theorem RotatedLimbs.toList_length (s : RotatedLimbs) : s.toList.length = 23 := rfl

/-- The limb list binds the structure: equal lists force equal `RotatedLimbs` (positional
peeling — every limb has a fixed position, so nothing can hide). -/
theorem RotatedLimbs.toList_injective {s s' : RotatedLimbs} (h : s.toList = s'.toList) :
    s = s' := by
  cases s; cases s'
  simp only [toList, List.cons.injEq, and_true] at h
  simp only [mk.injEq]
  exact h

/-! ## §2 — the rotated commitment: limbs ++ [iroot], the `CommitBindsMMR` discharge. -/

/-- **`rotatedCommit`** — the rotated per-turn state commitment: ONE sponge over the named limbs
with the receipt-index MMR root absorbed as the LAST element. This is the flag-day shape of
`recStateCommit`; the deployment realizes `hash` as the audited Poseidon2 sponge under the same
CR floor as everything else. -/
def rotatedCommit (hash : List ℤ → ℤ) (s : RotatedLimbs) (L : List ℤ) : ℤ :=
  hash (s.toList ++ [mroot hash L])

/-- **THE ROTATION OBLIGATION, DISCHARGED BY CONSTRUCTION.** `CommitBindsMMR` (the
`CommitBindsIndex` limb obligation verbatim, `iroot := mroot` — `Lightclient/MMR.lean` §6,
`Lightclient/AttestedQuery.lean` §5) holds for `rotatedCommit` by `rfl`: the commitment IS a
sponge absorbing the index root as its last limb. Whole-history non-omission
(`light_client_position_non_omission`) now composes with NO leftover hypothesis on the layout. -/
theorem rotatedCommit_binds_mmr (hash : List ℤ → ℤ) (s : RotatedLimbs) (L : List ℤ) :
    CommitBindsMMR hash s.toList (rotatedCommit hash s L) L := rfl

/-- **THE ANTI-GHOST KEYSTONE** — the rotated commitment binds EVERYTHING it absorbs: under the
ONE named CR floor, equal commits force equal limb structures AND equal receipt logs. Tampering
any register (including the widened `r8..r15`), any map root, the height, or any log position
(tamper / truncate / extend / REORDER — `MMR.mroot_binds_or_collides`) moves the commit.

⚠ STILL A FLOOR CARRIER, and named as one: the OUTER sponge peel (`hCR _ _ h`, splitting
`s.toList ++ [mroot hash L]`) is this file's own use of the refuted hypothesis and is untouched by the
MMR port. The MMR leg no longer needs it — the log binding now flows through the unconditional
`mroot_binds_or_collides`, with `hCR` discharging its named residual inline — so what remains here is
exactly one obligation, the rotated-limb split, for the rotation cone to port. -/
theorem rotatedCommit_binds (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    {s s' : RotatedLimbs} {L L' : List ℤ}
    (h : rotatedCommit hash s L = rotatedCommit hash s' L') : s = s' ∧ L = L' := by
  have hl := hCR _ _ h
  have hsplit := List.append_inj hl
    (by rw [RotatedLimbs.toList_length, RotatedLimbs.toList_length])
  refine ⟨RotatedLimbs.toList_injective hsplit.1,
    (mroot_binds_or_collides hash (L₁ := L) (L₂ := L') ?_).resolve_right
      (fun hc => hc.1 (hCR _ _ hc.2))⟩
  have h2 := hsplit.2
  simp only [List.cons.injEq, and_true] at h2
  exact h2

/-- The `heap_root` limb tooth (§2.4): equal commits force equal heap roots — the heap state
that entered `RecordKernelState` this session is COMMITTED, not carried out-of-band. -/
theorem rotatedCommit_binds_heapRoot (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    {s s' : RotatedLimbs} {L L' : List ℤ}
    (h : rotatedCommit hash s L = rotatedCommit hash s' L') : s.heapRoot = s'.heapRoot :=
  congrArg RotatedLimbs.heapRoot (rotatedCommit_binds hash hCR h).1

/-- The widened-register tooth: EVERY register limb — including the new upper eight — is bound.
(The pre-rotation layout had no carrier for `r8..r15` at all; here a tamper is refused.) -/
theorem rotatedCommit_binds_reg (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    {s s' : RotatedLimbs} {L L' : List ℤ}
    (h : rotatedCommit hash s L = rotatedCommit hash s' L') (i : Fin NUM_REGISTERS) :
    s.reg i = s'.reg i :=
  congrArg (fun t => RotatedLimbs.reg t i) (rotatedCommit_binds hash hCR h).1

/-- The log tooth: equal commits force EQUAL receipt logs — `server_cannot_omit`'s root face,
welded into the per-turn commitment (non-omission discharges by construction at the flag-day). -/
theorem rotatedCommit_binds_log (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    {s s' : RotatedLimbs} {L L' : List ℤ}
    (h : rotatedCommit hash s L = rotatedCommit hash s' L') : L = L' :=
  (rotatedCommit_binds hash hCR h).2

#assert_axioms rotatedCommit_binds_mmr
#assert_axioms rotatedCommit_binds
#assert_axioms rotatedCommit_binds_heapRoot
#assert_axioms rotatedCommit_binds_reg
#assert_axioms rotatedCommit_binds_log

/-! ## §3 — `FactoryDescriptor.fields`: declared names resolve to register indices.

The rotation gives `FactoryDescriptor` a `fields` name declaration (`REORIENT.md:73`); the
SEMANTICS is first-match resolution into the 16-register file. `resolveFrom` is the recursion;
`resolve` clips to `Fin 16`. Total on declared names when ≤ 16 are declared; injective on
resolved indices WITHOUT any nodup hypothesis (first-match is injective by construction). The
Rust twin is `FactoryDescriptor::resolve_field` (`cell/src/factory.rs`). -/

/-- First-match name resolution, counting from `i`. -/
def resolveFrom : List String → String → Nat → Option Nat
  | [], _, _ => none
  | x :: xs, n, i => if x = n then some i else resolveFrom xs n (i + 1)

theorem resolveFrom_ge : ∀ {names : List String} {n : String} {i j : Nat},
    resolveFrom names n i = some j → i ≤ j := by
  intro names
  induction names with
  | nil => intro n i j h; simp [resolveFrom] at h
  | cons x xs ih =>
    intro n i j h
    by_cases hx : x = n
    · simp only [resolveFrom, if_pos hx, Option.some.injEq] at h
      omega
    · simp only [resolveFrom, if_neg hx] at h
      have := ih h
      omega

theorem resolveFrom_lt : ∀ {names : List String} {n : String} {i j : Nat},
    resolveFrom names n i = some j → j < i + names.length := by
  intro names
  induction names with
  | nil => intro n i j h; simp [resolveFrom] at h
  | cons x xs ih =>
    intro n i j h
    by_cases hx : x = n
    · simp only [resolveFrom, if_pos hx, Option.some.injEq] at h
      simp only [List.length_cons]
      omega
    · simp only [resolveFrom, if_neg hx] at h
      have := ih h
      simp only [List.length_cons]
      omega

theorem resolveFrom_isSome_of_mem : ∀ {names : List String} {n : String} {i : Nat},
    n ∈ names → (resolveFrom names n i).isSome := by
  intro names
  induction names with
  | nil => intro n i h; simp at h
  | cons x xs ih =>
    intro n i h
    by_cases hx : x = n
    · simp [resolveFrom, if_pos hx]
    · rcases List.mem_cons.mp h with rfl | hmem
      · exact absurd rfl hx
      · simpa [resolveFrom, if_neg hx] using ih hmem

/-- First-match resolution is injective on resolved indices — no nodup needed: two names
resolving to the SAME index must both be the first match there, hence equal. -/
theorem resolveFrom_inj : ∀ {names : List String} {n m : String} {i j : Nat},
    resolveFrom names n i = some j → resolveFrom names m i = some j → n = m := by
  intro names
  induction names with
  | nil => intro n m i j h _; simp [resolveFrom] at h
  | cons x xs ih =>
    intro n m i j hn hm
    by_cases hxn : x = n
    · by_cases hxm : x = m
      · rw [← hxn, hxm]
      · simp only [resolveFrom, if_pos hxn, Option.some.injEq] at hn
        simp only [resolveFrom, if_neg hxm] at hm
        have := resolveFrom_ge hm
        omega
    · by_cases hxm : x = m
      · simp only [resolveFrom, if_pos hxm, Option.some.injEq] at hm
        simp only [resolveFrom, if_neg hxn] at hn
        have := resolveFrom_ge hn
        omega
      · simp only [resolveFrom, if_neg hxn] at hn
        simp only [resolveFrom, if_neg hxm] at hm
        exact ih hn hm

/-- **`resolve`** — the `FactoryDescriptor.fields` semantics: a declared field name resolves to
a register index in the 16-wide file (first match; `none` if undeclared or out of range). -/
def resolve (names : List String) (n : String) : Option (Fin NUM_REGISTERS) :=
  (resolveFrom names n 0).bind fun j =>
    if hj : j < NUM_REGISTERS then some ⟨j, hj⟩ else none

/-- **Resolution is total on declared names** when the declaration fits the file (≤ 16 names):
compilation never fails to place a declared field. -/
theorem resolve_total {names : List String} {n : String}
    (hlen : names.length ≤ NUM_REGISTERS) (hmem : n ∈ names) :
    (resolve names n).isSome := by
  obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp (resolveFrom_isSome_of_mem (i := 0) hmem)
  have hlt : j < NUM_REGISTERS := by
    have := resolveFrom_lt hj
    omega
  simp [resolve, hj, hlt]

/-- **Resolution is injective**: two declared names landing on the same register are the same
name — a factory's field declaration never aliases two fields onto one register. -/
theorem resolve_inj {names : List String} {n m : String} {k : Fin NUM_REGISTERS}
    (hn : resolve names n = some k) (hm : resolve names m = some k) : n = m := by
  unfold resolve at hn hm
  cases hjn : resolveFrom names n 0 with
  | none => rw [hjn] at hn; simp at hn
  | some j =>
    rw [hjn] at hn
    cases hjm : resolveFrom names m 0 with
    | none => rw [hjm] at hm; simp at hm
    | some j' =>
      rw [hjm] at hm
      simp only [Option.bind_some] at hn hm
      split at hn
      · split at hm
        · have hj : j = k.val := by
            have := Option.some.inj hn; exact congrArg Fin.val this
          have hj' : j' = k.val := by
            have := Option.some.inj hm; exact congrArg Fin.val this
          rw [hj', ← hj] at hjm
          exact resolveFrom_inj hjn hjm
        · exact absurd hm (by simp)
      · exact absurd hn (by simp)

/-- **The named-field weld**: a declared field name resolves to a register whose VALUE the
rotated commitment binds — `FactoryDescriptor.fields` declarations are commitment-carried, not
metadata. (The composition `resolve` ∘ `rotatedCommit_binds_reg`.) -/
theorem rotatedCommit_binds_named_field (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    {s s' : RotatedLimbs} {L L' : List ℤ} {names : List String} {n : String}
    {i : Fin NUM_REGISTERS}
    (_hres : resolve names n = some i)
    (h : rotatedCommit hash s L = rotatedCommit hash s' L') :
    s.reg i = s'.reg i :=
  rotatedCommit_binds_reg hash hCR h i

#assert_axioms resolve_total
#assert_axioms resolve_inj
#assert_axioms rotatedCommit_binds_named_field

/-! ## §4 — PI v3: the staged public-input tail (committed height + caveat tags).

The v3 tail appends FOUR slots after the frozen v2 prefix (`pi.rs` `BASE_COUNT = 202` — the
Rust drift-guard test `pi_v3_offsets_match_lean` pins these numbers against this module, so a
v2-prefix drift fails loudly before the flag-day):

  * `COMMITTED_HEIGHT` — the height the commitment carries (the `committedHeight` limb's PI
    face). Closes the temporal gate's prover-chosen-height note: the verifier reads the height
    FROM the committed state, never from a prover-chosen scalar. ⚑ This bullet used to end
    "(`CURRENT_BLOCK_HEIGHT`, PI 18, stays as the verifier-supplied comparand)" — wrong twice
    over: the slot was PI 26 post-Phase-C, and NO code ever performed the comparison that would
    have made it a comparand. It was DELETED on 2026-08-07 with the other six dead v1 slots
    (`docs/PI-DISPOSITION.md` §6). THIS column is the whole temporal binding.
  * `RATE_BOUND_TAG` / `CHALLENGE_WINDOW_TAG` — the caveat tags (`REORIENT.md:75-76`); the
    challengeWindow tag is what the optimistic proving mode reads (#169) — the tag ships at the
    flag-day, the mode ships later. -/

namespace PiV3

/-- The frozen v2 PI prefix length (`circuit/src/effect_vm/pi.rs` `BASE_COUNT`). Drift-guarded
by the Rust twin test — if the live layout grows before the flag-day, the pin fails there.

Phase C (`.docs-history-noclaude/FAITHFUL-STATE-COMMITMENT.md`): re-anchored 201 → 209 when the
OLD/NEW state commitment widened 4 → 8 felts each (+8 prefix shift) to lift the
collision floor ~62 → ~124 bits, matching FRI ~128-bit soundness.

⚑ THE SEVEN-SLOT COMPACTION (2026-08-07, `docs/PI-DISPOSITION.md` §6): re-anchored 209 → 202
when `CURRENT_BLOCK_HEIGHT` / `MAX_CUSTOM_EFFECTS` / `CUSTOM_EFFECT_COUNT` /
`APPROVED_HANDOFFS[4]` (v1 offsets 26..32) were DELETED — 0 `pi_binding`s across both deployed
registries, no verifier comparison, and the one off-circuit reader now derives its count from
the PI vector's own length. -/
def V2_BASE_COUNT : Nat := 202

/-- The committed-height PI column: the `committedHeight` limb's public face. -/
def COMMITTED_HEIGHT : Nat := V2_BASE_COUNT

/-- The rateBound caveat tag column. -/
def RATE_BOUND_TAG : Nat := V2_BASE_COUNT + 1

/-- The challengeWindow caveat tag column (what the optimistic proving mode reads — #169). -/
def CHALLENGE_WINDOW_TAG : Nat := V2_BASE_COUNT + 2

/-- The per-cell ASSET CLASS column (light-client conservation soundness). The asset /
issuer-cell class (dregg3: AssetId := issuer-cell), a single field element folding the cell's
committed `token_id`, surfaced to the PI and pinned (row-0 boundary) to the trace's committed
class. The per-asset cross-cell conservation gate partitions each per-cell proof's NET_DELTA by
THIS PI-bound class, so a ledgerless light client enforces per-asset Σδ=0 WITHOUT a ledger
lookup. Appended as the 4th v3 slot. -/
def ASSET_CLASS : Nat := V2_BASE_COUNT + 3

/-- The v3 base count: the v2 prefix + the four new slots. -/
def V3_BASE_COUNT : Nat := V2_BASE_COUNT + 4

/-- The four v3 slots are fresh (≥ the v2 prefix) and pairwise distinct. -/
theorem v3_slots_fresh_and_distinct :
    V2_BASE_COUNT ≤ COMMITTED_HEIGHT ∧ COMMITTED_HEIGHT < RATE_BOUND_TAG
      ∧ RATE_BOUND_TAG < CHALLENGE_WINDOW_TAG ∧ CHALLENGE_WINDOW_TAG < ASSET_CLASS
      ∧ ASSET_CLASS < V3_BASE_COUNT := by
  decide

/-- A PI vector carries the committed height: the v3 column EQUALS the commitment's
`committedHeight` limb (the binding the flag-day assembly enforces per descriptor). -/
def BindsCommittedHeight (pi : Nat → ℤ) (s : RotatedLimbs) : Prop :=
  pi COMMITTED_HEIGHT = s.committedHeight

/-- **The prover-chosen-height note CLOSES**: two PI vectors bound (via `BindsCommittedHeight`)
to the SAME rotated commitment agree on the committed height — under the CR floor the height is
a function of the commitment, not a prover choice. -/
theorem committed_height_not_prover_chosen (hash : List ℤ → ℤ)
    (hCR : Poseidon2SpongeCR hash)
    {pi pi' : Nat → ℤ} {s s' : RotatedLimbs} {L L' : List ℤ}
    (hb : BindsCommittedHeight pi s) (hb' : BindsCommittedHeight pi' s')
    (hc : rotatedCommit hash s L = rotatedCommit hash s' L') :
    pi COMMITTED_HEIGHT = pi' COMMITTED_HEIGHT := by
  rw [hb, hb', congrArg RotatedLimbs.committedHeight (rotatedCommit_binds hash hCR hc).1]

#assert_axioms committed_height_not_prover_chosen

end PiV3

/-! ## §5 — NON-VACUITY: both polarities, executable, on the Horner toy sponge.

`refSponge` (`Substrate/Heap.lean` §3 — computable, NOT crypto; deployment = the audited p3
Poseidon2 behind the same CR-floor hypothesis) + `demoLog` (`Lightclient/MMR.lean` §7). The
discharge is definitional (an `example` by `rfl`); every tamper class moves the commit. -/

/-- A concrete rotated payload: all 23 limbs distinct, registers `100+i`. -/
def demoLimbs : RotatedLimbs :=
  { cellsRoot := 1
  , r0 := 100, r1 := 101, r2 := 102, r3 := 103
  , r4 := 104, r5 := 105, r6 := 106, r7 := 107
  , r8 := 108, r9 := 109, r10 := 110, r11 := 111
  , r12 := 112, r13 := 113, r14 := 114, r15 := 115
  , capRoot := 7, nullifierRoot := 8, heapRoot := 9
  , lifecycle := 0, epoch := 3, committedHeight := 42 }

/-- The `CommitBindsMMR` discharge is DEFINITIONAL on the concrete payload. -/
example : CommitBindsMMR refSponge demoLimbs.toList
    (rotatedCommit refSponge demoLimbs demoLog) demoLog := rfl

-- ANTI-GHOST, executable: tampering the heap_root limb moves the commit...
#guard rotatedCommit refSponge demoLimbs demoLog
  != rotatedCommit refSponge { demoLimbs with heapRoot := 99 } demoLog
-- ...tampering a WIDENED register (r15 — no pre-rotation carrier existed) moves it...
#guard rotatedCommit refSponge demoLimbs demoLog
  != rotatedCommit refSponge { demoLimbs with r15 := 999 } demoLog
-- ...tampering the committed height moves it (the temporal pin)...
#guard rotatedCommit refSponge demoLimbs demoLog
  != rotatedCommit refSponge { demoLimbs with committedHeight := 43 } demoLog
-- ...and the cap/nullifier roots (adjacent-uniform map limbs) each move it.
#guard rotatedCommit refSponge demoLimbs demoLog
  != rotatedCommit refSponge { demoLimbs with capRoot := 99 } demoLog
#guard rotatedCommit refSponge demoLimbs demoLog
  != rotatedCommit refSponge { demoLimbs with nullifierRoot := 99 } demoLog
-- The LOG teeth: truncation, extension, and REORDER each move the commit (the iroot limb).
#guard rotatedCommit refSponge demoLimbs demoLog
  != rotatedCommit refSponge demoLimbs (demoLog.take 2)
#guard rotatedCommit refSponge demoLimbs demoLog
  != rotatedCommit refSponge demoLimbs (demoLog ++ [444])
#guard rotatedCommit refSponge demoLimbs demoLog
  != rotatedCommit refSponge demoLimbs [222, 111, 333]
-- The honest recompute is stable (the positive polarity).
#guard rotatedCommit refSponge demoLimbs demoLog
  == rotatedCommit refSponge demoLimbs [111, 222, 333]

-- Name resolution, executable: totality, first-match, clipping, injectivity witness.
#guard resolve ["balance", "owner", "expiry"] "owner" == some ⟨1, by decide⟩
#guard resolve ["balance", "owner", "expiry"] "ghost" == none
#guard (resolve ((List.range 17).map toString) "16") == none  -- the 17th name does NOT fit
#guard (resolve ((List.range 16).map toString) "15").isSome   -- exactly 16 fit

end Dregg2.Circuit.RotationLayout
