/-
  Pancake/Sem.lean — a faithful Lean model of Pancake operational semantics,
  restricted to the REGION-primitive construct subset.

  This is the first stone of the compiler-scale pivot (PANCAKE-IN-LEAN-DESIGN.md):
  model Pancake in Lean, prove the emitter, one named faithfulness assumption A1.

  STATUS (2026-11-06): this file is no longer what the ladder's theorems are
  stated against, and A1 is no longer assumed. CakeML's panSem `evaluate` is
  exported mechanically from HOL4 into `PanSem/` (DreggNet p3-bridge), and
  `Pancake/LadderPanSem.lean` states the rungs about that export. This file is
  retained as a PROVED LAYER: `Pancake/PanSemAgree.lean` proves `evaluate_agree`
  (this semantics and the export agree on every SCOPED program), and records as
  theorems the two places where this transcription is not panSem:
   * `assign` to an unbound local continues here; panSem returns `Error`
     (`sem_lean_assign_unscoped_disagrees`; the "vacuous" valid-value check
     below is vacuous for the shape, not for the binding);
   * `writeByteArray` with an unmapped head byte keeps the tail writes here;
     panSem's `write_bytearray` discards them (`sem_lean_write_unmapped_disagrees`;
     unreachable from `ExtCall`).
  The transcription notes below are kept as written; where they say "faithful",
  read "agrees with the export on scoped programs, by theorem".

  EVERY clause below is transcribed CLAUSE-FOR-CLAUSE from the CakeML sources on
  hbox (`~/src/cakeml/pancake/...`) at CakeML `ed31510b3`. Each word / signed /
  endianness / byte choice is annotated with its panSem source. This annotation
  IS the A1 faithfulness audit surface: the model can be wrong while typechecking
  clean, so the discipline is transcription, not invention.

  SOURCES (hbox):
    panLang     : ~/src/cakeml/pancake/panLangScript.sml
    panSem      : ~/src/cakeml/pancake/semantics/panSemScript.sml
    word_cmp    : ~/src/cakeml/compiler/encoders/asm/asmScript.sml:313
    word_op     : ~/src/cakeml/compiler/backend/wordLangScript.sml (word_op_def)
    get_byte    : ~/src/HOL/src/n-bit/byteScript.sml
    byte_align  : ~/src/HOL/src/n-bit/alignmentScript.sml
    read_bytearray : ~/src/cakeml/misc/miscScript.sml:113

  SUBSET SCOPE. The region primitive (Dsl/EmitPancake.emitRegion) uses:
    exp  : Const, Var Local, BaseAddr, Op Add, Op And, Panop Mul,
           Cmp Less [SIGNED], LoadByte, Load One
    prog : Dec, Assign, Store, ExtCall, Seq, If, While, Return, Skip
  The fused-serve stages additionally use the first-order arithmetic/relational
  ops `Op Sub`, `Cmp Equal` (`==`) and `Cmp NotLess` (`<=`), all now modelled
  here (Binop.sub / Cmp.equal / Cmp.notLess) with their word_op_def / word_cmp_def
  clauses. Constructs OUTSIDE this subset (RStruct/NStruct/Load shape≠One/Shift/Call/
  Raise/Break/Continue/ShMem/…) are deliberately NOT modelled — the honest
  emission surface. Values are the `ValWord` fragment only (region emits no
  structs), so `Value := BitVec 64` faithfully represents `Val (Word w)`; every
  `shape_of value` in the subset is `One`, so panSem's shape side-conditions
  (`Dec`, `Return ≤ 32`) are vacuously satisfied and are noted where dropped.

  FAITHFULNESS DELTAS (documented, not hidden):
   * Op is modelled BINARY (`op bop l r`) rather than panLang's `Op binop (exp list)`.
     The emitter emits only arity-2 ops; panSem `word_op Add = FOLDR word_add 0w`
     and `word_op And = FOLDR word_and (¬0w)` specialise at arity 2 to `l+r` and
     `l&&&r` (fold identities: `x+(y+0)=x+y`, `x&&&(y&&&~0)=x&&&y`). This is the
     emitted-arity specialisation, annotated here as the single structural delta.
   * `s.memaddrs`/`memory : α word → α word_lab`: `word_lab` has the single ctor
     `Word` in this CakeML revision, so `memory : Word → Word` is exact; the
     address set is its Bool characteristic function (`Word → Bool`), extensionally
     the panSem `α word set`.
-/

namespace Pancake

/-- The machine word. The region `.pnk` fixes the 64-bit x64 target
(`(4294967295w:word64)` literal, C1 boundsChk_def). -/
abbrev Word := BitVec 64

/-! ## 1. Byte-level substrate (the faithfulness hot-spot)

Transcribed from HOL `byteScript.sml` / `alignmentScript.sml`. These are the
word/endian/byte choices C1 flagged as where "an off-by-a-sign-bit bug would
live". -/

/-- `byte_align w = align (LOG2 (dimindex(:64) DIV 8)) w = align 3 w`
(alignmentScript `byte_align_def`,`align_def`: `align 3` clears the low
`LOG2 8 = 3` address bits). On 64-bit that is masking off the low 3 bits. -/
def byteAlign (w : Word) : Word := w &&& (~~~ (7 : Word))

/-- `byte_index a be = if be then 8*((d-1) - w2n a MOD d) else 8*(w2n a MOD d)`
with `d = dimindex(:64) DIV 8 = 8` (byteScript `byte_index_def`). This is the
ENDIANNESS choice: big-endian counts bytes from the high end. -/
def byteIndex (a : Word) (be : Bool) : Nat :=
  let d := 8
  if be then 8 * ((d - 1) - (a.toNat % d)) else 8 * (a.toNat % d)

/-- `get_byte a w be = w2w (w >>> byte_index a be) : word8` (byteScript
`get_byte_def`). `>>>` is the logical (unsigned) shift `word_lsr`; `w2w` to
word8 is truncation to the low 8 bits (`setWidth 8`). -/
def getByte (a w : Word) (be : Bool) : BitVec 8 :=
  (w >>> (byteIndex a be)).setWidth 8

/-- `word_slice_alt hi lo w = FCP i. lo ≤ i < hi ∧ w ' i` (byteScript
`word_slice_alt_def`): keep bits `[lo,hi)` of `w`, zero elsewhere. -/
def wordSliceAlt (hi lo : Nat) (w : Word) : Word :=
  let low  := (1#64 <<< lo) - 1#64   -- bits [0,lo) set
  let high := (1#64 <<< hi) - 1#64   -- bits [0,hi) set
  w &&& (high &&& (~~~ low))

/-- `set_byte a b w be = word_slice_alt 64 (i+8) w || (w2w b << i) || word_slice_alt i 0 w`
with `i = byte_index a be` (byteScript `set_byte_def`): overwrite the 8 bits at
byte position `i` with `b`, keeping the rest of `w`. -/
def setByte (a : Word) (b : BitVec 8) (w : Word) (be : Bool) : Word :=
  let i := byteIndex a be
  wordSliceAlt 64 (i + 8) w ||| ((b.setWidth 64) <<< i) ||| wordSliceAlt i 0 w

/-! ## 2. Values, memory, FFI oracle, state -/

/-- The `ValWord` fragment of panSem `v` (region emits no structs, so this is
exact). `shape_of` of every such value is `One`. -/
abbrev Value := Word

/-- A terminal FFI event (`ffi$final_event`), kept opaque — region never inspects
its contents; it only propagates as `FinalFFI`. -/
structure FinalEvent where
  tag : String
deriving Repr, DecidableEq

/-- panSem `result` restricted to the ctors the region subset can produce or
propagate. -/
inductive Result
  | error
  | timeout
  | break_
  | continue_
  | return_ (v : Value)
  | finalFFI (outcome : FinalEvent)
deriving Repr, DecidableEq

/-- The result of one `call_FFI` (`ffi$ffi_result`): either terminate the whole
run (`FFI_final`) or return with a new ffi state + the bytes written back into
the array region (`FFI_return`). -/
inductive FFIResult (σ : Type)
  | final (outcome : FinalEvent)
  | ret   (newState : σ) (newBytes : List (BitVec 8))

/-- The FFI oracle = A0 (the pre-existing FFI contract, an EXPLICIT trusted
assumption, NOT a `sorry`). `call ffi name conf array` models
`call_FFI s.ffi (ExtCall name) conf array`. For the region primitive this is the
`load_vec` / `report_vec` driver: the arena-encoding oracle. -/
structure Oracle (σ : Type) where
  call : σ → String → List (BitVec 8) → List (BitVec 8) → FFIResult σ

/-- panSem `('a,'ffi) state`, restricted to the fields the region subset reads.
`locals` is the partial map `varname |-> v` (region uses only `Local`); `memory`
is `α word → α word_lab` (single-ctor `Word`, so `Word → Word`); `memaddrs` is
the address set as its `Bool` characteristic function. `globals/structs/code/
eshapes/sh_memaddrs/top_addr` are unused by the subset and omitted. -/
structure PancakeState (σ : Type) where
  locals   : String → Option Value
  memory   : Word → Word
  memaddrs : Word → Bool
  be       : Bool
  clock    : Nat
  ffi      : σ
  baseAddr : Word

variable {σ : Type}

/-- `mem_load_byte m dm be w` (panSem `mem_load_byte_def`): `case m (byte_align w)
of Word v => if byte_align w IN dm then SOME (get_byte w v be) else NONE`. The
single-ctor `Word v` match is definitional here. -/
def memLoadByte (m : Word → Word) (dm : Word → Bool) (be : Bool) (w : Word) :
    Option (BitVec 8) :=
  if dm (byteAlign w) then some (getByte w (m (byteAlign w)) be) else none

/-- `mem_store a w dm m = if addr IN dm then SOME ((addr =+ w) m) else NONE`
(panSem `mem_store_def`), used by `Store` via `mem_stores`/`flatten` on the
single-word value (`flatten (Val w) = [w]`). -/
def memStoreWord (m : Word → Word) (dm : Word → Bool) (addr w : Word) :
    Option (Word → Word) :=
  if dm addr then some (fun k => if k = addr then w else m k) else none

/-- `mem_store_byte m dm be w b` (panSem `mem_store_byte_def`). -/
def memStoreByte (m : Word → Word) (dm : Word → Bool) (be : Bool)
    (w : Word) (b : BitVec 8) : Option (Word → Word) :=
  if dm (byteAlign w)
  then some (fun k => if k = byteAlign w then setByte w b (m (byteAlign w)) be else m k)
  else none

/-- `read_bytearray a n get_byte` (miscScript `read_bytearray_def`): `a` is the
ADDRESS, `n` the COUNT; reads `n` successive bytes from `a`. -/
def readByteArray (m : Word → Word) (dm : Word → Bool) (be : Bool) :
    Word → Nat → Option (List (BitVec 8))
  | _, 0 => some []
  | a, n + 1 =>
    match memLoadByte m dm be a with
    | none => none
    | some b =>
      match readByteArray m dm be (a + 1) n with
      | none => none
      | some bs => some (b :: bs)

/-- `write_bytearray a bs m dm be` (panSem `write_bytearray_def`): writes the
tail at `a+1` first, then `b` at `a` (a right fold), swallowing out-of-range
stores (`NONE => m`). -/
def writeByteArray (dm : Word → Bool) (be : Bool) :
    Word → List (BitVec 8) → (Word → Word) → (Word → Word)
  | _, [], m => m
  | a, b :: bs, m =>
    let m' := writeByteArray dm be (a + 1) bs m
    match memStoreByte m' dm be a b with
    | some m'' => m''
    | none => m'

/-! ## 3. Expression evaluation `eval : state → exp → Option Value`

Transcribed from panSem `eval_def`. `word_cmp Less` is SIGNED — this is C1's
trap, see §3.1. -/

/-- panLang `binop` subset used by the region (`asm$binop`), plus `sub` for the
fused-serve stages. `Sub` is the one binop panLang admits ONLY at arity 2
(`word_op Sub [w1;w2] = SOME (w1 - w2)`, `word_op_def`), so — unlike `Add`/`And`
— it carries no fold-identity specialisation delta: the model's binary `op .sub`
is exactly the source. -/
inductive Binop | add | and_ | sub
deriving Repr, DecidableEq

/-- panLang `cmp` subset (`asm$cmp`). `less` is `Cmp Less`, which `word_cmp Less
w1 w2 = (w1 < w2)` interprets as the SIGNED `word_lt` (asmScript `word_cmp_def`
:315). This is the P2 §4.2 seam that BITES for the comparison (C1-REPORT §2).
Modelled below with `BitVec.slt`.

`equal`/`notLess` are the two `cmp`s the fused-serve `==`/`<=` parse to
(panPtreeConversion `conv_cmp`): `word_cmp Equal w1 w2 = (w1 = w2)` and
`word_cmp NotLess w1 w2 = ¬(w1 < w2)` [SIGNED] (word_cmp_def). The parser emits
`a == b` as `Cmp Equal a b` and — SWAPPING operands — `a <= b` as
`Cmp NotLess b a` (`conv_cmp`: `LeqT ↦ (NotLess, swap=T)`); the swap is applied
in Lower.lean, so this model just needs the two comparators. -/
inductive Cmp | less | equal | notLess
deriving Repr, DecidableEq

/-- panLang `exp`, the region subset. `op`/`mul`/`cmp` are the arity-2
specialisations (see header delta note). -/
inductive PancakeExp
  | const    (w : Word)                       -- `Const w`
  | var      (name : String)                  -- `Var Local name`
  | base                                      -- `BaseAddr`
  | op       (bop : Binop) (l r : PancakeExp) -- `Op Add/And/Sub [l;r]`
  | mul      (l r : PancakeExp)               -- `Panop Mul [l;r]`
  | cmp      (c : Cmp) (l r : PancakeExp)     -- `Cmp Less/Equal/NotLess l r` (Less/NotLess SIGNED)
  | loadByte (addr : PancakeExp)              -- `LoadByte addr`
  | loadWord (addr : PancakeExp)              -- `Load One addr`
deriving Repr

/-- `word_cmp Less` = HOL `word_lt` = SIGNED comparison. In Lean `BitVec.slt` is
signed-less-than (`BitVec.<` / `<` would be UNSIGNED — the exact bug C1 warns of). -/
@[inline] def signedLt (a b : Word) : Bool := BitVec.slt a b

/-- `eval s e` (panSem `eval_def`), region subset. Total; returns `none` on the
panSem `NONE` cases (type mismatch, out-of-range load). -/
def eval (s : PancakeState σ) : PancakeExp → Option Value
  | .const w => some w                                   -- `eval s (Const w) = SOME (ValWord w)`
  | .var name => s.locals name                           -- `Var Local v = FLOOKUP s.locals v`
  | .base => some s.baseAddr                             -- `BaseAddr = SOME (ValWord s.base_addr)`
  | .op bop l r =>
    match eval s l, eval s r with
    | some a, some b =>
      match bop with
      | .add  => some (a + b)       -- `word_op Add [a;b] = FOLDR word_add 0w = a+b`
      | .and_ => some (a &&& b)     -- `word_op And [a;b] = FOLDR word_and (¬0w) = a&&&b`
      | .sub  => some (a - b)       -- `word_op Sub [a;b] = SOME (a - b)` (word_op_def, arity-2)
    | _, _ => none
  | .mul l r =>
    match eval s l, eval s r with
    | some a, some b => some (a * b)  -- `pan_op Mul [a;b] = SOME (a*b)` (pan_op_def)
    | _, _ => none
  | .cmp .less l r =>
    match eval s l, eval s r with
    -- `Cmp cmp e1 e2 = SOME (ValWord (if word_cmp cmp w1 w2 then 1w else 0w))`
    | some a, some b => some (if signedLt a b then 1 else 0)
    | _, _ => none
  | .cmp .equal l r =>
    match eval s l, eval s r with
    -- `word_cmp Equal w1 w2 = (w1 = w2)` (asmScript `word_cmp_def`)
    | some a, some b => some (if a = b then 1 else 0)
    | _, _ => none
  | .cmp .notLess l r =>
    match eval s l, eval s r with
    -- `word_cmp NotLess w1 w2 = ¬(w1 < w2)` [SIGNED] (asmScript `word_cmp_def`)
    | some a, some b => some (if signedLt a b then 0 else 1)
    | _, _ => none
  | .loadByte addr =>
    match eval s addr with
    -- `LoadByte addr`: mem_load_byte then `w2w` byte→word (zero-extend, setWidth 64)
    | some w =>
      match memLoadByte s.memory s.memaddrs s.be w with
      | some b => some (b.setWidth 64)
      | none => none
    | none => none
  | .loadWord addr =>
    match eval s addr with
    -- `Load One addr = if addr IN dm then SOME (Val (m addr)) else NONE` (mem_load_def, One)
    | some w => if s.memaddrs w then some (s.memory w) else none
    | none => none

/-! ### 3.2 Refinement lemmas for the fused-serve first-order ops

Each characterises `eval` of a newly-modelled op in terms of the underlying Lean
word operation it refines (`-`, word equality, signed `<`). These are the
non-vacuous obligations Lower.lean's totality on `POp.sub`/`eq`/`le` rests on:
whenever both operands evaluate, the op evaluates to exactly the word/bit result
of its `word_op_def`/`word_cmp_def` clause. -/

/-- `eval (Op Sub [l;r]) = SOME (a - b)` when `l ↦ a`, `r ↦ b` (`word_op Sub`). -/
theorem eval_sub (s : PancakeState σ) {l r : PancakeExp} {a b : Word}
    (hl : eval s l = some a) (hr : eval s r = some b) :
    eval s (.op .sub l r) = some (a - b) := by
  simp only [eval, hl, hr]

/-- `eval (Cmp Equal e1 e2) = SOME (if a = b then 1 else 0)` (`word_cmp Equal`). -/
theorem eval_equal (s : PancakeState σ) {l r : PancakeExp} {a b : Word}
    (hl : eval s l = some a) (hr : eval s r = some b) :
    eval s (.cmp .equal l r) = some (if a = b then 1 else 0) := by
  simp only [eval, hl, hr]

/-- `eval (Cmp NotLess e1 e2) = SOME (if a < b then 0 else 1)` [SIGNED `<`], i.e.
the indicator of `¬(a < b)` (`word_cmp NotLess`). Composed with Lower.lean's
operand swap this realises `a <= b`. -/
theorem eval_notLess (s : PancakeState σ) {l r : PancakeExp} {a b : Word}
    (hl : eval s l = some a) (hr : eval s r = some b) :
    eval s (.cmp .notLess l r) = some (if signedLt a b then 0 else 1) := by
  simp only [eval, hl, hr]

/-! ## 4. Program evaluation `evaluate : prog × state → result option × state`

Transcribed from panSem `evaluate_def`. Clocked big-step: `While`/`Call`
decrement the clock, `clock = 0` gives `TimeOut`. Termination is the panSem
lexicographic measure `(clock, sizeOf prog)` — see `termination_by` below.

The `fix_clock` clamp (panSem `fix_clock_def`) is INLINED at each loop/seq
recursive boundary as `min` on the returned clock: this is what makes the
well-founded recursion go through (the clamp bounds the recursive result's clock
UNCONDITIONALLY by `Nat.min_le_left`, exactly as panSem's `fix_clock_IMP_LESS_EQ`
supplies the decrease). -/

/-- panLang `prog`, the region subset. `dec` carries its continuation (panLang
`Dec v sh e prog` scopes over `prog`); a `.pnk` statement LIST lowers to a right
nest of `dec`/`seq` (see Pancake/Lower.lean). -/
inductive PancakeProg
  | skip
  | dec     (v : String) (e : PancakeExp) (cont : PancakeProg)  -- `Dec v One e cont`
  | assign  (v : String) (e : PancakeExp)                       -- `Assign Local v e`
  | store   (dst src : PancakeExp)                              -- `Store dst src`
  | extCall (name : String) (confPtr confLen arrPtr arrLen : PancakeExp) -- `ExtCall …`
  | seq     (c1 c2 : PancakeProg)                               -- `Seq c1 c2`
  | cond    (e : PancakeExp) (c1 c2 : PancakeProg)              -- `If e c1 c2`
  | while_  (e : PancakeExp) (c : PancakeProg)                  -- `While e c`
  | ret     (e : PancakeExp)                                    -- `Return e`
  | storeByte (dst src : PancakeExp)                            -- `StoreByte dst src`
deriving Repr

/-- `FLOOKUP`-style update: `set_var v value s` writes `locals |+ (v,value)`. -/
def setLocal (lc : String → Option Value) (v : String) (val : Value) :
    String → Option Value :=
  fun k => if k = v then some val else lc k

/-- `res_var lc (v, old)` (panSem `res_var_def`): `old = NONE` deletes, `old =
SOME x` restores — both captured by writing the `Option` back at `v`. -/
def resVar (lc : String → Option Value) (v : String) (old : Option Value) :
    String → Option Value :=
  fun k => if k = v then old else lc k

/-- `empty_locals s` (panSem `empty_locals_def`). -/
def emptyLocals (s : PancakeState σ) : PancakeState σ :=
  { s with locals := fun _ => none }

/-- `dec_clock s` (panSem `dec_clock_def`). -/
def decClock (s : PancakeState σ) : PancakeState σ :=
  { s with clock := s.clock - 1 }

/-- The inlined `fix_clock old_s (res,new_s)` (panSem `fix_clock_def`): clamp the
returned clock to `min old.clock new.clock`. -/
def clampClock (old : Nat) (r : Option Result × PancakeState σ) :
    Option Result × PancakeState σ :=
  (r.1, { r.2 with clock := min old r.2.clock })

/-- `evaluate (prog, s)` (panSem `evaluate_def`), region subset. -/
def PancakeSem (oracle : Oracle σ) : PancakeProg → PancakeState σ →
    (Option Result × PancakeState σ)
  | .skip, s => (none, s)                                   -- `evaluate (Skip,s) = (NONE,s)`
  | .dec v e cont, s =>
    -- `Dec v sh e prog`: bind, run cont, restore old binding (`res_var`).
    -- shape check `sh = shape_of value` is vacuous (all region values are `One`).
    match eval s e with
    | some val =>
      let r := PancakeSem oracle cont { s with locals := setLocal s.locals v val }
      (r.1, { r.2 with locals := resVar r.2.locals v (s.locals v) })
    | none => (some .error, s)
  | .assign v e, s =>
    -- `Assign Local v src`: valid-value check vacuous for the shape (`One`) but NOT
    -- for the binding: panSem errors on an unbound `v` (PanSemAgree). Write `set_var`.
    match eval s e with
    | some val => (none, { s with locals := setLocal s.locals v val })
    | none => (some .error, s)
  | .store dst src, s =>
    -- `Store dst src`: eval both, `mem_stores addr (flatten value)` on one word.
    match eval s dst, eval s src with
    | some addr, some val =>
      match memStoreWord s.memory s.memaddrs addr val with
      | some m => (none, { s with memory := m })
      | none => (some .error, s)
    | _, _ => (some .error, s)
  | .extCall name cptr clen aptr alen, s =>
    -- `ExtCall`: read conf=[clen bytes @cptr], arr=[alen bytes @aptr], call the
    -- oracle (A0), write new bytes back @aptr. (panSem names the four evals
    -- sz1/ad1/sz2/ad2; read_bytearray sz1 (w2n ad1) = addr cptr, count clen.)
    match eval s cptr, eval s clen, eval s aptr, eval s alen with
    | some cp, some cl, some ap, some al =>
      match readByteArray s.memory s.memaddrs s.be cp cl.toNat,
            readByteArray s.memory s.memaddrs s.be ap al.toNat with
      | some conf, some arr =>
        match oracle.call s.ffi name conf arr with
        | .final outcome => (some (.finalFFI outcome), emptyLocals s)
        | .ret newffi newBytes =>
          (none, { s with memory := writeByteArray s.memaddrs s.be ap newBytes s.memory,
                          ffi := newffi })
      | _, _ => (some .error, s)
    | _, _, _, _ => (some .error, s)
  | .seq c1 c2, s =>
    -- `Seq c1 c2`: `let (res,s1) = fix_clock s (evaluate (c1,s))`; if NONE run c2.
    let r := clampClock s.clock (PancakeSem oracle c1 s)
    match r.1 with
    | none => PancakeSem oracle c2 r.2
    | some res => (some res, r.2)
  | .cond e c1 c2, s =>
    -- `If e c1 c2`: `evaluate (if w <> 0w then c1 else c2, s)`. False is 0w.
    match eval s e with
    | some w => PancakeSem oracle (if w ≠ 0 then c1 else c2) s
    | none => (some .error, s)
  | .while_ e c, s =>
    -- `While e c`: clocked loop. `w<>0w` continues; clock=0 → TimeOut.
    match eval s e with
    | some w =>
      if w ≠ 0 then
        if s.clock = 0 then (some .timeout, emptyLocals s)
        else
          let r := clampClock (s.clock - 1) (PancakeSem oracle c (decClock s))
          match r.1 with
          | some .continue_ => PancakeSem oracle (.while_ e c) r.2
          | none            => PancakeSem oracle (.while_ e c) r.2
          | some .break_    => (none, r.2)
          | some res        => (some res, r.2)
      else (none, s)
    | none => (some .error, s)
  | .ret e, s =>
    -- `Return e`: `size_of_shape (shape_of value) ≤ 32` is vacuous (One = size 1).
    match eval s e with
    | some v => (some (.return_ v), emptyLocals s)
    | none => (some .error, s)
  | .storeByte dst src, s =>
    -- `StoreByte dst src` (panSem `evaluate (StoreByte ...)` clause): both operands
    -- must evaluate to `ValWord`; store the LOW BYTE of the source word — panSem's
    -- `w2w value : word8`, i.e. truncation `setWidth 8` — at the destination address
    -- via `mem_store_byte`. Out-of-range store (`NONE`) raises `Error`.
    match eval s dst, eval s src with
    | some adr, some w =>
      match memStoreByte s.memory s.memaddrs s.be adr (w.setWidth 8) with
      | some m => (none, { s with memory := m })
      | none => (some .error, s)
    | _, _ => (some .error, s)
  termination_by prog s => (s.clock, sizeOf prog)
  decreasing_by
    all_goals simp_wf
    all_goals
      first
        -- clock strictly decreases (While body via dec_clock, While recurse via clamp)
        | (apply Prod.Lex.left; simp only [clampClock, decClock]; omega)
        -- clock unchanged, size decreases (Dec cont, Seq c1, If chosen branch)
        | (apply Prod.Lex.right; (try split) <;> simp +arith)
        -- clamped clock (Seq c2): min s.clock _ ≤ s.clock, split eq/lt
        | (rw [Prod.lex_def]; simp only [clampClock];
           rcases Nat.eq_or_lt_of_le (Nat.min_le_left s.clock _) with h | h
           · exact Or.inr ⟨h, by simp +arith⟩
           · exact Or.inl h)

/-! ### 4.1 Refinement lemma for the byte store `StoreByte`

Characterises `evaluate (StoreByte dst src, s)` in terms of `mem_store_byte` on
the LOW BYTE of the source word (panSem's `w2w value`, i.e. `setWidth 8`):
whenever both operands evaluate and the byte-store is in range (`memStoreByte …
= some m`), the run raises NO result (`none`) and the post-state's memory IS the
byte-stored memory `m`, every other field of `s` unchanged. This is the
non-vacuous obligation that Lower.lean's lowering of `st8` (`PStmt.storeb`) to
`StoreByte` rests on: the conclusion pins the compiled post-state to the
`memStoreByte` image, not a `P → P` tautology. -/
theorem evaluate_storeByte (oracle : Oracle σ) (s : PancakeState σ)
    {dst src : PancakeExp} {adr w : Word} {m : Word → Word}
    (hd : eval s dst = some adr) (hs : eval s src = some w)
    (hm : memStoreByte s.memory s.memaddrs s.be adr (w.setWidth 8) = some m) :
    PancakeSem oracle (.storeByte dst src) s = (none, { s with memory := m }) := by
  simp only [PancakeSem, hd, hs, hm]

/-- The out-of-range companion: when the byte-store falls outside the address
domain (`memStoreByte … = none`), `StoreByte` raises `Error` and leaves the state
untouched (panSem's `NONE => (SOME Error, s)`). -/
theorem evaluate_storeByte_error (oracle : Oracle σ) (s : PancakeState σ)
    {dst src : PancakeExp} {adr w : Word}
    (hd : eval s dst = some adr) (hs : eval s src = some w)
    (hm : memStoreByte s.memory s.memaddrs s.be adr (w.setWidth 8) = none) :
    PancakeSem oracle (.storeByte dst src) s = (some .error, s) := by
  simp only [PancakeSem, hd, hs, hm]

end Pancake
