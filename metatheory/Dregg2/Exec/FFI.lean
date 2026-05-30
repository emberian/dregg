/-
# Dregg2.Exec.FFI — the C-ABI boundary onto the PROVED executable kernel.

A thin, scalar-only (`UInt64`/`UInt8`) shell over `Dregg2.Exec` (`Kernel.lean`):
the SAME `exec` whose conservation (`exec_conserves`) and integrity (`exec_authorized`)
are proved in Lean is the one a C/Rust host calls here. No new logic — we only marshal
`UInt64` ⇄ `ℤ` at the boundary and `@[export]` two entry points. This is the cascade
seam for dregg2 §8 (the Rust boundary hosts the verified kernel).
-/
import Dregg2.Exec.Kernel
import Dregg2.Exec.RecordKernel

namespace Dregg2.Exec.FFI

open Dregg2.Exec

/-- **C entry point — run one transfer, return the conserved total.**

Builds a 2-account state (`{0,1}`, `bal 0 ↦ balA`, `bal 1 ↦ balB`, no caps), a turn
moving `amt` from cell 0 to cell 1 under actor 0's own authority, runs the proved
`Exec.exec`, and returns the live total: on success the (conserved) total of the new
state, on a fail-closed `none` the unchanged total of the input. By `exec_conserves`
both equal `balA + balB`. -/
@[export dregg_kernel_transfer_total]
def transferTotal (balA balB amt : UInt64) : UInt64 :=
  let k : KernelState :=
    { accounts := {0, 1}
      bal := fun c => if c = 0 then Int.ofNat balA.toNat
                      else if c = 1 then Int.ofNat balB.toNat else 0
      caps := fun _ => [] }
  let turn : Turn := { actor := 0, src := 0, dst := 1, amt := Int.ofNat amt.toNat }
  let result : KernelState := (Exec.exec k turn).getD k
  (Exec.total result).toNat.toUInt64

/-- **C entry point — the authority check, in isolation.**

Returns `1` iff `actor` is authorized over `src = 0` for a unit transfer under the
empty cap table (i.e. iff `actor = 0`, ownership). Demonstrates `Exec.authorizedB`
— the integrity predicate from `exec` — callable directly from C. -/
@[export dregg_kernel_authorized]
def authorized (actor : UInt64) : UInt8 :=
  if Exec.authorizedB (fun _ => []) { actor := actor.toNat, src := 0, dst := 1, amt := 1 }
  then 1 else 0

/-- **C entry point — run one transfer on the CONTENT-ADDRESSED record cell, return the conserved
total `balance` field.**

The record-cell analog of `transferTotal`: the cell-state is now a `Value` record (carrying a
`balance` field plus, here, a `nonce` field that the transfer must leave intact), NOT two scalars.
We marshal the `balance` FIELD as the scalar at the boundary — the FFI signature stays
`UInt64 → UInt64 → UInt64 → UInt64`, byte-stable with `transferTotal`, so the Rust host and the
10k/10k differential oracle need no signature change — while the PROVED function underneath is now
`RecordKernel.recKExec` over the real record cell. By `recKExec_conserves` the returned total equals
`balA + balB` (conserved over the `balance` field). This turns the scalar PoC into the actual
record-cell migration ratchet, with the marshalling honestly limited to the `balance` field. -/
@[export dregg_record_kernel_transfer_total]
def recordTransferTotal (balA balB amt : UInt64) : UInt64 :=
  let k : RecordKernelState :=
    { accounts := {0, 1}
      cell := fun c => if c = 0 then .record [("balance", .int (Int.ofNat balA.toNat)),
                                              ("nonce", .int 0)]
                       else if c = 1 then .record [("balance", .int (Int.ofNat balB.toNat))]
                       else .record [("balance", .int 0)]
      caps := fun _ => [] }
  let turn : Turn := { actor := 0, src := 0, dst := 1, amt := Int.ofNat amt.toNat }
  let result : RecordKernelState := (Exec.recKExec k turn).getD k
  (Exec.recTotal result).toNat.toUInt64

end Dregg2.Exec.FFI
