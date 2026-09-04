import Mettapedia.GSLT.LanguageDef.M0GCBodyViewByteMachineRealization
import Mathlib.Tactic

/-!
# Checked indexed M0GC body addresses in the byte-machine

The zero-copy body view retains a base and count for each canonical table.
This module resolves one requested record address without copying or decoding
the table.  The independent source operation first checks `index < count`,
then performs checked `index * width` and `base + offset`.  The target is a
fixed eight-instruction byte-machine program with the same rejection/fault
distinction.

The generic resolver is shared by term, child, proof, argument, and premise
tables.  A small typed selector connects it to `BodyView`, keeping table
identity explicit even when two empty adjacent tables legitimately have the
same physical base.

Maturity boundary: this is a connected intermediate proof of concept, not an
endgame record decoder or production checker.  It proves address selection
only.  It does not yet load record fields, validate cross-table references,
compute the body checksum, replay a proof, allocate endgame registers, emit C,
or implement the official MM0/MMB format.  The proof-oriented register layout
may later be coalesced only behind a liveness/refinement theorem.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.M0GCIndexedBodyAddressByteMachineRealization

open Mettapedia.GSLT.LanguageDef.M0GCCheckedByteMachineIR
open Mettapedia.GSLT.LanguageDef.M0GCBodyViewByteMachineRealization
open Mettapedia.GSLT.LanguageDef.M0GCWordAddressedMemory

/-! ## Independent source operation -/

/-- Resolve one fixed-width table record.  An index outside the retained table
count is a logical rejection.  Arithmetic overflow is a physical-address
fault. -/
def resolveDetailed (base : UInt64) (count index : UInt32) (width : UInt64) :
    Except Fault (Option UInt64) :=
  if index.toNat < count.toNat then do
    let offset <- mulAddressDetailed index.toUInt64 width
    let address <- addAddressDetailed base offset
    pure (some address)
  else
    pure none

/-! ## Fixed target program -/

def shape : RegisterShape where
  byteCount := 0
  word16Count := 0
  word32Count := 2
  word64Count := 0
  addressCount := 6
  flagCount := 1

def countRegister : Word32Register shape := ⟨0, by decide⟩
def indexRegister : Word32Register shape := ⟨1, by decide⟩

def baseAddress : AddressRegister shape := ⟨0, by decide⟩
def indexAddress : AddressRegister shape := ⟨1, by decide⟩
def countAddress : AddressRegister shape := ⟨2, by decide⟩
def strideAddress : AddressRegister shape := ⟨3, by decide⟩
def offsetAddress : AddressRegister shape := ⟨4, by decide⟩
def resultAddress : AddressRegister shape := ⟨5, by decide⟩

def inBounds : FlagRegister shape := ⟨0, by decide⟩

attribute [local simp] shape countRegister indexRegister baseAddress
  indexAddress countAddress strideAddress offsetAddress resultAddress inBounds

attribute [local simp] bind Except.bind pure Except.pure

/-- Width-parametric address resolution.  The only table-specific constant is
the canonical record width supplied when the program is constructed. -/
def program (width : UInt64) : Program shape where
  code := #[
    .word32ToAddress indexAddress indexRegister,
    .word32ToAddress countAddress countRegister,
    .lessAddress inBounds indexAddress countAddress,
    .rejectUnless inBounds,
    .constAddress strideAddress width,
    .mulAddressChecked offsetAddress indexAddress strideAddress,
    .addAddressChecked resultAddress baseAddress offsetAddress,
    .halt true]

def initialRegisters (base : UInt64) (count index : UInt32) :
    RegisterFile shape :=
  ((((RegisterFile.zero shape).writeWord32 countRegister count).writeWord32
      indexRegister index).writeAddress baseAddress base)

def initialState (memory : ByteMemory) (base : UInt64)
    (count index : UInt32) : MachineState shape :=
  .running 0 (initialRegisters base count index) memory

def execute (memory : ByteMemory) (base : UInt64) (count index : UInt32)
    (width : UInt64) : MachineState shape :=
  runSteps (program width) 8 (initialState memory base count index)

/-- Observe the selected address while retaining logical rejection and
physical fault as different outcomes. -/
def observeAddress : MachineState shape ->
    Option (Except Fault (Option UInt64))
  | .running _ _ _ => none
  | .halted false _ _ => some (.ok none)
  | .halted true registers _ =>
      some (.ok (some (registers.addresses resultAddress)))
  | .faulted reason _ _ => some (.error reason)

/-! ## Generic source/target agreement -/

/-- The fixed target program implements the independent address resolver for
every base, count, index, width, and backing allocation. -/
theorem execute_agrees_resolveDetailed (memory : ByteMemory) (base : UInt64)
    (count index : UInt32) (width : UInt64) :
    observeAddress (execute memory base count index width) =
      some (resolveDetailed base count index width) := by
  by_cases bounds : index.toNat < count.toNat
  · cases hMul : checkedMul index.toUInt64 width with
    | none =>
        simp [execute, initialState, initialRegisters, program, observeAddress,
          resolveDetailed, mulAddressDetailed, runSteps,
          step, executeInstruction, continueAt, bounds, hMul]
    | some offset =>
        cases hAdd : checkedAdd base offset with
        | none =>
            simp [execute, initialState, initialRegisters, program,
              observeAddress, resolveDetailed, addAddressDetailed,
              mulAddressDetailed, runSteps, step, executeInstruction,
              continueAt, bounds, hMul, hAdd]
        | some address =>
            simp [execute, initialState, initialRegisters, program,
              observeAddress, resolveDetailed, addAddressDetailed,
              mulAddressDetailed, runSteps, step, executeInstruction,
              continueAt, bounds, hMul, hAdd]
  · simp [execute, initialState, initialRegisters, program, observeAddress,
      resolveDetailed, runSteps, step, executeInstruction, continueAt, bounds]

/-! ## Typed connection to the prepared body view -/

/-- The five canonical M0GC body tables.  Table identity is not inferred from
physical-base inequality because adjacent empty tables may share a base. -/
inductive BodyTable where
  | term
  | child
  | proof
  | argument
  | premise
deriving DecidableEq, Repr

namespace BodyTable

/-- Canonical record width in bytes. -/
def width : BodyTable -> UInt64
  | .term => 20
  | .child => 4
  | .proof => 32
  | .argument => 4
  | .premise => 4

end BodyTable

def tableBase (view : BodyView) : BodyTable -> UInt64
  | .term => view.termBase
  | .child => view.childBase
  | .proof => view.proofBase
  | .argument => view.argumentBase
  | .premise => view.premiseBase

def tableCount (view : BodyView) : BodyTable -> UInt32
  | .term => view.termCount
  | .child => view.childCount
  | .proof => view.proofCount
  | .argument => view.argumentCount
  | .premise => view.premiseCount

/-- Resolve a record through an already-qualified body view. -/
def resolveTableDetailed (view : BodyView) (table : BodyTable)
    (index : UInt32) : Except Fault (Option UInt64) :=
  resolveDetailed (tableBase view table) (tableCount view table) index table.width

/-- The machine theorem specializes directly to every selected body table. -/
theorem execute_table_agrees (memory : ByteMemory) (view : BodyView)
    (table : BodyTable) (index : UInt32) :
    observeAddress
        (execute memory (tableBase view table) (tableCount view table) index
          table.width) =
      some (resolveTableDetailed view table index) := by
  exact execute_agrees_resolveDetailed memory (tableBase view table)
    (tableCount view table) index table.width

/-! ## Positive and negative executable controls -/

namespace Canary

def memory : ByteMemory := ByteMemory.ofList 1000 []

theorem term_zero_resolves :
    resolveTableDetailed
        M0GCBodyViewByteMachineRealization.Canary.expectedView .term 0 =
      .ok (some 1104) := by
  decide

theorem proof_zero_resolves :
    resolveTableDetailed
        M0GCBodyViewByteMachineRealization.Canary.expectedView .proof 0 =
      .ok (some 1124) := by
  decide

/-- The empty child table shares its base with the proof table, but its count
still rejects every index. -/
theorem empty_child_rejects :
    resolveTableDetailed
        M0GCBodyViewByteMachineRealization.Canary.expectedView .child 0 =
      .ok none := by
  decide

theorem index_at_count_rejects :
    resolveDetailed 1104 3 3 20 = .ok none := by
  decide

theorem addition_overflow_faults :
    resolveDetailed (UInt64.ofNat (UInt64.size - 1)) 2 1 1 =
      .error .addressOverflow := by
  decide

theorem multiplication_overflow_faults :
    resolveDetailed 0 3 2 (UInt64.ofNat (UInt64.size - 1)) =
      .error .addressOverflow := by
  decide

theorem target_term_zero_resolves :
    observeAddress (execute memory 1104 1 0 20) =
      some (.ok (some 1104)) := by
  rw [execute_agrees_resolveDetailed]
  decide

theorem target_out_of_range_rejects :
    observeAddress (execute memory 1104 1 1 20) =
      some (.ok none) := by
  rw [execute_agrees_resolveDetailed]
  decide

end Canary

#print axioms execute_agrees_resolveDetailed
#print axioms execute_table_agrees
#print axioms Canary.term_zero_resolves
#print axioms Canary.empty_child_rejects
#print axioms Canary.addition_overflow_faults
#print axioms Canary.multiplication_overflow_faults
#print axioms Canary.target_term_zero_resolves
#print axioms Canary.target_out_of_range_rejects

end Mettapedia.GSLT.LanguageDef.M0GCIndexedBodyAddressByteMachineRealization
