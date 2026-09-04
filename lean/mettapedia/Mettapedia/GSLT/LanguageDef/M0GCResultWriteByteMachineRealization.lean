import Mettapedia.GSLT.LanguageDef.M0GCCheckedByteMachineIR

/-!
# Source-derived result writes in the checked byte-machine

This module lowers one genuine mutable operation of the unified M0GC checker
to a finite instruction program.  The source operation is
`CheckerMemory.writeResultNext?`; the target program materializes the selected
physical cell address and result identifier, performs one checked
little-endian word store, and returns success.

The correspondence is not agreement between handwritten twins.  The target
program is constructed from the source memory's checked cell address.  A
successful source write yields a four-instruction accepting target trace with
exactly the same backing bytes, while successful compilation reflects the
source capacity condition and therefore guarantees that the source write can
be performed.

Maturity boundary: this is a fully connected intermediate proof of concept
for the mutable-result operation, not the complete checker lowering.  It does
not yet lower decoding, preparation, matching, rule validation, premise
iteration, or final observation.  The program uses the specification-level
typed byte-machine and has not yet been rendered as StructuredC, Clight,
Pancake, portable C, object code, or machine code.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.M0GCResultWriteByteMachineRealization

open Mettapedia.GSLT.LanguageDef.M0GCWordAddressedMemory
open Mettapedia.GSLT.LanguageDef.M0GCBytePackedResultStoreRefinement
open Mettapedia.GSLT.LanguageDef.M0GCFixedResultStoreRefinement
open Mettapedia.GSLT.LanguageDef.M0GCDisjointCertificateResultMemory
open Mettapedia.GSLT.LanguageDef.M0GCDisjointCertificateResultMemory.CheckerMemory
open Mettapedia.GSLT.LanguageDef.M0GCCheckedByteMachineIR

/-! ## Generated four-instruction write program -/

def shape : RegisterShape where
  byteCount := 0
  word16Count := 0
  word32Count := 1
  word64Count := 0
  addressCount := 1
  flagCount := 0

def resultRegister : Word32Register shape := ⟨0, by decide⟩
def addressRegister : AddressRegister shape := ⟨0, by decide⟩

/-- The target program is a pure function of the selected physical address
and the logical result identifier. -/
def program (address : UInt64) (resultId : UInt32) : Program shape where
  code := #[
    .constAddress addressRegister address,
    .constWord32 resultRegister resultId,
    .storeWord32LE addressRegister resultRegister,
    .halt true]

/-- Compile only when the source allocation exposes the next result cell. -/
def compile? (memory : CheckerMemory) (resultId : UInt32) :
    Option (Program shape) := do
  let address ← memory.cellAddress? memory.resultUsed
  some (program address resultId)

def initialState (memory : CheckerMemory) : MachineState shape :=
  .running 0 (RegisterFile.zero shape) (ByteMemory.ofCheckerMemory memory)

def execute (address : UInt64) (resultId : UInt32)
    (memory : CheckerMemory) : MachineState shape :=
  runSteps (program address resultId) 4 (initialState memory)

/-! ## Instruction-level behavior -/

theorem execute_observes_success_of_store
    {address : UInt64} {resultId : UInt32} {memory : CheckerMemory}
    {updated : ByteMemory}
    (stored : (ByteMemory.ofCheckerMemory memory).storeUInt32LE?
      address resultId = some updated) :
    (execute address resultId memory).observe = some (.ok true) := by
  simp [execute, runSteps, step, executeInstruction, continueAt, program,
    initialState, RegisterFile.writeAddress, RegisterFile.writeWord32, stored,
    MachineState.observe]

theorem execute_memory_of_store
    {address : UInt64} {resultId : UInt32} {memory : CheckerMemory}
    {updated : ByteMemory}
    (stored : (ByteMemory.ofCheckerMemory memory).storeUInt32LE?
      address resultId = some updated) :
    (execute address resultId memory).memory = updated := by
  simp [execute, runSteps, step, executeInstruction, continueAt, program,
    initialState, RegisterFile.writeAddress, RegisterFile.writeWord32, stored,
    MachineState.memory]

/-! ## Address and store correspondence -/

theorem cellAddress?_some_inBounds
    {memory : CheckerMemory} {index : Nat} {address : UInt64}
    (accepted : memory.cellAddress? index = some address) :
    index < memory.resultCapacity := by
  unfold CheckerMemory.cellAddress? at accepted
  split at accepted
  next inBounds => exact inBounds
  next outside => contradiction

/-- The raw byte-machine resolves the source-selected physical cell address
to exactly the source checker's array offset. -/
theorem rangeOffset?_cellAddress
    {memory : CheckerMemory} {index : Nat} {address : UInt64}
    (wellFormed : memory.WellFormed)
    (inBounds : index < memory.resultCapacity)
    (selected : memory.cellAddress? index = some address) :
    (ByteMemory.ofCheckerMemory memory).rangeOffset? address 4 =
      some (memory.resultOffset + resultCellBytes * index) := by
  have addressValue := cellAddress?_some_toNat selected
  have endFits : address.toNat + (4 : UInt64).toNat < UInt64.size := by
    simp only [UInt64.reduceToNat]
    rw [addressValue, wellFormed.resultBase_eq]
    have allocation := wellFormed.addressable
    rw [wellFormed.size_eq] at allocation
    unfold resultCellBytes at allocation ⊢
    omega
  cases addition : checkedAdd address 4 with
  | none =>
      have succeeds := checkedAdd_of_lt address 4 endFits
      rw [addition] at succeeds
      contradiction
  | some addressEnd =>
      have addressEndValue :
          addressEnd.toNat = address.toNat + (4 : UInt64).toNat :=
        checkedAdd_some_toNat addition
      have baseBefore : memory.base.toNat ≤ address.toNat := by
        rw [addressValue, wellFormed.resultBase_eq]
        omega
      have endInside :
          addressEnd.toNat ≤ memory.base.toNat + memory.cells.size := by
        rw [addressEndValue, addressValue, wellFormed.resultBase_eq,
          wellFormed.size_eq]
        simp only [UInt64.reduceToNat]
        unfold resultCellBytes
        omega
      unfold ByteMemory.rangeOffset?
      rw [addition]
      simp only [ByteMemory.ofCheckerMemory]
      split
      next _inside =>
        congr 1
        rw [addressValue, wellFormed.resultBase_eq]
        omega
      next outside =>
        exact (outside ⟨baseBefore, endInside⟩).elim

/-- A successful source-level chronological write is exactly one raw
byte-machine word store at the selected physical address. -/
theorem rawStore_of_checkerWrite
    {memory next : CheckerMemory} {resultId : UInt32} {address : UInt64}
    (wellFormed : memory.WellFormed)
    (selected : memory.cellAddress? memory.resultUsed = some address)
    (accepted : memory.writeResultNext? resultId = some next) :
    (ByteMemory.ofCheckerMemory memory).storeUInt32LE? address resultId =
      some (ByteMemory.ofCheckerMemory next) := by
  have room : memory.resultUsed < memory.resultCapacity :=
    cellAddress?_some_inBounds selected
  have range := rangeOffset?_cellAddress wellFormed room selected
  let offset := memory.resultOffset + resultCellBytes * memory.resultUsed
  cases packed :
      M0GCBytePackedResultStoreRefinement.storeUInt32LE?
        memory.cells offset resultId with
  | none =>
      simp [CheckerMemory.writeResultNext?, room, selected, offset, packed]
        at accepted
  | some cells =>
      simp [CheckerMemory.writeResultNext?, room, selected, offset, packed]
        at accepted
      subst next
      have packedAt :
          M0GCBytePackedResultStoreRefinement.storeUInt32LE?
            memory.cells
              (memory.resultOffset + resultCellBytes * memory.resultUsed)
              resultId = some cells := by
        simpa [offset] using packed
      unfold ByteMemory.storeUInt32LE?
      rw [range]
      simp [ByteMemory.ofCheckerMemory, packedAt]

/-! ## Two-sided one-operation refinement -/

/-- Every successful source write compiles to an accepting four-step target
trace with the exact source-updated byte image. -/
theorem compile_execute_of_checkerWrite
    {memory next : CheckerMemory} {resultId : UInt32}
    (wellFormed : memory.WellFormed)
    (accepted : memory.writeResultNext? resultId = some next) :
    ∃ address,
      compile? memory resultId = some (program address resultId) ∧
      (execute address resultId memory).observe = some (.ok true) ∧
      (execute address resultId memory).memory =
        ByteMemory.ofCheckerMemory next := by
  have room : memory.resultUsed < memory.resultCapacity := by
    by_cases room : memory.resultUsed < memory.resultCapacity
    · exact room
    · simp [CheckerMemory.writeResultNext?, room] at accepted
  obtain ⟨address, selected, _addressValue⟩ :=
    CheckerMemory.cellAddress?_exists memory memory.resultUsed wellFormed room
  have raw := rawStore_of_checkerWrite wellFormed selected accepted
  refine ⟨address, ?_, execute_observes_success_of_store raw,
    execute_memory_of_store raw⟩
  simp [compile?, selected]

/-- Successful generation reflects the source capacity condition.  Hence the
source write exists; a target program cannot be invented for a full result
store. -/
theorem compile?_success_implies_checkerWrite_exists
    {memory : CheckerMemory} {resultId : UInt32} {compiled : Program shape}
    (wellFormed : memory.WellFormed)
    (generated : compile? memory resultId = some compiled) :
    ∃ next, memory.writeResultNext? resultId = some next := by
  unfold compile? at generated
  cases selected : memory.cellAddress? memory.resultUsed with
  | none => simp [selected] at generated
  | some address =>
      have room := cellAddress?_some_inBounds selected
      exact CheckerMemory.writeResultNext?_exists_of_room
        memory resultId wellFormed room

/-! ## Concrete positive and negative canaries -/

namespace Canary

open Mettapedia.GSLT.LanguageDef.M0GCDisjointCertificateResultMemory.CheckerMemory.Canary

theorem concrete_compiles :
    compile? emptyMemory 0x11223344 = some (program 4 0x11223344) := by
  decide

theorem concrete_executes_exactly :
    (execute 4 0x11223344 emptyMemory).observe = some (.ok true) ∧
      (execute 4 0x11223344 emptyMemory).memory =
        ByteMemory.ofCheckerMemory writtenMemory := by
  decide

def fullMemory : CheckerMemory :=
  { emptyMemory with resultUsed := 2 }

theorem full_source_write_rejected :
    fullMemory.writeResultNext? 7 = none := by
  decide

theorem full_target_generation_rejected :
    compile? fullMemory 7 = none := by
  decide

end Canary

#print axioms rangeOffset?_cellAddress
#print axioms rawStore_of_checkerWrite
#print axioms compile_execute_of_checkerWrite
#print axioms compile?_success_implies_checkerWrite_exists
#print axioms Canary.concrete_executes_exactly
#print axioms Canary.full_target_generation_rejected

end Mettapedia.GSLT.LanguageDef.M0GCResultWriteByteMachineRealization
