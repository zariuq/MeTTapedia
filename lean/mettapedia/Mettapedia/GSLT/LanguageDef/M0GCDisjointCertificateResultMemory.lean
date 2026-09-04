import Mettapedia.GSLT.LanguageDef.M0GCBytePackedResultStoreRefinement
import Mettapedia.GSLT.LanguageDef.M0GCWordAddressedMemory

/-!
# Disjoint certificate and result memory for the M0GC checker

This module places the immutable M0GC certificate image and the mutable
chronological result table in one finite byte array.  The result suffix begins
at the least four-byte-aligned physical address at or after the certificate.
The state retains the original certificate bytes as proof-relevant immutable
authority; reachable states must agree with that snapshot at every certificate
position.

The central frame theorem says that a successful result write changes exactly
its selected four-byte result field while preserving every certificate byte
and every earlier admitted result.  Address formation is checked against the
complete unsigned 64-bit carrier, and allocation rejects layouts whose final
exclusive bound would wrap.

Maturity boundary: this is a fully connected intermediate proof of concept.
The memory is a persistent Lean `Array`, certificate immutability is a proved
state invariant rather than an operating-system page permission, and there is
not yet pointer provenance, an optimized ABI, generated C, a verified
compiler, object code, an OS, or hardware.  It is also not the official
MM0/MMB format.  The explicit layout and frame laws are intended as the
source semantics for those later refinements.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.M0GCDisjointCertificateResultMemory

open Mettapedia.GSLT.LanguageDef.CompiledPlanWireFormat
open Mettapedia.GSLT.LanguageDef.M0GCWireFormat
open Mettapedia.GSLT.LanguageDef.M0GCBoundedByteMemory
open Mettapedia.GSLT.LanguageDef.M0GCWordAddressedMemory
open Mettapedia.GSLT.LanguageDef.M0GCFixedResultStoreRefinement
open Mettapedia.GSLT.LanguageDef.M0GCBytePackedResultStoreRefinement

/-! ## Alignment and physical layout -/

/-- Minimal padding required to align a natural-number address to a
four-byte result-cell boundary. -/
def alignmentPadding (address : Nat) : Nat :=
  (resultCellBytes - address % resultCellBytes) % resultCellBytes

theorem alignmentPadding_lt (address : Nat) :
    alignmentPadding address < resultCellBytes := by
  unfold alignmentPadding
  exact Nat.mod_lt _ (by decide)

theorem alignmentPadding_aligned (address : Nat) :
    (address + alignmentPadding address) % resultCellBytes = 0 := by
  unfold alignmentPadding resultCellBytes
  omega

/-- Byte offset of the result suffix within one allocation. -/
def resultOffsetFor (base : UInt64) (certificateBytes : Nat) : Nat :=
  certificateBytes + alignmentPadding (base.toNat + certificateBytes)

theorem certificate_le_resultOffset (base : UInt64)
    (certificateBytes : Nat) :
    certificateBytes ≤ resultOffsetFor base certificateBytes := by
  simp [resultOffsetFor]

theorem resultAddress_aligned (base : UInt64) (certificateBytes : Nat) :
    (base.toNat + resultOffsetFor base certificateBytes) %
        resultCellBytes = 0 := by
  rw [resultOffsetFor, ← Nat.add_assoc]
  exact alignmentPadding_aligned (base.toNat + certificateBytes)

/-- One contiguous allocation with an immutable certificate prefix and a
four-byte-per-cell mutable result suffix.  `certificate` is a ghost snapshot:
the executable bytes are in `cells`, while `WellFormed` requires the selected
prefix to remain equal to the snapshot. -/
structure CheckerMemory where
  base : UInt64
  certificate : Array UInt8
  cells : Array UInt8
  resultOffset : Nat
  resultBase : UInt64
  resultCapacity : Nat
  resultUsed : Nat
deriving DecidableEq, Repr

namespace CheckerMemory

/-- Unaligned payload width, excluding any padding inserted between the
certificate and result suffix. -/
def payloadBytes (certificateBytes resultCapacity : Nat) : Nat :=
  certificateBytes + resultCellBytes * resultCapacity

/-- Reachable unified-memory invariant. -/
structure WellFormed (memory : CheckerMemory) : Prop where
  offset_eq : memory.resultOffset =
    resultOffsetFor memory.base memory.certificate.size
  resultBase_eq : memory.resultBase.toNat =
    memory.base.toNat + memory.resultOffset
  size_eq : memory.cells.size =
    memory.resultOffset + resultCellBytes * memory.resultCapacity
  used_le : memory.resultUsed ≤ memory.resultCapacity
  addressable : memory.base.toNat + memory.cells.size < UInt64.size
  certificate_frame : ∀ index, index < memory.certificate.size →
    memory.cells[index]? = memory.certificate[index]?

/-- Allocate one zero-initialized result suffix after the immutable
certificate prefix.  The conditional covers the complete allocation rather
than merely the first result address. -/
def allocate? (base : UInt64) (certificate : Array UInt8)
    (resultCapacity : Nat) : Option CheckerMemory :=
  let resultOffset := resultOffsetFor base certificate.size
  let totalBytes := resultOffset + resultCellBytes * resultCapacity
  if addressable : base.toNat + totalBytes < UInt64.size then
    have resultBaseAddressable :
        base.toNat + resultOffset < UInt64.size :=
      lt_of_le_of_lt
        (Nat.add_le_add_left
          (Nat.le_add_right resultOffset
            (resultCellBytes * resultCapacity)) base.toNat)
        addressable
    let resultBase := UInt64.ofNatLT
      (base.toNat + resultOffset) resultBaseAddressable
    let suffix := Array.replicate (totalBytes - certificate.size) 0
    some
      { base
        certificate
        cells := certificate ++ suffix
        resultOffset
        resultBase
        resultCapacity
        resultUsed := 0 }
  else
    none

theorem allocate?_shape {base : UInt64} {certificate : Array UInt8}
    {resultCapacity : Nat} {memory : CheckerMemory}
    (allocated : allocate? base certificate resultCapacity = some memory) :
    memory.base = base ∧ memory.certificate = certificate ∧
      memory.resultOffset = resultOffsetFor base certificate.size ∧
      memory.resultBase.toNat =
        base.toNat + resultOffsetFor base certificate.size ∧
      memory.resultCapacity = resultCapacity ∧ memory.resultUsed = 0 := by
  simp only [allocate?] at allocated
  split at allocated
  next addressable =>
    simp only [Option.some.injEq] at allocated
    subst memory
    simp [UInt64.toNat_ofNatLT]
    unfold resultCellBytes at addressable
    exact lt_of_le_of_lt
      (Nat.add_le_add_left
        (Nat.le_add_right (resultOffsetFor base certificate.size)
          (4 * resultCapacity)) base.toNat)
      addressable
  next overflow => contradiction

theorem allocate?_wellFormed {base : UInt64} {certificate : Array UInt8}
    {resultCapacity : Nat} {memory : CheckerMemory}
    (allocated : allocate? base certificate resultCapacity = some memory) :
    memory.WellFormed := by
  simp only [allocate?] at allocated
  split at allocated
  next addressable =>
    simp only [Option.some.injEq] at allocated
    subst memory
    let resultOffset := resultOffsetFor base certificate.size
    let totalBytes := resultOffset + resultCellBytes * resultCapacity
    have certificateFits : certificate.size ≤ totalBytes := by
      dsimp only [totalBytes]
      exact (certificate_le_resultOffset base certificate.size).trans
        (Nat.le_add_right _ _)
    refine
      { offset_eq := rfl
        resultBase_eq := UInt64.toNat_ofNatLT
        size_eq := ?_
        used_le := by simp
        addressable := ?_
        certificate_frame := ?_ }
    · simp [totalBytes, resultOffset, certificateFits]
    · simpa [totalBytes, resultOffset, certificateFits] using addressable
    · intro index inCertificate
      simp [Array.getElem?_append_left, inCertificate]
  next overflow => contradiction

/-- Successful allocation has one contiguous array of the requested aligned
width. -/
theorem allocate?_cells_size {base : UInt64} {certificate : Array UInt8}
    {resultCapacity : Nat} {memory : CheckerMemory}
    (allocated : allocate? base certificate resultCapacity = some memory) :
    memory.cells.size =
      resultOffsetFor base certificate.size +
        resultCellBytes * resultCapacity :=
  (allocate?_wellFormed allocated).size_eq.trans (by
    rw [(allocate?_shape allocated).2.2.1,
      (allocate?_shape allocated).2.2.2.2.1])

/-! ## Disjoint address ranges -/

/-- Half-open membership in the immutable certificate range, using allocation
relative byte offsets. -/
def InCertificateRange (memory : CheckerMemory) (offset : Nat) : Prop :=
  offset < memory.certificate.size

/-- Half-open membership in the complete result allocation, whether or not a
cell has yet been initialized. -/
def InResultRange (memory : CheckerMemory) (offset : Nat) : Prop :=
  memory.resultOffset ≤ offset ∧
    offset < memory.resultOffset +
      resultCellBytes * memory.resultCapacity

theorem certificate_result_disjoint (memory : CheckerMemory)
    (wellFormed : memory.WellFormed) {offset : Nat}
    (certificate : memory.InCertificateRange offset)
    (result : memory.InResultRange offset) : False := by
  have certificateBeforeResult :
      memory.certificate.size ≤ memory.resultOffset := by
    rw [wellFormed.offset_eq]
    exact certificate_le_resultOffset _ _
  unfold InCertificateRange at certificate
  unfold InResultRange at result
  omega

/-- Physical result-cell address, rejected outside the allocated suffix or
when unsigned address formation would wrap. -/
def cellAddress? (memory : CheckerMemory) (index : Nat) : Option UInt64 :=
  if _inBounds : index < memory.resultCapacity then
    if addressable :
        memory.resultBase.toNat + resultCellBytes * index < UInt64.size then
      some (UInt64.ofNatLT
        (memory.resultBase.toNat + resultCellBytes * index) addressable)
    else
      none
  else
    none

theorem cellAddress?_some_toNat {memory : CheckerMemory} {index : Nat}
    {address : UInt64}
    (accepted : memory.cellAddress? index = some address) :
    address.toNat =
      memory.resultBase.toNat + resultCellBytes * index := by
  unfold cellAddress? at accepted
  split at accepted
  next inBounds =>
    split at accepted
    next addressable =>
      simp only [Option.some.injEq] at accepted
      subst address
      exact UInt64.toNat_ofNatLT
    next overflow => contradiction
  next outOfBounds => contradiction

theorem cellAddress?_exists (memory : CheckerMemory) (index : Nat)
    (wellFormed : memory.WellFormed)
    (inBounds : index < memory.resultCapacity) :
    ∃ address, memory.cellAddress? index = some address ∧
      address.toNat =
        memory.resultBase.toNat + resultCellBytes * index := by
  have addressable :
      memory.resultBase.toNat + resultCellBytes * index < UInt64.size := by
    rw [wellFormed.resultBase_eq]
    have allocationAddressable := wellFormed.addressable
    rw [wellFormed.size_eq] at allocationAddressable
    unfold resultCellBytes at allocationAddressable ⊢
    omega
  let address := UInt64.ofNatLT
    (memory.resultBase.toNat + resultCellBytes * index) addressable
  refine ⟨address, ?_, ?_⟩
  · simp [cellAddress?, inBounds, addressable, address]
  · exact UInt64.toNat_ofNatLT

/-- Every result address is four-byte aligned in physical address space. -/
theorem cellAddress_aligned {memory : CheckerMemory} {index : Nat}
    {address : UInt64} (wellFormed : memory.WellFormed)
    (accepted : memory.cellAddress? index = some address) :
    address.toNat % resultCellBytes = 0 := by
  rw [cellAddress?_some_toNat accepted, wellFormed.resultBase_eq,
    wellFormed.offset_eq]
  have baseAligned :=
    resultAddress_aligned memory.base memory.certificate.size
  unfold resultCellBytes at baseAligned ⊢
  omega

/-! ## Checked mutable result operations -/

/-- Read only a completely initialized result cell from its location in the
single backing array. -/
def readResult? (memory : CheckerMemory) (index : Nat) : Option UInt32 :=
  if _admitted : index < memory.resultUsed then do
    let _address ← memory.cellAddress? index
    loadUInt32LE? memory.cells
      (memory.resultOffset + resultCellBytes * index)
  else
    none

/-- Write the next chronological result into the single backing array. -/
def writeResultNext? (memory : CheckerMemory)
    (resultId : UInt32) : Option CheckerMemory := do
  if memory.resultUsed < memory.resultCapacity then
    let _address ← memory.cellAddress? memory.resultUsed
    let cells ← storeUInt32LE? memory.cells
      (memory.resultOffset + resultCellBytes * memory.resultUsed) resultId
    some { memory with cells, resultUsed := memory.resultUsed + 1 }
  else
    none

theorem nextField_complete (memory : CheckerMemory)
    (wellFormed : memory.WellFormed)
    (room : memory.resultUsed < memory.resultCapacity) :
    memory.resultOffset + resultCellBytes * memory.resultUsed + 4 ≤
      memory.cells.size := by
  rw [wellFormed.size_eq]
  unfold resultCellBytes
  omega

theorem writeResultNext?_exists_of_room (memory : CheckerMemory)
    (resultId : UInt32) (wellFormed : memory.WellFormed)
    (room : memory.resultUsed < memory.resultCapacity) :
    ∃ next, memory.writeResultNext? resultId = some next := by
  obtain ⟨address, addressEq, _addressValue⟩ :=
    cellAddress?_exists memory memory.resultUsed wellFormed room
  let start := memory.resultOffset +
    resultCellBytes * memory.resultUsed
  let cells0 := memory.cells.setIfInBounds start (uint32ByteLE resultId 0)
  let cells1 := cells0.setIfInBounds (start + 1)
    (uint32ByteLE resultId 8)
  let cells2 := cells1.setIfInBounds (start + 2)
    (uint32ByteLE resultId 16)
  let cells3 := cells2.setIfInBounds (start + 3)
    (uint32ByteLE resultId 24)
  have stored : storeUInt32LE? memory.cells start resultId = some cells3 := by
    simp [storeUInt32LE?, nextField_complete memory wellFormed room,
      start, cells0, cells1, cells2, cells3]
  let next : CheckerMemory :=
    { memory with
      cells := cells3
      resultUsed := memory.resultUsed + 1 }
  refine ⟨next, ?_⟩
  simp [writeResultNext?, room, addressEq, stored, start, next]

/-- A successful result write changes only the byte array and initialized
frontier.  Every allocation descriptor and the ghost certificate snapshot are
preserved literally. -/
theorem writeResultNext?_shape {memory next : CheckerMemory}
    {resultId : UInt32}
    (accepted : memory.writeResultNext? resultId = some next) :
    next.base = memory.base ∧
      next.certificate = memory.certificate ∧
      next.resultOffset = memory.resultOffset ∧
      next.resultBase = memory.resultBase ∧
      next.resultCapacity = memory.resultCapacity ∧
      next.cells.size = memory.cells.size ∧
      next.resultUsed = memory.resultUsed + 1 := by
  by_cases room : memory.resultUsed < memory.resultCapacity
  · cases addressResult : memory.cellAddress? memory.resultUsed with
    | none => simp [writeResultNext?, room, addressResult] at accepted
    | some address =>
        cases cellsResult :
            storeUInt32LE? memory.cells
              (memory.resultOffset + resultCellBytes * memory.resultUsed)
              resultId with
        | none =>
            simp [writeResultNext?, room, addressResult, cellsResult] at accepted
        | some cells =>
            simp [writeResultNext?, room, addressResult, cellsResult] at accepted
            subst next
            simp [storeUInt32LE?_size cellsResult]
  · simp [writeResultNext?, room] at accepted

/-- A result write cannot mutate a certificate byte.  This is the key
read-only frame fact for the unified allocation. -/
theorem certificate_byte_preserved_of_write
    {memory next : CheckerMemory} {resultId : UInt32} {index : Nat}
    (wellFormed : memory.WellFormed)
    (accepted : memory.writeResultNext? resultId = some next)
    (inCertificate : index < memory.certificate.size) :
    next.cells[index]? = memory.cells[index]? := by
  by_cases room : memory.resultUsed < memory.resultCapacity
  · cases addressResult : memory.cellAddress? memory.resultUsed with
    | none => simp [writeResultNext?, room, addressResult] at accepted
    | some address =>
        cases cellsResult :
            storeUInt32LE? memory.cells
              (memory.resultOffset + resultCellBytes * memory.resultUsed)
              resultId with
        | none =>
            simp [writeResultNext?, room, addressResult, cellsResult] at accepted
        | some cells =>
            simp [writeResultNext?, room, addressResult, cellsResult] at accepted
            subst next
            apply getElem?_of_storeUInt32LE?_outside cellsResult
            left
            have beforeResult :
                memory.certificate.size ≤ memory.resultOffset := by
              rw [wellFormed.offset_eq]
              exact certificate_le_resultOffset _ _
            omega
  · simp [writeResultNext?, room] at accepted

/-- Successful writes preserve the complete reachable-memory invariant,
including the immutable certificate frame. -/
theorem writeResultNext?_wellFormed {memory next : CheckerMemory}
    {resultId : UInt32} (wellFormed : memory.WellFormed)
    (accepted : memory.writeResultNext? resultId = some next) :
    next.WellFormed := by
  obtain ⟨sameBase, sameCertificate, sameOffset, sameResultBase,
      sameCapacity, sameSize, nextUsed⟩ := writeResultNext?_shape accepted
  have room : memory.resultUsed < memory.resultCapacity := by
    by_contra noRoom
    simp [writeResultNext?, noRoom] at accepted
  refine
    { offset_eq := ?_
      resultBase_eq := ?_
      size_eq := ?_
      used_le := ?_
      addressable := ?_
      certificate_frame := ?_ }
  · rw [sameOffset, sameBase, sameCertificate]
    exact wellFormed.offset_eq
  · rw [sameResultBase, sameBase, sameOffset]
    exact wellFormed.resultBase_eq
  · rw [sameSize, sameOffset, sameCapacity]
    exact wellFormed.size_eq
  · rw [nextUsed, sameCapacity]
    omega
  · rw [sameBase, sameSize]
    exact wellFormed.addressable
  · intro index inCertificate
    have oldInCertificate : index < memory.certificate.size := by
      simpa [sameCertificate] using inCertificate
    calc
      next.cells[index]? = memory.cells[index]? :=
        certificate_byte_preserved_of_write wellFormed accepted oldInCertificate
      _ = memory.certificate[index]? :=
        wellFormed.certificate_frame index oldInCertificate
      _ = next.certificate[index]? := by rw [sameCertificate]

/-- Reading the cell written by a successful chronological update returns the
exact result identifier. -/
theorem readResult?_writeResultNext_at {memory next : CheckerMemory}
    {resultId : UInt32}
    (accepted : memory.writeResultNext? resultId = some next) :
    next.readResult? memory.resultUsed = some resultId := by
  by_cases room : memory.resultUsed < memory.resultCapacity
  · cases addressResult : memory.cellAddress? memory.resultUsed with
    | none => simp [writeResultNext?, room, addressResult] at accepted
    | some address =>
        cases cellsResult :
            storeUInt32LE? memory.cells
              (memory.resultOffset + resultCellBytes * memory.resultUsed)
              resultId with
        | none =>
            simp [writeResultNext?, room, addressResult, cellsResult] at accepted
        | some cells =>
            simp [writeResultNext?, room, addressResult, cellsResult] at accepted
            subst next
            simp only [readResult?]
            rw [dif_pos (by omega)]
            have sameAddress :
                ({ memory with
                    cells := cells
                    resultUsed := memory.resultUsed + 1 } : CheckerMemory).cellAddress?
                    memory.resultUsed =
                  memory.cellAddress? memory.resultUsed := rfl
            rw [sameAddress, addressResult]
            exact loadUInt32LE?_of_storeUInt32LE? cellsResult
  · simp [writeResultNext?, room] at accepted

/-- A later chronological result write preserves every previously admitted
result observation. -/
theorem readResult?_writeResultNext_before
    {memory next : CheckerMemory} {resultId : UInt32} {index : Nat}
    (accepted : memory.writeResultNext? resultId = some next)
    (before : index < memory.resultUsed) :
    next.readResult? index = memory.readResult? index := by
  by_cases room : memory.resultUsed < memory.resultCapacity
  · cases addressResult : memory.cellAddress? memory.resultUsed with
    | none => simp [writeResultNext?, room, addressResult] at accepted
    | some address =>
        cases cellsResult :
            storeUInt32LE? memory.cells
              (memory.resultOffset + resultCellBytes * memory.resultUsed)
              resultId with
        | none =>
            simp [writeResultNext?, room, addressResult, cellsResult] at accepted
        | some cells =>
            simp [writeResultNext?, room, addressResult, cellsResult] at accepted
            subst next
            have fieldBefore :
                memory.resultOffset + resultCellBytes * index + 4 ≤
                  memory.resultOffset +
                    resultCellBytes * memory.resultUsed := by
              unfold resultCellBytes
              omega
            have nextBefore : index < memory.resultUsed + 1 := by omega
            simp only [readResult?]
            rw [dif_pos nextBefore, dif_pos before]
            have sameAddress :
                ({ memory with
                    cells := cells
                    resultUsed := memory.resultUsed + 1 } : CheckerMemory).cellAddress?
                    index = memory.cellAddress? index := rfl
            rw [sameAddress]
            cases addressAt : memory.cellAddress? index with
            | none => rfl
            | some addressAtValue =>
                exact loadUInt32LE?_of_storeUInt32LE?_before
                  cellsResult fieldBefore
  · simp [writeResultNext?, room] at accepted

/-! ## Refinement to the typed addressed result store -/

/-- Unified byte memory refines the earlier typed-cell result store on every
admitted result observation.  The certificate prefix is extra physical state;
the result suffix shares the typed store's base, capacity, and chronological
frontier. -/
structure RefinesResultStore (memory : CheckerMemory)
    (typed : ResultStore) : Prop where
  memoryWellFormed : memory.WellFormed
  typedWellFormed : typed.WellFormed
  base_eq : memory.resultBase = typed.base
  capacity_eq : memory.resultCapacity = typed.cells.size
  used_eq : memory.resultUsed = typed.used
  read_eq : ∀ index, index < memory.resultUsed →
    memory.readResult? index = typed.readAdmitted? index

namespace RefinesResultStore

/-- Refinement agrees on every checked read, including rejection beyond the
initialized frontier. -/
theorem read_eq_all {memory : CheckerMemory} {typed : ResultStore}
    (refines : RefinesResultStore memory typed) (index : Nat) :
    memory.readResult? index = typed.readAdmitted? index := by
  by_cases admitted : index < memory.resultUsed
  · exact refines.read_eq index admitted
  · have typedNotAdmitted : ¬ index < typed.used := by
      rw [← refines.used_eq]
      exact admitted
    simp [CheckerMemory.readResult?, ResultStore.readAdmitted?, admitted,
      typedNotAdmitted]

/-- Every well-formed unified layout admits a typed reference allocation for
its result suffix. -/
theorem typed_allocation_exists (memory : CheckerMemory)
    (wellFormed : memory.WellFormed) :
    ∃ typed,
      ResultStore.allocate? memory.resultBase memory.resultCapacity =
        some typed := by
  have addressable :
      memory.resultBase.toNat +
          resultCellBytes * memory.resultCapacity < UInt64.size := by
    rw [wellFormed.resultBase_eq]
    have allocationAddressable := wellFormed.addressable
    rw [wellFormed.size_eq] at allocationAddressable
    omega
  let typed : ResultStore :=
    { base := memory.resultBase
      cells := Array.replicate memory.resultCapacity 0
      used := 0 }
  refine ⟨typed, ?_⟩
  simp [ResultStore.allocate?, addressable, typed]

/-- Paired successful allocations establish the initial refinement. -/
theorem of_allocations {base : UInt64} {certificate : Array UInt8}
    {resultCapacity : Nat} {memory : CheckerMemory} {typed : ResultStore}
    (memoryAllocated :
      CheckerMemory.allocate? base certificate resultCapacity = some memory)
    (typedAllocated :
      ResultStore.allocate? memory.resultBase resultCapacity = some typed) :
    RefinesResultStore memory typed := by
  have memoryWellFormed := CheckerMemory.allocate?_wellFormed memoryAllocated
  have typedWellFormed := ResultStore.allocate?_wellFormed typedAllocated
  obtain ⟨_memoryBase, _memoryCertificate, _memoryOffset,
      _memoryResultBase, memoryCapacity, memoryUsed⟩ :=
    CheckerMemory.allocate?_shape memoryAllocated
  obtain ⟨typedBase, typedCapacity, typedUsed⟩ :=
    ResultStore.allocate?_shape typedAllocated
  refine
    { memoryWellFormed
      typedWellFormed
      base_eq := ?_
      capacity_eq := ?_
      used_eq := ?_
      read_eq := ?_ }
  · rw [typedBase]
  · rw [memoryCapacity, typedCapacity]
  · rw [memoryUsed, typedUsed]
  · intro index admitted
    rw [memoryUsed] at admitted
    omega

/-- Synchronized writes preserve the full unified-memory-to-typed-store
refinement relation. -/
theorem write {memory memoryNext : CheckerMemory}
    {typed typedNext : ResultStore} {resultId : UInt32}
    (refines : RefinesResultStore memory typed)
    (memoryAccepted :
      memory.writeResultNext? resultId = some memoryNext)
    (typedAccepted : typed.writeNext? resultId = some typedNext) :
    RefinesResultStore memoryNext typedNext := by
  obtain ⟨_sameMemoryBase, _sameCertificate, _sameOffset, sameResultBase,
      sameMemoryCapacity, _sameBytes, nextMemoryUsed⟩ :=
    CheckerMemory.writeResultNext?_shape memoryAccepted
  have typedCapacity := ResultStore.writeNext?_capacity typedAccepted
  have typedUsed := ResultStore.writeNext?_used typedAccepted
  refine
    { memoryWellFormed :=
        CheckerMemory.writeResultNext?_wellFormed
          refines.memoryWellFormed memoryAccepted
      typedWellFormed :=
        ResultStore.writeNext?_wellFormed refines.typedWellFormed typedAccepted
      base_eq := ?_
      capacity_eq := ?_
      used_eq := ?_
      read_eq := ?_ }
  · rw [sameResultBase, typedWriteNext?_base typedAccepted]
    exact refines.base_eq
  · rw [sameMemoryCapacity, typedCapacity]
    exact refines.capacity_eq
  · rw [nextMemoryUsed, typedUsed, refines.used_eq]
  · intro index admittedNext
    by_cases admittedBefore : index < memory.resultUsed
    · have typedBefore : index < typed.used := by
        rw [← refines.used_eq]
        exact admittedBefore
      rw [CheckerMemory.readResult?_writeResultNext_before
        memoryAccepted admittedBefore]
      rw [typedReadAdmitted?_writeNext_before refines.typedWellFormed
        typedAccepted typedBefore]
      exact refines.read_eq index admittedBefore
    · have atFrontier : index = memory.resultUsed := by
        rw [nextMemoryUsed] at admittedNext
        omega
      subst index
      rw [CheckerMemory.readResult?_writeResultNext_at memoryAccepted]
      rw [refines.used_eq]
      exact (typedReadAdmitted?_writeNext_at
        refines.typedWellFormed typedAccepted).symm

end RefinesResultStore

/-! ## Executable layout and mutation discriminators -/

namespace Canary

def certificate : Array UInt8 := #[10, 20]

def emptyMemory : CheckerMemory :=
  { base := 1
    certificate
    cells := #[10, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    resultOffset := 3
    resultBase := 4
    resultCapacity := 2
    resultUsed := 0 }

def writtenMemory : CheckerMemory :=
  { emptyMemory with
    cells := #[10, 20, 0, 68, 51, 34, 17, 0, 0, 0, 0]
    resultUsed := 1 }

def typedEmpty : ResultStore :=
  { base := 4
    cells := #[0, 0]
    used := 0 }

def typedWritten : ResultStore :=
  { base := 4
    cells := #[0x11223344, 0]
    used := 1 }

/-- A nonzero base and non-aligned certificate length force a real padding
byte before the aligned result suffix. -/
theorem allocation_has_padding :
    CheckerMemory.allocate? 1 certificate 2 = some emptyMemory := by
  decide

theorem result_base_is_aligned :
    emptyMemory.resultBase.toNat % resultCellBytes = 0 := by
  decide

/-- Negative initialized-prefix discriminator: allocated result bytes are not
readable before a proof record admits them. -/
theorem unwritten_result_rejected : emptyMemory.readResult? 0 = none := by
  decide

/-- Positive physical-write discriminator through the unified allocation. -/
theorem first_write_exact :
    emptyMemory.writeResultNext? 0x11223344 = some writtenMemory := by
  decide

theorem first_result_reads_exactly :
    writtenMemory.readResult? 0 = some 0x11223344 := by
  decide

/-- Concrete frame discriminator: the certificate bytes survive the result
write byte-for-byte. -/
theorem certificate_prefix_survives :
    writtenMemory.cells.extract 0 certificate.size = certificate := by
  decide

/-- Negative full-allocation overflow discriminator. -/
theorem overflowing_layout_rejected :
    CheckerMemory.allocate?
      (UInt64.ofNat (UInt64.size - 1)) #[1] 1 = none := by
  decide

/-- The nontrivial padded allocation refines an independently allocated typed
result store by construction. -/
theorem initial_refines_typed :
    RefinesResultStore emptyMemory typedEmpty := by
  exact RefinesResultStore.of_allocations (base := 1)
    (certificate := certificate) (resultCapacity := 2)
    allocation_has_padding (by decide)

/-- The refinement persists across synchronized byte-level and typed writes. -/
theorem written_refines_typed :
    RefinesResultStore writtenMemory typedWritten := by
  exact RefinesResultStore.write initial_refines_typed
    first_write_exact (by decide)

end Canary

end CheckerMemory

#print axioms alignmentPadding_aligned
#print axioms CheckerMemory.allocate?_wellFormed
#print axioms CheckerMemory.certificate_result_disjoint
#print axioms CheckerMemory.cellAddress?_exists
#print axioms CheckerMemory.cellAddress_aligned
#print axioms CheckerMemory.writeResultNext?_exists_of_room
#print axioms CheckerMemory.writeResultNext?_wellFormed
#print axioms CheckerMemory.certificate_byte_preserved_of_write
#print axioms CheckerMemory.readResult?_writeResultNext_at
#print axioms CheckerMemory.readResult?_writeResultNext_before
#print axioms CheckerMemory.RefinesResultStore.of_allocations
#print axioms CheckerMemory.RefinesResultStore.write
#print axioms CheckerMemory.Canary.written_refines_typed

end Mettapedia.GSLT.LanguageDef.M0GCDisjointCertificateResultMemory
