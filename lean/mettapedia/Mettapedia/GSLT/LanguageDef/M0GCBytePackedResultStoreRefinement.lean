import Mettapedia.GSLT.LanguageDef.M0GCAddressedReplayControlMachine
import Mettapedia.GSLT.LanguageDef.M0GCBoundedByteMemory

/-!
# Byte-packed result storage for the M0GC checker

This module refines the typed 32-bit result cells used by the addressed M0GC
proof-replay experiment to a fixed-capacity byte region.  Result identifiers
are stored as canonical four-byte little-endian fields.  Allocation checks
four-byte alignment and the complete unsigned 64-bit address range; reads are
restricted to the initialized prefix; writes replace exactly the next four
bytes without growing the allocation.

Maturity boundary: this is a fully connected intermediate proof of concept.
The backing memory is a functional Lean byte array, and `setIfInBounds` models
mutation.  It is not a pointer-provenance model, separation logic, Pancake,
Clight, generated production C, compiler theorem, object code, an OS, or
hardware.  The byte ABI is explicit so later targets can refine it without
inheriting the Lean representation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.M0GCBytePackedResultStoreRefinement

open Mettapedia.GSLT.LanguageDef.CompiledPlanWireFormat
open Mettapedia.GSLT.LanguageDef.M0GCBoundedByteMemory
open Mettapedia.GSLT.LanguageDef.M0GCWireFormat
open Mettapedia.GSLT.LanguageDef.M0GCFixedResultStoreRefinement

/-! ## Exact four-byte scalar mutation -/

/-- One selected little-endian byte of a 32-bit value. -/
def uint32ByteLE (value : UInt32) (shift : Nat) : UInt8 :=
  UInt8.ofBitVec (value.toBitVec.extractLsb' shift 8)

theorem uint32Bytes_eq_encode (value : UInt32) :
    [uint32ByteLE value 0, uint32ByteLE value 8,
      uint32ByteLE value 16, uint32ByteLE value 24] =
      encodeUInt32LE value := rfl

/-- Read one complete little-endian 32-bit field from a byte array. -/
def loadUInt32LE? (cells : Array UInt8) (start : Nat) : Option UInt32 := do
  let byte0 ← cells[start]?
  let byte1 ← cells[start + 1]?
  let byte2 ← cells[start + 2]?
  let byte3 ← cells[start + 3]?
  ByteRegion.readerExhaustive? readUInt32LE [byte0, byte1, byte2, byte3]

/-- Replace exactly one complete four-byte field.  A partial write is never
performed. -/
def storeUInt32LE? (cells : Array UInt8) (start : Nat)
    (value : UInt32) : Option (Array UInt8) :=
  if _complete : start + 4 ≤ cells.size then
    let cells0 := cells.setIfInBounds start (uint32ByteLE value 0)
    let cells1 := cells0.setIfInBounds (start + 1) (uint32ByteLE value 8)
    let cells2 := cells1.setIfInBounds (start + 2) (uint32ByteLE value 16)
    let cells3 := cells2.setIfInBounds (start + 3) (uint32ByteLE value 24)
    some cells3
  else
    none

theorem storeUInt32LE?_size
    {cells updated : Array UInt8} {start : Nat} {value : UInt32}
    (stored : storeUInt32LE? cells start value = some updated) :
    updated.size = cells.size := by
  unfold storeUInt32LE? at stored
  split at stored
  next complete =>
    simp only [Option.some.injEq] at stored
    subst updated
    simp
  next incomplete => contradiction

/-- Reading a successfully stored field returns exactly the written 32-bit
value through the independently defined little-endian decoder. -/
theorem loadUInt32LE?_of_storeUInt32LE?
    {cells updated : Array UInt8} {start : Nat} {value : UInt32}
    (stored : storeUInt32LE? cells start value = some updated) :
    loadUInt32LE? updated start = some value := by
  unfold storeUInt32LE? at stored
  split at stored
  next complete =>
    simp only [Option.some.injEq] at stored
    subst updated
    have start0 : start < cells.size := by omega
    have start1 : start + 1 < cells.size := by omega
    have start2 : start + 2 < cells.size := by omega
    have start3 : start + 3 < cells.size := by omega
    unfold loadUInt32LE?
    simp only [Array.getElem?_setIfInBounds]
    simp [start0, start1, start2, start3,
      ByteRegion.readerExhaustive?, uint32Bytes_eq_encode]
    have decoded : readUInt32LE (encodeUInt32LE value) = some (value, []) := by
      simpa using readUInt32LE_encodeUInt32LE value []
    rw [decoded]
    simp
  next incomplete => contradiction

/-- A four-byte write changes no byte outside its selected half-open field. -/
theorem getElem?_of_storeUInt32LE?_outside
    {cells updated : Array UInt8} {start index : Nat} {value : UInt32}
    (stored : storeUInt32LE? cells start value = some updated)
    (outside : index < start ∨ start + 4 ≤ index) :
    updated[index]? = cells[index]? := by
  unfold storeUInt32LE? at stored
  split at stored
  next complete =>
    simp only [Option.some.injEq] at stored
    subst updated
    simp only [Array.getElem?_setIfInBounds]
    have ne0 : start ≠ index := by omega
    have ne1 : start + 1 ≠ index := by omega
    have ne2 : start + 2 ≠ index := by omega
    have ne3 : start + 3 ≠ index := by omega
    simp [ne0, ne1, ne2, ne3]
  next incomplete => contradiction

/-- Earlier complete fields are observationally unchanged by a later field
write. -/
theorem loadUInt32LE?_of_storeUInt32LE?_before
    {cells updated : Array UInt8} {earlier start : Nat} {value : UInt32}
    (stored : storeUInt32LE? cells start value = some updated)
    (before : earlier + 4 ≤ start) :
    loadUInt32LE? updated earlier = loadUInt32LE? cells earlier := by
  unfold loadUInt32LE?
  rw [getElem?_of_storeUInt32LE?_outside stored
    (by exact Or.inl (by omega))]
  rw [getElem?_of_storeUInt32LE?_outside stored
    (by exact Or.inl (by omega))]
  rw [getElem?_of_storeUInt32LE?_outside stored
    (by exact Or.inl (by omega))]
  rw [getElem?_of_storeUInt32LE?_outside stored
    (by exact Or.inl (by omega))]

/-! ## Fixed-capacity packed result region -/

/-- Byte-packed chronological result storage.  `capacity` and `used` count
32-bit cells; `bytes` is the fixed four-byte-per-cell allocation. -/
structure PackedResultStore where
  base : UInt64
  capacity : Nat
  bytes : Array UInt8
  used : Nat
deriving DecidableEq, Repr

namespace PackedResultStore

/-- Reachable packed-store invariant. -/
def WellFormed (store : PackedResultStore) : Prop :=
  store.bytes.size = resultCellBytes * store.capacity ∧
    store.used ≤ store.capacity ∧
    store.base.toNat % resultCellBytes = 0 ∧
    store.base.toNat + store.bytes.size < UInt64.size

/-- Allocate and zero-initialize a complete aligned result region. -/
def allocate? (base : UInt64) (capacity : Nat) : Option PackedResultStore :=
  if _aligned : base.toNat % resultCellBytes = 0 then
    if _addressable :
        base.toNat + resultCellBytes * capacity < UInt64.size then
      some
        { base
          capacity
          bytes := Array.replicate (resultCellBytes * capacity) 0
          used := 0 }
    else
      none
  else
    none

theorem allocate?_wellFormed {base : UInt64} {capacity : Nat}
    {store : PackedResultStore}
    (allocated : allocate? base capacity = some store) :
    store.WellFormed := by
  unfold allocate? at allocated
  split at allocated
  next aligned =>
    split at allocated
    next addressable =>
      simp only [Option.some.injEq] at allocated
      subst store
      simp [WellFormed, aligned, addressable]
    next overflow => contradiction
  next unaligned => contradiction

/-- Successful allocation has the requested physical shape and no initialized
cells. -/
theorem allocate?_shape {base : UInt64} {capacity : Nat}
    {store : PackedResultStore}
    (allocated : allocate? base capacity = some store) :
    store.base = base ∧ store.capacity = capacity ∧
      store.bytes.size = resultCellBytes * capacity ∧ store.used = 0 := by
  unfold allocate? at allocated
  split at allocated
  next aligned =>
    split at allocated
    next addressable =>
      simp only [Option.some.injEq] at allocated
      subst store
      simp
    next overflow => contradiction
  next unaligned => contradiction

/-- Compute the checked byte address of an allocated result cell. -/
def cellAddress? (store : PackedResultStore) (index : Nat) : Option UInt64 :=
  if _inBounds : index < store.capacity then
    if addressable :
        store.base.toNat + resultCellBytes * index < UInt64.size then
      some
        (UInt64.ofNatLT
          (store.base.toNat + resultCellBytes * index) addressable)
    else
      none
  else
    none

/-- Read only a completely initialized result cell. -/
def readAdmitted? (store : PackedResultStore) (index : Nat) : Option UInt32 :=
  if _admitted : index < store.used then do
    let _address ← store.cellAddress? index
    loadUInt32LE? store.bytes (resultCellBytes * index)
  else
    none

/-- Store one chronological result in the next fixed four-byte cell. -/
def writeNext? (store : PackedResultStore)
    (resultId : UInt32) : Option PackedResultStore := do
  if store.used < store.capacity then
    let _address ← store.cellAddress? store.used
    let bytes ← storeUInt32LE? store.bytes
      (resultCellBytes * store.used) resultId
    some { store with bytes, used := store.used + 1 }
  else
    none

/-! ## Packed allocation and mutation laws -/

/-- A successful packed-cell address is the ordinary, non-wrapping byte
address selected by the ABI. -/
theorem cellAddress?_some_toNat {store : PackedResultStore} {index : Nat}
    {address : UInt64}
    (accepted : store.cellAddress? index = some address) :
    address.toNat = store.base.toNat + resultCellBytes * index := by
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

/-- Every cell in a well-formed packed allocation has a checked byte
address. -/
theorem cellAddress?_exists (store : PackedResultStore) (index : Nat)
    (wellFormed : store.WellFormed) (inBounds : index < store.capacity) :
    ∃ address,
      store.cellAddress? index = some address ∧
        address.toNat = store.base.toNat + resultCellBytes * index := by
  rcases wellFormed with
    ⟨bytesSize, _usedFits, _aligned, allocationAddressable⟩
  have addressable :
      store.base.toNat + resultCellBytes * index < UInt64.size := by
    rw [bytesSize] at allocationAddressable
    unfold resultCellBytes at allocationAddressable ⊢
    omega
  let address := UInt64.ofNatLT
    (store.base.toNat + resultCellBytes * index) addressable
  refine ⟨address, ?_, ?_⟩
  · simp [cellAddress?, inBounds, addressable, address]
  · exact UInt64.toNat_ofNatLT

/-- A well-formed store with a free cell has enough backing bytes for the
complete next four-byte write. -/
theorem nextField_complete (store : PackedResultStore)
    (wellFormed : store.WellFormed) (room : store.used < store.capacity) :
    resultCellBytes * store.used + 4 ≤ store.bytes.size := by
  rw [wellFormed.1]
  unfold resultCellBytes
  omega

/-- A well-formed packed store with available capacity can always perform its
next chronological write. -/
theorem writeNext?_exists_of_room (store : PackedResultStore)
    (resultId : UInt32) (wellFormed : store.WellFormed)
    (room : store.used < store.capacity) :
    ∃ next, store.writeNext? resultId = some next := by
  obtain ⟨address, addressEq, _addressValue⟩ :=
    cellAddress?_exists store store.used wellFormed room
  let bytes0 := store.bytes.setIfInBounds
    (resultCellBytes * store.used) (uint32ByteLE resultId 0)
  let bytes1 := bytes0.setIfInBounds
    (resultCellBytes * store.used + 1) (uint32ByteLE resultId 8)
  let bytes2 := bytes1.setIfInBounds
    (resultCellBytes * store.used + 2) (uint32ByteLE resultId 16)
  let bytes3 := bytes2.setIfInBounds
    (resultCellBytes * store.used + 3) (uint32ByteLE resultId 24)
  have stored :
      storeUInt32LE? store.bytes (resultCellBytes * store.used) resultId =
        some bytes3 := by
    simp [storeUInt32LE?, nextField_complete store wellFormed room,
      bytes0, bytes1, bytes2, bytes3]
  refine ⟨{ store with bytes := bytes3, used := store.used + 1 }, ?_⟩
  simp [writeNext?, room, addressEq, stored]

/-- A successful packed write preserves the allocation shape and advances
the initialized prefix by exactly one cell. -/
theorem writeNext?_shape {store next : PackedResultStore} {resultId : UInt32}
    (accepted : store.writeNext? resultId = some next) :
    next.base = store.base ∧ next.capacity = store.capacity ∧
      next.bytes.size = store.bytes.size ∧ next.used = store.used + 1 := by
  by_cases room : store.used < store.capacity
  · cases addressResult : store.cellAddress? store.used with
    | none => simp [writeNext?, room, addressResult] at accepted
    | some address =>
        cases bytesResult :
            storeUInt32LE? store.bytes (resultCellBytes * store.used)
              resultId with
        | none => simp [writeNext?, room, addressResult, bytesResult] at accepted
        | some bytes =>
            simp [writeNext?, room, addressResult, bytesResult] at accepted
            subst next
            simp [storeUInt32LE?_size bytesResult]
  · simp [writeNext?, room] at accepted

/-- Successful packed writes preserve the reachable-store invariant. -/
theorem writeNext?_wellFormed {store next : PackedResultStore}
    {resultId : UInt32} (wellFormed : store.WellFormed)
    (accepted : store.writeNext? resultId = some next) :
    next.WellFormed := by
  obtain ⟨sameBase, sameCapacity, sameBytes, nextUsed⟩ :=
    writeNext?_shape accepted
  rcases wellFormed with
    ⟨bytesSize, usedFits, aligned, addressable⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [sameBytes, bytesSize, sameCapacity]
  · rw [nextUsed, sameCapacity]
    have room : store.used < store.capacity := by
      by_contra noRoom
      simp [writeNext?, noRoom] at accepted
    omega
  · rw [sameBase]
    exact aligned
  · rw [sameBase, sameBytes]
    exact addressable

/-- Reading the just-written packed cell returns exactly the admitted result
identifier. -/
theorem readAdmitted?_writeNext_at {store next : PackedResultStore}
    {resultId : UInt32}
    (accepted : store.writeNext? resultId = some next) :
    next.readAdmitted? store.used = some resultId := by
  by_cases room : store.used < store.capacity
  · cases addressResult : store.cellAddress? store.used with
    | none => simp [writeNext?, room, addressResult] at accepted
    | some address =>
        cases bytesResult :
            storeUInt32LE? store.bytes (resultCellBytes * store.used)
              resultId with
        | none => simp [writeNext?, room, addressResult, bytesResult] at accepted
        | some bytes =>
            simp [writeNext?, room, addressResult, bytesResult] at accepted
            subst next
            simp only [readAdmitted?]
            rw [dif_pos (by omega)]
            have sameAddress :
                ({ store with bytes := bytes, used := store.used + 1 } :
                    PackedResultStore).cellAddress? store.used =
                  store.cellAddress? store.used := rfl
            rw [sameAddress, addressResult]
            exact loadUInt32LE?_of_storeUInt32LE? bytesResult
  · simp [writeNext?, room] at accepted

/-- A later chronological packed write leaves every already-admitted read
unchanged. -/
theorem readAdmitted?_writeNext_before {store next : PackedResultStore}
    {resultId : UInt32} {index : Nat}
    (accepted : store.writeNext? resultId = some next)
    (before : index < store.used) :
    next.readAdmitted? index = store.readAdmitted? index := by
  by_cases room : store.used < store.capacity
  · cases addressResult : store.cellAddress? store.used with
    | none => simp [writeNext?, room, addressResult] at accepted
    | some address =>
        cases bytesResult :
            storeUInt32LE? store.bytes (resultCellBytes * store.used)
              resultId with
        | none => simp [writeNext?, room, addressResult, bytesResult] at accepted
        | some bytes =>
            simp [writeNext?, room, addressResult, bytesResult] at accepted
            subst next
            have fieldBefore :
                resultCellBytes * index + 4 ≤
                  resultCellBytes * store.used := by
              unfold resultCellBytes
              omega
            have nextBefore : index < store.used + 1 := by omega
            simp only [readAdmitted?]
            rw [dif_pos nextBefore, dif_pos before]
            have sameAddress :
                ({ store with bytes := bytes, used := store.used + 1 } :
                    PackedResultStore).cellAddress? index =
                  store.cellAddress? index := rfl
            rw [sameAddress]
            cases addressAt : store.cellAddress? index with
            | none => rfl
            | some addressAtValue =>
              exact loadUInt32LE?_of_storeUInt32LE?_before
                bytesResult fieldBefore
  · simp [writeNext?, room] at accepted

end PackedResultStore

/-! ## Refinement to the typed addressed reference store -/

/-- A successful typed-cell write preserves the allocation base.  This local
lemma complements the existing capacity and used-count laws. -/
theorem typedWriteNext?_base {store next : ResultStore} {resultId : UInt32}
    (accepted : store.writeNext? resultId = some next) :
    next.base = store.base := by
  by_cases room : store.used < store.cells.size
  · cases addressResult : store.cellAddress? store.used with
    | none => simp [ResultStore.writeNext?, room, addressResult] at accepted
    | some address =>
        simp [ResultStore.writeNext?, room, addressResult] at accepted
        subst next
        rfl
  · simp [ResultStore.writeNext?, room] at accepted

/-- The typed reference store reads back its just-written result. -/
theorem typedReadAdmitted?_writeNext_at
    {store next : ResultStore} {resultId : UInt32}
    (wellFormed : store.WellFormed)
    (accepted : store.writeNext? resultId = some next) :
    next.readAdmitted? store.used = some resultId := by
  have nextWellFormed := ResultStore.writeNext?_wellFormed wellFormed accepted
  rw [ResultStore.readAdmitted?_eq_snapshot next store.used nextWellFormed]
  rw [ResultStore.writeNext?_snapshot accepted]
  have snapshotSize := ResultStore.snapshot_size store wellFormed
  rw [← snapshotSize]
  simp

/-- The typed reference store preserves reads before its next write. -/
theorem typedReadAdmitted?_writeNext_before
    {store next : ResultStore} {resultId : UInt32} {index : Nat}
    (wellFormed : store.WellFormed)
    (accepted : store.writeNext? resultId = some next)
    (before : index < store.used) :
    next.readAdmitted? index = store.readAdmitted? index := by
  have nextWellFormed := ResultStore.writeNext?_wellFormed wellFormed accepted
  rw [ResultStore.readAdmitted?_eq_snapshot next index nextWellFormed]
  rw [ResultStore.readAdmitted?_eq_snapshot store index wellFormed]
  rw [ResultStore.writeNext?_snapshot accepted]
  have snapshotSize := ResultStore.snapshot_size store wellFormed
  have beforeSnapshot : index < store.snapshot.size := by
    rw [snapshotSize]
    exact before
  have indexNe : index ≠ store.snapshot.size := Nat.ne_of_lt beforeSnapshot
  simp [Array.getElem?_push, indexNe, beforeSnapshot]

/-- The byte-packed store refines the typed-cell reference exactly on every
admitted observation, while preserving the same base, capacity, and
chronological frontier. -/
structure RefinesTyped (packed : PackedResultStore)
    (typed : ResultStore) : Prop where
  packedWellFormed : packed.WellFormed
  typedWellFormed : typed.WellFormed
  base_eq : packed.base = typed.base
  capacity_eq : packed.capacity = typed.cells.size
  used_eq : packed.used = typed.used
  read_eq : ∀ index, index < packed.used →
    packed.readAdmitted? index = typed.readAdmitted? index

namespace RefinesTyped

/-- Refinement gives equality for all checked reads, including rejection
outside the initialized prefix. -/
theorem readAdmitted?_eq {packed : PackedResultStore} {typed : ResultStore}
    (refines : RefinesTyped packed typed) (index : Nat) :
    packed.readAdmitted? index = typed.readAdmitted? index := by
  by_cases admitted : index < packed.used
  · exact refines.read_eq index admitted
  · have typedNotAdmitted : ¬ index < typed.used := by
      rw [← refines.used_eq]
      exact admitted
    simp [PackedResultStore.readAdmitted?, ResultStore.readAdmitted?,
      admitted, typedNotAdmitted]

/-- Paired successful allocations establish the initial packed-to-typed
refinement relation. -/
theorem of_allocations {base : UInt64} {capacity : Nat}
    {packed : PackedResultStore} {typed : ResultStore}
    (packedAllocated : PackedResultStore.allocate? base capacity = some packed)
    (typedAllocated : ResultStore.allocate? base capacity = some typed) :
    RefinesTyped packed typed := by
  have packedWellFormed :=
    PackedResultStore.allocate?_wellFormed packedAllocated
  have typedWellFormed := ResultStore.allocate?_wellFormed typedAllocated
  rcases PackedResultStore.allocate?_shape packedAllocated with
    ⟨packedBase, packedCapacity, _packedBytes, packedUsed⟩
  rcases ResultStore.allocate?_shape typedAllocated with
    ⟨typedBase, typedCapacity, typedUsed⟩
  refine
    { packedWellFormed
      typedWellFormed
      base_eq := ?_
      capacity_eq := ?_
      used_eq := ?_
      read_eq := ?_ }
  · rw [packedBase, typedBase]
  · rw [packedCapacity, typedCapacity]
  · rw [packedUsed, typedUsed]
  · intro index admitted
    rw [packedUsed] at admitted
    omega

/-- Synchronized successful writes preserve the complete packed-to-typed
refinement relation. -/
theorem writeNext {packed packedNext : PackedResultStore}
    {typed typedNext : ResultStore} {resultId : UInt32}
    (refines : RefinesTyped packed typed)
    (packedAccepted : packed.writeNext? resultId = some packedNext)
    (typedAccepted : typed.writeNext? resultId = some typedNext) :
    RefinesTyped packedNext typedNext := by
  have packedShape := PackedResultStore.writeNext?_shape packedAccepted
  have typedCapacity := ResultStore.writeNext?_capacity typedAccepted
  have typedUsed := ResultStore.writeNext?_used typedAccepted
  refine
    { packedWellFormed :=
        PackedResultStore.writeNext?_wellFormed
          refines.packedWellFormed packedAccepted
      typedWellFormed :=
        ResultStore.writeNext?_wellFormed refines.typedWellFormed typedAccepted
      base_eq := ?_
      capacity_eq := ?_
      used_eq := ?_
      read_eq := ?_ }
  · rw [packedShape.1, typedWriteNext?_base typedAccepted]
    exact refines.base_eq
  · rw [packedShape.2.1, typedCapacity]
    exact refines.capacity_eq
  · rw [packedShape.2.2.2, typedUsed, refines.used_eq]
  · intro index admittedNext
    by_cases admittedBefore : index < packed.used
    · have typedBefore : index < typed.used := by
        rw [← refines.used_eq]
        exact admittedBefore
      rw [PackedResultStore.readAdmitted?_writeNext_before
        packedAccepted admittedBefore]
      rw [typedReadAdmitted?_writeNext_before refines.typedWellFormed
        typedAccepted typedBefore]
      exact refines.read_eq index admittedBefore
    · have atFrontier : index = packed.used := by
        rw [packedShape.2.2.2] at admittedNext
        omega
      subst index
      rw [PackedResultStore.readAdmitted?_writeNext_at packedAccepted]
      rw [refines.used_eq]
      exact (typedReadAdmitted?_writeNext_at
        refines.typedWellFormed typedAccepted).symm

end RefinesTyped

/-! ## Byte-packed replay refinement -/

namespace PackedReplay

open Mettapedia.GSLT.LanguageDef.M0GCAddressedReplayControlMachine
open Mettapedia.GSLT.LanguageDef.M0GCLogicalReplay
open Mettapedia.GSLT.LanguageDef.M0GCPhysicalTemplateAdequacy

/-- Resolve chronological premise references through byte-packed checked
reads. -/
def resolveAdmitted? (store : PackedResultStore) :
    List UInt32 → Option (List UInt32)
  | [] => some []
  | reference :: references => do
      let resultId ← store.readAdmitted? reference.toNat
      let results ← resolveAdmitted? store references
      some (resultId :: results)

/-- Packed and typed premise resolution are extensionally identical whenever
their stores are related. -/
theorem resolveAdmitted?_eq_typed {packed : PackedResultStore}
    {typed : ResultStore} (refines : RefinesTyped packed typed)
    (references : List UInt32) :
    resolveAdmitted? packed references =
      M0GCAddressedReplayControlMachine.resolveAdmitted? typed references := by
  induction references with
  | nil => rfl
  | cons reference references inductionHypothesis =>
      simp [resolveAdmitted?,
        M0GCAddressedReplayControlMachine.resolveAdmitted?,
        RefinesTyped.readAdmitted?_eq refines reference.toNat,
        inductionHypothesis]

/-- One record transition using the byte-packed result region.  Logical rule
validation is deliberately shared with the independently qualified addressed
checker; only premise storage and the final chronological write are refined. -/
def replayRecord? (profile : RuntimeProfile) (tables : RuleTables)
    (certificate : Certificate) (terms : TermState) (fuel : Nat)
    (store : PackedResultStore) (proof : ProofNode) :
    Option PackedResultStore := do
  let resultId ← recordResult? profile tables certificate terms fuel
    (resolveAdmitted? store) proof
  store.writeNext? resultId

/-- Pointwise lifting of a state relation through partial computations. -/
def OptionRefines {Source Target : Type*}
    (relation : Source → Target → Prop) :
    Option Source → Option Target → Prop
  | none, none => True
  | some source, some target => relation source target
  | _, _ => False

/-- One byte-packed replay transition refines the typed addressed transition
in both success and rejection behavior. -/
theorem replayRecord?_refines_typed
    (profile : RuntimeProfile) (tables : RuleTables)
    (certificate : Certificate) (terms : TermState) (fuel : Nat)
    (packed : PackedResultStore) (typed : ResultStore) (proof : ProofNode)
    (refines : RefinesTyped packed typed) :
    OptionRefines RefinesTyped
      (replayRecord? profile tables certificate terms fuel packed proof)
      (M0GCAddressedReplayControlMachine.replayRecord?
        profile tables certificate terms fuel typed proof) := by
  have resolverEq :
      resolveAdmitted? packed =
        M0GCAddressedReplayControlMachine.resolveAdmitted? typed := by
    funext references
    exact resolveAdmitted?_eq_typed refines references
  unfold replayRecord?
    M0GCAddressedReplayControlMachine.replayRecord?
  rw [resolverEq]
  cases validation : recordResult? profile tables certificate terms fuel
      (M0GCAddressedReplayControlMachine.resolveAdmitted? typed) proof with
  | none => simp [OptionRefines]
  | some resultId =>
      dsimp
      by_cases packedRoom : packed.used < packed.capacity
      · have typedRoom : typed.used < typed.cells.size := by
          rw [← refines.used_eq, ← refines.capacity_eq]
          exact packedRoom
        obtain ⟨packedNext, packedAccepted⟩ :=
          PackedResultStore.writeNext?_exists_of_room packed resultId
            refines.packedWellFormed packedRoom
        obtain ⟨typedNext, typedAccepted⟩ :=
          ResultStore.writeNext?_exists_of_room typed resultId
            refines.typedWellFormed typedRoom
        rw [packedAccepted, typedAccepted]
        exact RefinesTyped.writeNext refines packedAccepted typedAccepted
      · have typedNoRoom : ¬ typed.used < typed.cells.size := by
          rw [← refines.used_eq, ← refines.capacity_eq]
          exact packedRoom
        simp [PackedResultStore.writeNext?, ResultStore.writeNext?,
          packedRoom, typedNoRoom, OptionRefines]

/-- Any successful byte-packed record advances the result frontier by exactly
one without changing capacity. -/
theorem replayRecord?_shape
    {profile : RuntimeProfile} {tables : RuleTables}
    {certificate : Certificate} {terms : TermState} {fuel : Nat}
    {store next : PackedResultStore} {proof : ProofNode}
    (accepted :
      replayRecord? profile tables certificate terms fuel store proof =
        some next) :
    next.capacity = store.capacity ∧ next.used = store.used + 1 := by
  unfold replayRecord? at accepted
  rcases Option.bind_eq_some_iff.mp accepted with
    ⟨resultId, _validated, writeAccepted⟩
  have shape := PackedResultStore.writeNext?_shape writeAccepted
  exact ⟨shape.2.1, shape.2.2.2⟩

/-- Complete chronological replay through the byte-packed result region. -/
def replayLoop (profile : RuntimeProfile) (tables : RuleTables)
    (certificate : Certificate) (terms : TermState) (fuel : Nat) :
    List ProofNode → PackedResultStore → Option PackedResultStore
  | [], store => some store
  | proof :: proofs, store => do
      let next ← replayRecord? profile tables certificate terms fuel
        store proof
      replayLoop profile tables certificate terms fuel proofs next

/-- Sufficient capacity makes complete byte-packed replay refine complete
typed addressed replay, including identical rejection behavior. -/
theorem replayLoop_refines_typed_of_capacity
    (profile : RuntimeProfile) (tables : RuleTables)
    (certificate : Certificate) (terms : TermState) (fuel : Nat)
    (proofs : List ProofNode) (packed : PackedResultStore)
    (typed : ResultStore) (refines : RefinesTyped packed typed)
    (enough : packed.used + proofs.length ≤ packed.capacity) :
    OptionRefines RefinesTyped
      (replayLoop profile tables certificate terms fuel proofs packed)
      (M0GCAddressedReplayControlMachine.replayLoop
        profile tables certificate terms fuel proofs typed) := by
  induction proofs generalizing packed typed with
  | nil =>
      simpa [replayLoop,
        M0GCAddressedReplayControlMachine.replayLoop, OptionRefines]
  | cons proof proofs inductionHypothesis =>
      simp only [replayLoop,
        M0GCAddressedReplayControlMachine.replayLoop]
      have stepRefines := replayRecord?_refines_typed
        profile tables certificate terms fuel packed typed proof refines
      cases packedStep :
          replayRecord? profile tables certificate terms fuel packed proof with
      | none =>
          cases typedStep :
              M0GCAddressedReplayControlMachine.replayRecord?
                profile tables certificate terms fuel typed proof with
          | none => simp [OptionRefines]
          | some typedNext =>
              simp [packedStep, typedStep, OptionRefines] at stepRefines
      | some packedNext =>
          cases typedStep :
              M0GCAddressedReplayControlMachine.replayRecord?
                profile tables certificate terms fuel typed proof with
          | none =>
              simp [packedStep, typedStep, OptionRefines] at stepRefines
          | some typedNext =>
              have nextRefines : RefinesTyped packedNext typedNext := by
                simpa [packedStep, typedStep, OptionRefines] using stepRefines
              have packedShape := replayRecord?_shape packedStep
              have enoughTail :
                  packedNext.used + proofs.length ≤ packedNext.capacity := by
                rw [packedShape.1, packedShape.2]
                simp only [List.length_cons] at enough
                omega
              exact inductionHypothesis packedNext typedNext nextRefines
                enoughTail

end PackedReplay

/-! ## Executable scalar and allocation discriminators -/

namespace Canary

open Mettapedia.GSLT.LanguageDef.M0GCLogicalReplayCanary

def zeroBytes : Array UInt8 := #[0, 0, 0, 0, 0, 0, 0, 0]

def firstStored : Array UInt8 :=
  #[68, 51, 34, 17, 0, 0, 0, 0]

/-- Positive little-endian discriminator. -/
theorem one_scalar_stored :
    storeUInt32LE? zeroBytes 0 0x11223344 = some firstStored := by
  decide

theorem one_scalar_read :
    loadUInt32LE? firstStored 0 = some 0x11223344 := by
  decide

/-- Negative partial-write discriminator. -/
theorem partial_scalar_rejected :
    storeUInt32LE? #[0, 0, 0] 0 7 = none := by
  decide

def emptyTwoCell : PackedResultStore :=
  { base := 100, capacity := 2, bytes := zeroBytes, used := 0 }

theorem two_cell_allocation :
    PackedResultStore.allocate? 100 2 = some emptyTwoCell := by
  decide

/-- Negative alignment discriminator. -/
theorem unaligned_allocation_rejected :
    PackedResultStore.allocate? 101 1 = none := by
  decide

/-- Negative full-region overflow discriminator at an aligned base. -/
theorem overflowing_allocation_rejected :
    PackedResultStore.allocate?
        (UInt64.ofNat (UInt64.size - resultCellBytes)) 1 = none := by
  decide

def packedEmptyOneSlot : PackedResultStore :=
  { base := 100, capacity := 1, bytes := #[0, 0, 0, 0], used := 0 }

def packedAcceptedOneSlot : PackedResultStore :=
  { base := 100, capacity := 1, bytes := #[2, 0, 0, 0], used := 1 }

def packedZeroSlot : PackedResultStore :=
  { base := 100, capacity := 0, bytes := #[], used := 0 }

/-- Negative initialized-prefix discriminator: allocated but unwritten bytes
are not admitted results. -/
theorem unwritten_cell_rejected :
    packedEmptyOneSlot.readAdmitted? 0 = none := by
  decide

/-- The byte-packed initial store is related to the typed addressed canary by
the allocation theorem, not by a post-hoc equality assertion. -/
theorem initial_store_refines :
    RefinesTyped packedEmptyOneSlot
      M0GCAddressedReplayControlMachine.Canary.emptyOneSlot := by
  exact RefinesTyped.of_allocations (base := 100) (capacity := 1)
    (by decide) (by decide)

theorem zero_store_refines :
    RefinesTyped packedZeroSlot
      M0GCAddressedReplayControlMachine.Canary.zeroSlot := by
  exact RefinesTyped.of_allocations (base := 100) (capacity := 0)
    (by decide) (by decide)

/-- The pair record's logical validation is inherited from the typed checker
through the proved premise-resolver equality. -/
theorem pair_record_validation_of_refines
    {packed : PackedResultStore} {typed : ResultStore}
    (refines : RefinesTyped packed typed) :
    M0GCAddressedReplayControlMachine.recordResult? profile
      M0GCAddressedReplayControlMachine.Canary.tables certificate termState
      M0GCNativeReplayAdequacy.Canary.canaryFuel
        (PackedReplay.resolveAdmitted? packed) proofNode =
          some proofNode.resultTerm := by
  have resolverEq :
      PackedReplay.resolveAdmitted? packed =
        M0GCAddressedReplayControlMachine.resolveAdmitted? typed := by
    funext references
    exact PackedReplay.resolveAdmitted?_eq_typed refines references
  rw [resolverEq]
  exact M0GCAddressedReplayControlMachine.Canary.pair_record_validation typed

/-- Positive end-to-end discriminator: the qualified pair record is replayed
into the exact four-byte little-endian result cell. -/
theorem packed_pair_record_accepts :
    PackedReplay.replayRecord? profile
      M0GCAddressedReplayControlMachine.Canary.tables certificate termState
      M0GCNativeReplayAdequacy.Canary.canaryFuel packedEmptyOneSlot proofNode =
        some packedAcceptedOneSlot := by
  unfold PackedReplay.replayRecord?
  rw [pair_record_validation_of_refines initial_store_refines]
  change packedEmptyOneSlot.writeNext? 2 = some packedAcceptedOneSlot
  decide

/-- The one-record packed loop has the same positive result. -/
theorem packed_pair_loop_accepts :
    PackedReplay.replayLoop profile
      M0GCAddressedReplayControlMachine.Canary.tables certificate termState
      M0GCNativeReplayAdequacy.Canary.canaryFuel certificate.proofs
        packedEmptyOneSlot = some packedAcceptedOneSlot := by
  change PackedReplay.replayLoop profile
    M0GCAddressedReplayControlMachine.Canary.tables certificate termState
      M0GCNativeReplayAdequacy.Canary.canaryFuel [proofNode]
        packedEmptyOneSlot = some packedAcceptedOneSlot
  rw [PackedReplay.replayLoop, packed_pair_record_accepts]
  rfl

/-- Negative capacity discriminator: semantic validity cannot grow a packed
zero-capacity region. -/
theorem packed_zero_capacity_rejected :
    PackedReplay.replayRecord? profile
      M0GCAddressedReplayControlMachine.Canary.tables certificate termState
      M0GCNativeReplayAdequacy.Canary.canaryFuel packedZeroSlot proofNode =
        none := by
  unfold PackedReplay.replayRecord?
  rw [pair_record_validation_of_refines zero_store_refines]
  change packedZeroSlot.writeNext? 2 = none
  decide

end Canary

#print axioms uint32Bytes_eq_encode
#print axioms storeUInt32LE?_size
#print axioms loadUInt32LE?_of_storeUInt32LE?
#print axioms getElem?_of_storeUInt32LE?_outside
#print axioms loadUInt32LE?_of_storeUInt32LE?_before
#print axioms PackedResultStore.allocate?_wellFormed
#print axioms PackedResultStore.allocate?_shape
#print axioms PackedResultStore.cellAddress?_some_toNat
#print axioms PackedResultStore.cellAddress?_exists
#print axioms PackedResultStore.nextField_complete
#print axioms PackedResultStore.writeNext?_exists_of_room
#print axioms PackedResultStore.writeNext?_shape
#print axioms PackedResultStore.writeNext?_wellFormed
#print axioms PackedResultStore.readAdmitted?_writeNext_at
#print axioms PackedResultStore.readAdmitted?_writeNext_before
#print axioms typedReadAdmitted?_writeNext_at
#print axioms typedReadAdmitted?_writeNext_before
#print axioms RefinesTyped.of_allocations
#print axioms RefinesTyped.writeNext
#print axioms PackedReplay.resolveAdmitted?_eq_typed
#print axioms PackedReplay.replayRecord?_refines_typed
#print axioms PackedReplay.replayLoop_refines_typed_of_capacity
#print axioms Canary.one_scalar_stored
#print axioms Canary.one_scalar_read
#print axioms Canary.partial_scalar_rejected
#print axioms Canary.two_cell_allocation
#print axioms Canary.unaligned_allocation_rejected
#print axioms Canary.overflowing_allocation_rejected
#print axioms Canary.unwritten_cell_rejected
#print axioms Canary.initial_store_refines
#print axioms Canary.zero_store_refines
#print axioms Canary.pair_record_validation_of_refines
#print axioms Canary.packed_pair_record_accepts
#print axioms Canary.packed_pair_loop_accepts
#print axioms Canary.packed_zero_capacity_rejected

end Mettapedia.GSLT.LanguageDef.M0GCBytePackedResultStoreRefinement
