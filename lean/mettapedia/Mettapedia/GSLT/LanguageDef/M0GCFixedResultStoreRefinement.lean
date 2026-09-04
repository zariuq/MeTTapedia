import Mettapedia.GSLT.LanguageDef.M0GCNativeReplayAdequacy
import Mettapedia.GSLT.LanguageDef.M0GCWordAddressedMemory

/-!
# Fixed-capacity addressed result storage for the M0GC checker

The M0GC replay core needs one 32-bit result-term identifier for every
admitted proof record.  This module replaces allocation-by-`Array.push` with
a fixed-capacity region, an explicit used count, checked 64-bit cell
addresses, and in-place-style indexed updates.  Its observable prefix is
proved to refine the existing source-level `NativeProofState` exactly.

Maturity boundary: this is a fully connected intermediate proof of concept.
The functional `Array.set` models mutation of typed 32-bit cells, but this is
not yet a byte-packed ABI, pointer-provenance model, Pancake or Clight
semantics, generated C, compiler correctness, object code, an OS, or hardware.
Later target memories must refine this addressed store and its prefix
observation; they must not inherit this Lean representation as an ABI.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.M0GCFixedResultStoreRefinement

open Mettapedia.GSLT.LanguageDef.M0GCNativeReplayAdequacy

/-! ## Addressed fixed-capacity store -/

/-- The ABI width of one stored M0GC result identifier. -/
def resultCellBytes : Nat := 4

/-- A fixed allocation for chronological result identifiers.

`cells.size` is the allocation capacity.  `used` is the initialized prefix;
no successful update changes the base or the capacity. -/
structure ResultStore where
  base : UInt64
  cells : Array UInt32
  used : Nat
deriving DecidableEq, Repr

namespace ResultStore

/-- Reachable-store invariant: the initialized prefix fits in the allocation,
and the complete allocation has a non-wrapping 64-bit byte range. -/
def WellFormed (store : ResultStore) : Prop :=
  store.used ≤ store.cells.size ∧
    store.base.toNat + resultCellBytes * store.cells.size < UInt64.size

/-- Allocate and zero-initialize a fixed number of result cells only when the
complete byte range is representable without address wraparound. -/
def allocate? (base : UInt64) (capacity : Nat) : Option ResultStore :=
  if _addressable :
      base.toNat + resultCellBytes * capacity < UInt64.size then
    some
      { base := base
        cells := Array.replicate capacity 0
        used := 0 }
  else
    none

/-- The initialized chronological prefix observed by the source model. -/
def snapshot (store : ResultStore) : Array UInt32 :=
  store.cells.extract 0 store.used

/-- A well-formed store exposes exactly `used` initialized result cells. -/
theorem snapshot_size (store : ResultStore) (wellFormed : store.WellFormed) :
    store.snapshot.size = store.used := by
  have minUsed : min store.used store.cells.size = store.used :=
    min_eq_left wellFormed.1
  simp [snapshot, minUsed]

/-- Forget the fixed allocation while preserving exactly the initialized
source-level result sequence. -/
def toNative (store : ResultStore) : NativeProofState :=
  { resultIds := store.snapshot }

/-- Compute the byte address of a physical result cell, checking both the
allocation bound and unsigned-address representability. -/
def cellAddress? (store : ResultStore) (index : Nat) : Option UInt64 :=
  if _inBounds : index < store.cells.size then
    if _addressable :
        store.base.toNat + resultCellBytes * index < UInt64.size then
      some
        (UInt64.ofNatLT
          (store.base.toNat + resultCellBytes * index) _addressable)
    else
      none
  else
    none

/-- A successful cell-address calculation has its ordinary mathematical byte
address; it is never a wrapped modular result. -/
theorem cellAddress?_some_toNat {store : ResultStore} {index : Nat}
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

/-- Every allocated cell of a well-formed store has a checked byte address. -/
theorem cellAddress?_exists (store : ResultStore) (index : Nat)
    (wellFormed : store.WellFormed) (inBounds : index < store.cells.size) :
    ∃ address,
      store.cellAddress? index = some address ∧
        address.toNat = store.base.toNat + resultCellBytes * index := by
  have addressable :
      store.base.toNat + resultCellBytes * index < UInt64.size := by
    rcases wellFormed with ⟨_, allocationAddressable⟩
    unfold resultCellBytes at allocationAddressable ⊢
    omega
  let address := UInt64.ofNatLT
    (store.base.toNat + resultCellBytes * index) addressable
  refine ⟨address, ?_, ?_⟩
  · simp [cellAddress?, inBounds, addressable, address]
  · exact UInt64.toNat_ofNatLT

/-- Read an initialized result cell.  The address check remains an executable
part of the operation even though the present semantic backing is an array. -/
def readAdmitted? (store : ResultStore) (index : Nat) : Option UInt32 :=
  if _admitted : index < store.used then do
    let _address ← store.cellAddress? index
    store.cells[index]?
  else
    none

/-- Checked physical reads expose exactly the corresponding initialized-prefix
entry of the source model. -/
theorem readAdmitted?_eq_snapshot (store : ResultStore) (index : Nat)
    (wellFormed : store.WellFormed) :
    store.readAdmitted? index = store.snapshot[index]? := by
  have usedFits : store.used ≤ store.cells.size := wellFormed.1
  have minUsed : min store.used store.cells.size = store.used :=
    min_eq_left usedFits
  by_cases admitted : index < store.used
  · have inBounds : index < store.cells.size :=
      lt_of_lt_of_le admitted usedFits
    obtain ⟨address, addressEq, _⟩ :=
      cellAddress?_exists store index wellFormed inBounds
    simp [readAdmitted?, admitted, addressEq, snapshot, minUsed]
  · simp [readAdmitted?, admitted, snapshot, minUsed]

/-- Write the next chronological result into its preallocated cell.  This
operation never grows the backing array. -/
def writeNext? (store : ResultStore) (resultId : UInt32) : Option ResultStore :=
  if room : store.used < store.cells.size then
    match store.cellAddress? store.used with
    | none => none
    | some _address =>
        some
          { store with
            cells := store.cells.set store.used resultId room
            used := store.used + 1 }
  else
    none

/-! ## Allocation and write refinement -/

theorem allocate?_wellFormed {base : UInt64} {capacity : Nat}
    {store : ResultStore}
    (allocated : allocate? base capacity = some store) :
    store.WellFormed := by
  unfold allocate? at allocated
  split at allocated
  next addressable =>
    simp only [Option.some.injEq] at allocated
    subst store
    simp [WellFormed, addressable]
  next overflow => contradiction

/-- Successful allocation has exactly the requested base, capacity, and empty
initialized prefix. -/
theorem allocate?_shape {base : UInt64} {capacity : Nat}
    {store : ResultStore}
    (allocated : allocate? base capacity = some store) :
    store.base = base ∧ store.cells.size = capacity ∧ store.used = 0 := by
  unfold allocate? at allocated
  split at allocated
  next addressable =>
    simp only [Option.some.injEq] at allocated
    subst store
    simp
  next overflow => contradiction

theorem allocate?_snapshot_empty {base : UInt64} {capacity : Nat}
    {store : ResultStore}
    (allocated : allocate? base capacity = some store) :
    store.snapshot = #[] := by
  unfold allocate? at allocated
  split at allocated
  next addressable =>
    simp only [Option.some.injEq] at allocated
    subst store
    simp [snapshot]
  next overflow => contradiction

/-- Updating precisely the first uninitialized cell extends the observed
prefix by one value.  This is the central fixed-store/functional-state law. -/
theorem extract_set_at_end {alpha : Type*} (cells : Array alpha) (used : Nat)
    (value : alpha) (room : used < cells.size) :
    (cells.set used value room).extract 0 (used + 1) =
      (cells.extract 0 used).push value := by
  have minUsed : min used cells.size = used := by omega
  have minNext : min (used + 1) cells.size = used + 1 := by omega
  apply Array.ext_getElem?
  intro index
  rw [Array.getElem?_extract, Array.getElem?_push]
  simp only [Array.size_extract, Array.size_set, minUsed, minNext,
    Nat.sub_zero]
  rw [Array.getElem?_set room, Array.getElem?_extract]
  simp only [minUsed, Nat.sub_zero, Nat.zero_add]
  by_cases beforeEnd : index < used
  · have usedNe : used ≠ index := by omega
    have indexNe : index ≠ used := by omega
    have beforeNext : index < used + 1 := by omega
    simp [beforeEnd, usedNe, indexNe, beforeNext]
  · by_cases atEnd : index = used
    · subst index
      simp
    · have afterNext : ¬ index < used + 1 := by omega
      simp [beforeEnd, atEnd, afterNext]

/-- A successful fixed-store write has exactly the source model's `push`
observation. -/
theorem writeNext?_snapshot {store next : ResultStore} {resultId : UInt32}
    (accepted : store.writeNext? resultId = some next) :
    next.snapshot = store.snapshot.push resultId := by
  by_cases room : store.used < store.cells.size
  · cases addressResult : store.cellAddress? store.used with
    | none =>
        simp [writeNext?, room, addressResult] at accepted
    | some address =>
        simp [writeNext?, room, addressResult] at accepted
        subst next
        exact extract_set_at_end store.cells store.used resultId room
  · simp [writeNext?, room] at accepted

/-- Successful fixed-store writes preserve the reachability invariant. -/
theorem writeNext?_wellFormed {store next : ResultStore} {resultId : UInt32}
    (wellFormed : store.WellFormed)
    (accepted : store.writeNext? resultId = some next) :
    next.WellFormed := by
  by_cases room : store.used < store.cells.size
  · cases addressResult : store.cellAddress? store.used with
    | none =>
        simp [writeNext?, room, addressResult] at accepted
    | some address =>
        simp [writeNext?, room, addressResult] at accepted
        subst next
        rcases wellFormed with ⟨usedFits, addressable⟩
        constructor
        · simp only [Array.size_set]
          omega
        · simpa using addressable
  · simp [writeNext?, room] at accepted

/-- Successful writes do not allocate or resize the result region. -/
theorem writeNext?_capacity {store next : ResultStore} {resultId : UInt32}
    (accepted : store.writeNext? resultId = some next) :
    next.cells.size = store.cells.size := by
  by_cases room : store.used < store.cells.size
  · cases addressResult : store.cellAddress? store.used with
    | none =>
        simp [writeNext?, room, addressResult] at accepted
    | some address =>
        simp [writeNext?, room, addressResult] at accepted
        subst next
        simp
  · simp [writeNext?, room] at accepted

/-- Every successful write advances the initialized prefix by exactly one
cell. -/
theorem writeNext?_used {store next : ResultStore} {resultId : UInt32}
    (accepted : store.writeNext? resultId = some next) :
    next.used = store.used + 1 := by
  by_cases room : store.used < store.cells.size
  · cases addressResult : store.cellAddress? store.used with
    | none =>
        simp [writeNext?, room, addressResult] at accepted
    | some address =>
        simp [writeNext?, room, addressResult] at accepted
        subst next
        rfl
  · simp [writeNext?, room] at accepted

/-- A well-formed store with available capacity can always perform its next
addressed write. -/
theorem writeNext?_exists_of_room (store : ResultStore) (resultId : UInt32)
    (wellFormed : store.WellFormed)
    (room : store.used < store.cells.size) :
    ∃ next, store.writeNext? resultId = some next := by
  obtain ⟨address, addressEq, _⟩ :=
    cellAddress?_exists store store.used wellFormed room
  refine ⟨
    { store with
      cells := store.cells.set store.used resultId room
      used := store.used + 1 }, ?_⟩
  simp [writeNext?, room, addressEq]

/-- The target-addressed write refines the allocation-free native replay
state exactly. -/
theorem writeNext?_toNative {store next : ResultStore} {resultId : UInt32}
    (accepted : store.writeNext? resultId = some next) :
    next.toNative =
      { resultIds := store.toNative.resultIds.push resultId } := by
  simp only [toNative]
  rw [writeNext?_snapshot accepted]

/-- With available capacity, the complete addressed-write observation is
exactly one source-level chronological `push`. -/
theorem map_toNative_writeNext_of_room (store : ResultStore)
    (resultId : UInt32) (wellFormed : store.WellFormed)
    (room : store.used < store.cells.size) :
    Option.map toNative (store.writeNext? resultId) =
      some { resultIds := store.toNative.resultIds.push resultId } := by
  obtain ⟨next, accepted⟩ :=
    writeNext?_exists_of_room store resultId wellFormed room
  rw [accepted]
  simp [writeNext?_toNative accepted]

/-! ## Positive and negative discriminators -/

namespace Canary

def emptyTwoSlot : ResultStore :=
  { base := 100, cells := #[0, 0], used := 0 }

def oneResult : ResultStore :=
  { base := 100, cells := #[7, 0], used := 1 }

def twoResults : ResultStore :=
  { base := 100, cells := #[7, 9], used := 2 }

theorem two_slot_allocation :
    allocate? 100 2 = some emptyTwoSlot := by
  decide

/-- Positive discriminator: sequential writes use the fixed cells and expose
the same chronological result sequence as the source model. -/
theorem two_results_written :
    (do
      let first ← emptyTwoSlot.writeNext? 7
      first.writeNext? 9) = some twoResults := by
  decide

theorem two_results_snapshot :
    twoResults.snapshot = #[7, 9] := by
  decide

def zeroSlot : ResultStore :=
  { base := 0, cells := #[], used := 0 }

/-- Negative capacity discriminator: a valid identifier cannot grow a
zero-capacity store. -/
theorem zero_capacity_rejected :
    zeroSlot.writeNext? 7 = none := by
  decide

/-- Negative address discriminator: an allocation whose four-byte cell would
cross the finite-word boundary is rejected. -/
theorem overflowing_allocation_rejected :
    allocate? (UInt64.ofNat (UInt64.size - 1)) 1 = none := by
  decide

end Canary

#print axioms cellAddress?_some_toNat
#print axioms cellAddress?_exists
#print axioms snapshot_size
#print axioms readAdmitted?_eq_snapshot
#print axioms allocate?_wellFormed
#print axioms allocate?_shape
#print axioms allocate?_snapshot_empty
#print axioms extract_set_at_end
#print axioms writeNext?_snapshot
#print axioms writeNext?_wellFormed
#print axioms writeNext?_capacity
#print axioms writeNext?_used
#print axioms writeNext?_exists_of_room
#print axioms writeNext?_toNative
#print axioms map_toNative_writeNext_of_room
#print axioms Canary.two_slot_allocation
#print axioms Canary.two_results_written
#print axioms Canary.zero_capacity_rejected
#print axioms Canary.overflowing_allocation_rejected

end ResultStore

end Mettapedia.GSLT.LanguageDef.M0GCFixedResultStoreRefinement
