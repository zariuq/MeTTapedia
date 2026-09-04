import Mettapedia.GSLT.LanguageDef.M0GCDisjointCertificateResultMemory

/-!
# A checked, width-typed byte-machine IR for M0GC lowering

This module defines the first low-level instruction language below the unified
M0GC reference checker.  Registers are intrinsically separated into byte,
16-bit, 32-bit, and 64-bit data-word banks, plus distinct 64-bit address and
Boolean banks.  Memory operations use
physical `UInt64` addresses, checked addition, complete-range checks, and
explicit little-endian loads and stores.  Execution has three terminal
observations: Boolean return, explicit fault, or continued execution.  There
is no undefined-behavior outcome.

The machine is deliberately smaller than C.  It supplies only constants,
copies, checked address addition, equality/order tests, byte and word loads
and stores, branches, jumps, and Boolean returns.  This makes the physical
obligations of the checker visible before a C-facing syntax or compiler is
selected.

Maturity boundary: this is a connected intermediate proof of concept, not an
endgame ABI or production checker.  Separate realization modules now lower
header parsing and zero-copy table-view preparation into this instruction
set.  Indexed record decoding, checksum replay, matching, and rule validation
remain to be connected; none of those operations is hidden behind an opaque
instruction here.  Register functions and persistent Lean arrays are
specification representations.  There is not yet generated StructuredC,
Clight, Pancake, portable C, verified compilation, object code, an OS,
hardware, or the official MM0/MMB format.  Later layers must refine this
machine and preserve its distinct reject/fault behavior.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.M0GCCheckedByteMachineIR

open Mettapedia.GSLT.LanguageDef.CompiledPlanWireFormat
open Mettapedia.GSLT.LanguageDef.M0GCWordAddressedMemory
open Mettapedia.GSLT.LanguageDef.M0GCBoundedByteMemory
open Mettapedia.GSLT.LanguageDef.M0GCBytePackedResultStoreRefinement
open Mettapedia.GSLT.LanguageDef.M0GCDisjointCertificateResultMemory

/-! ## Checked physical byte memory -/

/-- One finite byte allocation at a physical 64-bit base address.  The
executable operations remain total even for a malformed value; `WellFormed`
identifies allocations whose complete exclusive bound is representable. -/
structure ByteMemory where
  base : UInt64
  cells : Array UInt8
deriving DecidableEq, Repr

namespace ByteMemory

/-- The complete allocation lies strictly below the unrepresentable
exclusive address `2^64`.  This matches the conservative M0GC allocation
discipline used by the reference checker. -/
def WellFormed (memory : ByteMemory) : Prop :=
  memory.base.toNat + memory.cells.size < UInt64.size

/-- Admit an allocation only when its complete bound is representable. -/
def allocate? (base : UInt64) (cells : Array UInt8) : Option ByteMemory :=
  if base.toNat + cells.size < UInt64.size then
    some { base, cells }
  else
    none

theorem allocate?_wellFormed {base : UInt64} {cells : Array UInt8}
    {memory : ByteMemory}
    (allocated : allocate? base cells = some memory) :
    memory.WellFormed := by
  unfold allocate? at allocated
  split at allocated
  next fits =>
    simp only [Option.some.injEq] at allocated
    subst memory
    exact fits
  next overflow => contradiction

/-- Forget the proof-only allocation descriptors of the unified checker while
retaining the exact physical base and backing bytes. -/
def ofCheckerMemory (memory : CheckerMemory) : ByteMemory :=
  { base := memory.base, cells := memory.cells }

/-- Compile a byte list into one physically based allocation. -/
def ofList (base : UInt64) (bytes : List UInt8) : ByteMemory :=
  { base, cells := bytes.toArray }

/-- Forget the physical base after a checked address has been resolved to an
array offset.  This reuses the already-qualified bounded field decoders
without conflating physical addresses and relative array indices. -/
def toNeutralRegion (memory : ByteMemory) : ByteRegion where
  cells := memory.cells
  base := 0
  extent := memory.cells.size
  inBounds := by simp

@[simp] theorem toNeutralRegion_ofList (base : UInt64) (bytes : List UInt8) :
    (ofList base bytes).toNeutralRegion = ByteRegion.ofList bytes := by
  simp [ofList, toNeutralRegion, ByteRegion.ofList]

theorem ofCheckerMemory_wellFormed (memory : CheckerMemory)
    (wellFormed : memory.WellFormed) :
    (ofCheckerMemory memory).WellFormed := by
  exact wellFormed.addressable

/-- Resolve a complete half-open physical address range to an array offset.
The end address is formed by checked unsigned addition before array bounds
are consulted. -/
def rangeOffset? (memory : ByteMemory) (address width : UInt64) : Option Nat :=
  match checkedAdd address width with
  | none => none
  | some addressEnd =>
      if _inside : memory.base.toNat ≤ address.toNat ∧
          addressEnd.toNat ≤ memory.base.toNat + memory.cells.size then
        some (address.toNat - memory.base.toNat)
      else
        none

theorem rangeOffset?_some_bounds
    {memory : ByteMemory} {address width : UInt64} {offset : Nat}
    (resolved : memory.rangeOffset? address width = some offset) :
    offset = address.toNat - memory.base.toNat ∧
      memory.base.toNat ≤ address.toNat ∧
      offset + width.toNat ≤ memory.cells.size := by
  cases addition : checkedAdd address width with
  | none =>
      simp [rangeOffset?, addition] at resolved
  | some addressEnd =>
      by_cases inside : memory.base.toNat ≤ address.toNat ∧
          addressEnd.toNat ≤ memory.base.toNat + memory.cells.size
      · simp [rangeOffset?, addition, inside] at resolved
        subst offset
        have addressEndValue :
            addressEnd.toNat = address.toNat + width.toNat :=
          checkedAdd_some_toNat addition
        refine ⟨rfl, inside.1, ?_⟩
        rw [addressEndValue] at inside
        omega
      · simp [rangeOffset?, addition, inside] at resolved

/-- A checked subfield beginning `shift` bytes into a resolved physical range
resolves to the correspondingly shifted array offset.  This is the reusable
bridge from one whole-record bounds proof to its explicit field loads. -/
theorem rangeOffset?_shifted
    {memory : ByteMemory} {address totalWidth : UInt64} {offset : Nat}
    {shift shiftedAddress fieldWidth : UInt64}
    (whole : memory.rangeOffset? address totalWidth = some offset)
    (shifted : checkedAdd address shift = some shiftedAddress)
    (covered : shift.toNat + fieldWidth.toNat ≤ totalWidth.toNat) :
    memory.rangeOffset? shiftedAddress fieldWidth =
      some (offset + shift.toNat) := by
  rcases rangeOffset?_some_bounds whole with
    ⟨offsetExact, baseBeforeAddress, wholeCovered⟩
  have shiftedNat := checkedAdd_some_toNat shifted
  cases wholeAddition : checkedAdd address totalWidth with
  | none =>
      simp [rangeOffset?, wholeAddition] at whole
  | some wholeEnd =>
      have wholeEndNat := checkedAdd_some_toNat wholeAddition
      have fieldFits :
          shiftedAddress.toNat + fieldWidth.toNat < UInt64.size := by
        have wholeEndFits := wholeEnd.toNat_lt_size
        omega
      let fieldEnd : UInt64 :=
        UInt64.ofNatLT
          (shiftedAddress.toNat + fieldWidth.toNat) fieldFits
      have fieldAddition :
          checkedAdd shiftedAddress fieldWidth = some fieldEnd := by
        exact checkedAdd_of_lt shiftedAddress fieldWidth fieldFits
      have fieldEndNat :
          fieldEnd.toNat = shiftedAddress.toNat + fieldWidth.toNat := by
        exact UInt64.toNat_ofNatLT
      have inside :
          memory.base.toNat ≤ shiftedAddress.toNat ∧
            fieldEnd.toNat ≤ memory.base.toNat + memory.cells.size := by
        constructor
        · omega
        · omega
      have offsetShift :
          shiftedAddress.toNat - memory.base.toNat =
            offset + shift.toNat := by
        omega
      simp [rangeOffset?, fieldAddition, inside, offsetShift]

/-- Shrinking a resolved range at the same physical address preserves its
array offset. -/
theorem rangeOffset?_smaller_width
    {memory : ByteMemory} {address totalWidth fieldWidth : UInt64}
    {offset : Nat}
    (whole : memory.rangeOffset? address totalWidth = some offset)
    (covered : fieldWidth.toNat ≤ totalWidth.toNat) :
    memory.rangeOffset? address fieldWidth = some offset := by
  have shifted := rangeOffset?_shifted whole (checkedAdd_zero address)
    (shift := 0) (fieldWidth := fieldWidth) (by simpa using covered)
  simpa using shifted

/-- A prefix width no larger than a resolved range has a representable
checked end address. -/
theorem exists_checkedAdd_of_rangeOffset
    {memory : ByteMemory} {address totalWidth fieldWidth : UInt64}
    {offset : Nat}
    (whole : memory.rangeOffset? address totalWidth = some offset)
    (covered : fieldWidth.toNat ≤ totalWidth.toNat) :
    ∃ fieldEnd, checkedAdd address fieldWidth = some fieldEnd := by
  cases wholeAddition : checkedAdd address totalWidth with
  | none =>
      simp [rangeOffset?, wholeAddition] at whole
  | some wholeEnd =>
      have wholeEndNat := checkedAdd_some_toNat wholeAddition
      have wholeEndFits := wholeEnd.toNat_lt_size
      have fieldFits : address.toNat + fieldWidth.toNat < UInt64.size := by
        omega
      exact
        ⟨UInt64.ofNatLT (address.toNat + fieldWidth.toNat) fieldFits,
          checkedAdd_of_lt address fieldWidth fieldFits⟩

/-- Construct a successful physical range resolution from its checked end
address and the complete allocation-bound proof. -/
theorem rangeOffset?_ofList_eq_some
    {base address width addressEnd : UInt64} {bytes : List UInt8}
    (addition : checkedAdd address width = some addressEnd)
    (inside : base.toNat ≤ address.toNat ∧
      addressEnd.toNat ≤ base.toNat + bytes.length) :
    (ofList base bytes).rangeOffset? address width =
      some (address.toNat - base.toNat) := by
  simp [rangeOffset?, addition, inside, ofList]

/-- Checked one-byte physical load. -/
def loadByte? (memory : ByteMemory) (address : UInt64) : Option UInt8 := do
  let offset ← memory.rangeOffset? address 1
  memory.cells[offset]?

/-- Checked complete two-byte little-endian load. -/
def loadUInt16LE? (memory : ByteMemory) (address : UInt64) : Option UInt16 := do
  let offset ← memory.rangeOffset? address 2
  ByteRegion.loadUInt16LE? memory.toNeutralRegion offset

/-- Checked one-byte physical store. -/
def storeByte? (memory : ByteMemory) (address : UInt64)
    (value : UInt8) : Option ByteMemory := do
  let offset ← memory.rangeOffset? address 1
  if offset < memory.cells.size then
    some { memory with cells := memory.cells.setIfInBounds offset value }
  else
    none

/-- Checked complete four-byte little-endian load. -/
def loadUInt32LE? (memory : ByteMemory) (address : UInt64) : Option UInt32 := do
  let offset ← memory.rangeOffset? address 4
  ByteRegion.loadUInt32LE? memory.toNeutralRegion offset

/-- Checked complete eight-byte little-endian load.  Data words have their
own register bank and are never represented as addresses. -/
def loadUInt64LE? (memory : ByteMemory) (address : UInt64) : Option UInt64 := do
  let offset ← memory.rangeOffset? address 8
  ByteRegion.loadUInt64LE? memory.toNeutralRegion offset

/-- Once a physical range has been resolved, a two-byte load from compiled
list memory is exactly the established fixed-offset list reader. -/
theorem loadUInt16LE?_ofList_of_range
    (base address : UInt64) (bytes : List UInt8) (offset : Nat)
    (range : (ofList base bytes).rangeOffset? address 2 = some offset) :
    (ofList base bytes).loadUInt16LE? address =
      M0GCFlatHeaderLoaderCorrespondence.readAt?
        M0GCWireFormat.readUInt16LE bytes offset := by
  simp [loadUInt16LE?, range,
    M0GCBoundedByteMemory.ByteRegion.loadUInt16LE?_ofList]

/-- Four-byte physical/list-reader correspondence. -/
theorem loadUInt32LE?_ofList_of_range
    (base address : UInt64) (bytes : List UInt8) (offset : Nat)
    (range : (ofList base bytes).rangeOffset? address 4 = some offset) :
    (ofList base bytes).loadUInt32LE? address =
      M0GCFlatHeaderLoaderCorrespondence.readAt?
        CompiledPlanWireFormat.readUInt32LE bytes offset := by
  simp [loadUInt32LE?, range,
    M0GCBoundedByteMemory.ByteRegion.loadUInt32LE?_ofList]

/-- Eight-byte physical/list-reader correspondence. -/
theorem loadUInt64LE?_ofList_of_range
    (base address : UInt64) (bytes : List UInt8) (offset : Nat)
    (range : (ofList base bytes).rangeOffset? address 8 = some offset) :
    (ofList base bytes).loadUInt64LE? address =
      M0GCFlatHeaderLoaderCorrespondence.readAt?
        M0GCWireFormat.readUInt64LE bytes offset := by
  simp [loadUInt64LE?, range,
    M0GCBoundedByteMemory.ByteRegion.loadUInt64LE?_ofList]

/-- Checked complete four-byte little-endian store.  No prefix is written
when the complete field is unavailable. -/
def storeUInt32LE? (memory : ByteMemory) (address : UInt64)
    (value : UInt32) : Option ByteMemory := do
  let offset ← memory.rangeOffset? address 4
  let cells ← M0GCBytePackedResultStoreRefinement.storeUInt32LE?
    memory.cells offset value
  some { memory with cells }

theorem storeByte?_size
    {memory updated : ByteMemory} {address : UInt64} {value : UInt8}
    (stored : memory.storeByte? address value = some updated) :
    updated.cells.size = memory.cells.size := by
  cases range : memory.rangeOffset? address 1 with
  | none =>
      simp [storeByte?, range] at stored
  | some offset =>
      by_cases inBounds : offset < memory.cells.size
      · simp [storeByte?, range, inBounds] at stored
        subst updated
        simp
      · simp [storeByte?, range, inBounds] at stored

theorem storeUInt32LE?_size
    {memory updated : ByteMemory} {address : UInt64} {value : UInt32}
    (stored : memory.storeUInt32LE? address value = some updated) :
    updated.cells.size = memory.cells.size := by
  cases range : memory.rangeOffset? address 4 with
  | none =>
      simp [storeUInt32LE?, range] at stored
  | some offset =>
      cases packed :
          M0GCBytePackedResultStoreRefinement.storeUInt32LE?
            memory.cells offset value with
      | none =>
          simp [storeUInt32LE?, range, packed] at stored
      | some cells =>
          simp [storeUInt32LE?, range, packed] at stored
          subst updated
          exact M0GCBytePackedResultStoreRefinement.storeUInt32LE?_size packed

theorem storeByte?_base
    {memory updated : ByteMemory} {address : UInt64} {value : UInt8}
    (stored : memory.storeByte? address value = some updated) :
    updated.base = memory.base := by
  cases range : memory.rangeOffset? address 1 with
  | none =>
      simp [storeByte?, range] at stored
  | some offset =>
      by_cases inBounds : offset < memory.cells.size
      · simp [storeByte?, range, inBounds] at stored
        subst updated
        rfl
      · simp [storeByte?, range, inBounds] at stored

theorem storeUInt32LE?_base
    {memory updated : ByteMemory} {address : UInt64} {value : UInt32}
    (stored : memory.storeUInt32LE? address value = some updated) :
    updated.base = memory.base := by
  cases range : memory.rangeOffset? address 4 with
  | none =>
      simp [storeUInt32LE?, range] at stored
  | some offset =>
      cases packed :
          M0GCBytePackedResultStoreRefinement.storeUInt32LE?
            memory.cells offset value with
      | none =>
          simp [storeUInt32LE?, range, packed] at stored
      | some cells =>
          simp [storeUInt32LE?, range, packed] at stored
          subst updated
          rfl

theorem storeByte?_wellFormed
    {memory updated : ByteMemory} {address : UInt64} {value : UInt8}
    (wellFormed : memory.WellFormed)
    (stored : memory.storeByte? address value = some updated) :
    updated.WellFormed := by
  unfold WellFormed at wellFormed ⊢
  rw [storeByte?_base stored, storeByte?_size stored]
  exact wellFormed

theorem storeUInt32LE?_wellFormed
    {memory updated : ByteMemory} {address : UInt64} {value : UInt32}
    (wellFormed : memory.WellFormed)
    (stored : memory.storeUInt32LE? address value = some updated) :
    updated.WellFormed := by
  unfold WellFormed at wellFormed ⊢
  rw [storeUInt32LE?_base stored, storeUInt32LE?_size stored]
  exact wellFormed

/-- A successful word store changes no byte outside the selected physical
four-byte interval. -/
theorem getElem?_of_storeUInt32LE?_outside
    {memory updated : ByteMemory} {address : UInt64} {value : UInt32}
    {index offset : Nat}
    (range : memory.rangeOffset? address 4 = some offset)
    (stored : memory.storeUInt32LE? address value = some updated)
    (outside : index < offset ∨ offset + 4 ≤ index) :
    updated.cells[index]? = memory.cells[index]? := by
  cases packed :
      M0GCBytePackedResultStoreRefinement.storeUInt32LE?
        memory.cells offset value with
  | none =>
      simp [storeUInt32LE?, range, packed] at stored
  | some cells =>
      simp [storeUInt32LE?, range, packed] at stored
      subst updated
      exact
        M0GCBytePackedResultStoreRefinement.getElem?_of_storeUInt32LE?_outside
          packed outside

/-! Concrete memory discriminators. -/

def fourBytes : ByteMemory :=
  { base := 100, cells := #[0, 0, 0, 0] }

theorem fourBytes_wellFormed : fourBytes.WellFormed := by
  change 104 < UInt64.size
  decide

theorem fourBytes_roundTrip :
    (fourBytes.storeUInt32LE? 100 0x04030201).bind
        (fun memory => memory.loadUInt32LE? 100) =
      some 0x04030201 := by
  decide

theorem partial_word_store_rejected :
    fourBytes.storeUInt32LE? 101 7 = none := by
  decide

theorem wrapped_word_store_rejected :
    fourBytes.storeUInt32LE?
      (UInt64.ofNat (UInt64.size - 1)) 7 = none := by
  decide

def eightBytes : ByteMemory :=
  { base := 200, cells := #[1, 2, 3, 4, 5, 6, 7, 8] }

theorem two_byte_load_exact :
    eightBytes.loadUInt16LE? 200 = some 0x0201 := by
  decide

theorem eight_byte_load_exact :
    eightBytes.loadUInt64LE? 200 = some 0x0807060504030201 := by
  decide

theorem partial_eight_byte_load_rejected :
    eightBytes.loadUInt64LE? 201 = none := by
  decide

end ByteMemory

/-! ## Intrinsically width-typed register banks -/

structure RegisterShape where
  byteCount : Nat
  word16Count : Nat
  word32Count : Nat
  word64Count : Nat
  addressCount : Nat
  flagCount : Nat
deriving DecidableEq, Repr

abbrev ByteRegister (shape : RegisterShape) := Fin shape.byteCount
abbrev Word16Register (shape : RegisterShape) := Fin shape.word16Count
abbrev Word32Register (shape : RegisterShape) := Fin shape.word32Count
abbrev Word64Register (shape : RegisterShape) := Fin shape.word64Count
abbrev AddressRegister (shape : RegisterShape) := Fin shape.addressCount
abbrev FlagRegister (shape : RegisterShape) := Fin shape.flagCount

/-- A target register file whose bank type determines every register's value
type.  Register lookup cannot fail at runtime. -/
structure RegisterFile (shape : RegisterShape) where
  bytes : ByteRegister shape → UInt8
  words16 : Word16Register shape → UInt16
  words32 : Word32Register shape → UInt32
  words64 : Word64Register shape → UInt64
  addresses : AddressRegister shape → UInt64
  flags : FlagRegister shape → Bool

namespace RegisterFile

def zero (shape : RegisterShape) : RegisterFile shape where
  bytes := fun _ => 0
  words16 := fun _ => 0
  words32 := fun _ => 0
  words64 := fun _ => 0
  addresses := fun _ => 0
  flags := fun _ => false

def writeByte {shape : RegisterShape} (registers : RegisterFile shape)
    (target : ByteRegister shape) (value : UInt8) : RegisterFile shape :=
  { registers with bytes := Function.update registers.bytes target value }

def writeWord16 {shape : RegisterShape} (registers : RegisterFile shape)
    (target : Word16Register shape) (value : UInt16) : RegisterFile shape :=
  { registers with words16 := Function.update registers.words16 target value }

def writeWord32 {shape : RegisterShape} (registers : RegisterFile shape)
    (target : Word32Register shape) (value : UInt32) : RegisterFile shape :=
  { registers with words32 := Function.update registers.words32 target value }

def writeWord64 {shape : RegisterShape} (registers : RegisterFile shape)
    (target : Word64Register shape) (value : UInt64) : RegisterFile shape :=
  { registers with words64 := Function.update registers.words64 target value }

def writeAddress {shape : RegisterShape} (registers : RegisterFile shape)
    (target : AddressRegister shape) (value : UInt64) : RegisterFile shape :=
  { registers with addresses := Function.update registers.addresses target value }

def writeFlag {shape : RegisterShape} (registers : RegisterFile shape)
    (target : FlagRegister shape) (value : Bool) : RegisterFile shape :=
  { registers with flags := Function.update registers.flags target value }

@[simp] theorem writeByte_same {shape : RegisterShape}
    (registers : RegisterFile shape) (target : ByteRegister shape)
    (value : UInt8) :
    (registers.writeByte target value).bytes target = value := by
  simp [writeByte]

@[simp] theorem writeWord16_same {shape : RegisterShape}
    (registers : RegisterFile shape) (target : Word16Register shape)
    (value : UInt16) :
    (registers.writeWord16 target value).words16 target = value := by
  simp [writeWord16]

@[simp] theorem writeWord32_same {shape : RegisterShape}
    (registers : RegisterFile shape) (target : Word32Register shape)
    (value : UInt32) :
    (registers.writeWord32 target value).words32 target = value := by
  simp [writeWord32]

@[simp] theorem writeWord64_same {shape : RegisterShape}
    (registers : RegisterFile shape) (target : Word64Register shape)
    (value : UInt64) :
    (registers.writeWord64 target value).words64 target = value := by
  simp [writeWord64]

@[simp] theorem writeAddress_same {shape : RegisterShape}
    (registers : RegisterFile shape) (target : AddressRegister shape)
    (value : UInt64) :
    (registers.writeAddress target value).addresses target = value := by
  simp [writeAddress]

@[simp] theorem writeFlag_same {shape : RegisterShape}
    (registers : RegisterFile shape) (target : FlagRegister shape)
    (value : Bool) :
    (registers.writeFlag target value).flags target = value := by
  simp [writeFlag]

@[simp] theorem writeWord16_other {shape : RegisterShape}
    (registers : RegisterFile shape) (target source : Word16Register shape)
    (value : UInt16) (different : source ≠ target) :
    (registers.writeWord16 target value).words16 source =
      registers.words16 source := by
  simp [writeWord16, different]

@[simp] theorem writeWord32_other {shape : RegisterShape}
    (registers : RegisterFile shape) (target source : Word32Register shape)
    (value : UInt32) (different : source ≠ target) :
    (registers.writeWord32 target value).words32 source =
      registers.words32 source := by
  simp [writeWord32, different]

@[simp] theorem writeWord64_other {shape : RegisterShape}
    (registers : RegisterFile shape) (target source : Word64Register shape)
    (value : UInt64) (different : source ≠ target) :
    (registers.writeWord64 target value).words64 source =
      registers.words64 source := by
  simp [writeWord64, different]

@[simp] theorem writeAddress_other {shape : RegisterShape}
    (registers : RegisterFile shape) (target source : AddressRegister shape)
    (value : UInt64) (different : source ≠ target) :
    (registers.writeAddress target value).addresses source =
      registers.addresses source := by
  simp [writeAddress, different]

@[simp] theorem writeFlag_other {shape : RegisterShape}
    (registers : RegisterFile shape) (target source : FlagRegister shape)
    (value : Bool) (different : source ≠ target) :
    (registers.writeFlag target value).flags source = registers.flags source := by
  simp [writeFlag, different]

/-! Projection preservation is part of the typed-bank interface.  Lowering
proofs should not unfold the representation merely to learn that writing a
data register preserves physical addresses, or that address formation
preserves data and flags. -/

@[simp] theorem writeByte_words16 {shape : RegisterShape}
    (registers : RegisterFile shape) (target : ByteRegister shape)
    (value : UInt8) :
    (registers.writeByte target value).words16 = registers.words16 := rfl

@[simp] theorem writeByte_words32 {shape : RegisterShape}
    (registers : RegisterFile shape) (target : ByteRegister shape)
    (value : UInt8) :
    (registers.writeByte target value).words32 = registers.words32 := rfl

@[simp] theorem writeByte_words64 {shape : RegisterShape}
    (registers : RegisterFile shape) (target : ByteRegister shape)
    (value : UInt8) :
    (registers.writeByte target value).words64 = registers.words64 := rfl

@[simp] theorem writeByte_addresses {shape : RegisterShape}
    (registers : RegisterFile shape) (target : ByteRegister shape)
    (value : UInt8) :
    (registers.writeByte target value).addresses = registers.addresses := rfl

@[simp] theorem writeByte_flags {shape : RegisterShape}
    (registers : RegisterFile shape) (target : ByteRegister shape)
    (value : UInt8) :
    (registers.writeByte target value).flags = registers.flags := rfl

@[simp] theorem writeWord16_bytes {shape : RegisterShape}
    (registers : RegisterFile shape) (target : Word16Register shape)
    (value : UInt16) :
    (registers.writeWord16 target value).bytes = registers.bytes := rfl

@[simp] theorem writeWord16_words32 {shape : RegisterShape}
    (registers : RegisterFile shape) (target : Word16Register shape)
    (value : UInt16) :
    (registers.writeWord16 target value).words32 = registers.words32 := rfl

@[simp] theorem writeWord16_words64 {shape : RegisterShape}
    (registers : RegisterFile shape) (target : Word16Register shape)
    (value : UInt16) :
    (registers.writeWord16 target value).words64 = registers.words64 := rfl

@[simp] theorem writeWord16_flags {shape : RegisterShape}
    (registers : RegisterFile shape) (target : Word16Register shape)
    (value : UInt16) :
    (registers.writeWord16 target value).flags = registers.flags := rfl

@[simp] theorem writeWord32_bytes {shape : RegisterShape}
    (registers : RegisterFile shape) (target : Word32Register shape)
    (value : UInt32) :
    (registers.writeWord32 target value).bytes = registers.bytes := rfl

@[simp] theorem writeWord32_words16 {shape : RegisterShape}
    (registers : RegisterFile shape) (target : Word32Register shape)
    (value : UInt32) :
    (registers.writeWord32 target value).words16 = registers.words16 := rfl

@[simp] theorem writeWord32_words64 {shape : RegisterShape}
    (registers : RegisterFile shape) (target : Word32Register shape)
    (value : UInt32) :
    (registers.writeWord32 target value).words64 = registers.words64 := rfl

@[simp] theorem writeWord32_flags {shape : RegisterShape}
    (registers : RegisterFile shape) (target : Word32Register shape)
    (value : UInt32) :
    (registers.writeWord32 target value).flags = registers.flags := rfl

@[simp] theorem writeWord64_bytes {shape : RegisterShape}
    (registers : RegisterFile shape) (target : Word64Register shape)
    (value : UInt64) :
    (registers.writeWord64 target value).bytes = registers.bytes := rfl

@[simp] theorem writeWord64_words16 {shape : RegisterShape}
    (registers : RegisterFile shape) (target : Word64Register shape)
    (value : UInt64) :
    (registers.writeWord64 target value).words16 = registers.words16 := rfl

@[simp] theorem writeWord64_words32 {shape : RegisterShape}
    (registers : RegisterFile shape) (target : Word64Register shape)
    (value : UInt64) :
    (registers.writeWord64 target value).words32 = registers.words32 := rfl

@[simp] theorem writeWord64_flags {shape : RegisterShape}
    (registers : RegisterFile shape) (target : Word64Register shape)
    (value : UInt64) :
    (registers.writeWord64 target value).flags = registers.flags := rfl

@[simp] theorem writeWord16_addresses {shape : RegisterShape}
    (registers : RegisterFile shape) (target : Word16Register shape)
    (value : UInt16) :
    (registers.writeWord16 target value).addresses = registers.addresses := rfl

@[simp] theorem writeWord32_addresses {shape : RegisterShape}
    (registers : RegisterFile shape) (target : Word32Register shape)
    (value : UInt32) :
    (registers.writeWord32 target value).addresses = registers.addresses := rfl

@[simp] theorem writeWord64_addresses {shape : RegisterShape}
    (registers : RegisterFile shape) (target : Word64Register shape)
    (value : UInt64) :
    (registers.writeWord64 target value).addresses = registers.addresses := rfl

@[simp] theorem writeFlag_addresses {shape : RegisterShape}
    (registers : RegisterFile shape) (target : FlagRegister shape)
    (value : Bool) :
    (registers.writeFlag target value).addresses = registers.addresses := rfl

@[simp] theorem writeAddress_words16 {shape : RegisterShape}
    (registers : RegisterFile shape) (target : AddressRegister shape)
    (value : UInt64) :
    (registers.writeAddress target value).words16 = registers.words16 := rfl

@[simp] theorem writeAddress_bytes {shape : RegisterShape}
    (registers : RegisterFile shape) (target : AddressRegister shape)
    (value : UInt64) :
    (registers.writeAddress target value).bytes = registers.bytes := rfl

@[simp] theorem writeAddress_words32 {shape : RegisterShape}
    (registers : RegisterFile shape) (target : AddressRegister shape)
    (value : UInt64) :
    (registers.writeAddress target value).words32 = registers.words32 := rfl

@[simp] theorem writeAddress_words64 {shape : RegisterShape}
    (registers : RegisterFile shape) (target : AddressRegister shape)
    (value : UInt64) :
    (registers.writeAddress target value).words64 = registers.words64 := rfl

@[simp] theorem writeAddress_flags {shape : RegisterShape}
    (registers : RegisterFile shape) (target : AddressRegister shape)
    (value : UInt64) :
    (registers.writeAddress target value).flags = registers.flags := rfl

@[simp] theorem writeFlag_bytes {shape : RegisterShape}
    (registers : RegisterFile shape) (target : FlagRegister shape)
    (value : Bool) :
    (registers.writeFlag target value).bytes = registers.bytes := rfl

@[simp] theorem writeFlag_words16 {shape : RegisterShape}
    (registers : RegisterFile shape) (target : FlagRegister shape)
    (value : Bool) :
    (registers.writeFlag target value).words16 = registers.words16 := rfl

@[simp] theorem writeFlag_words32 {shape : RegisterShape}
    (registers : RegisterFile shape) (target : FlagRegister shape)
    (value : Bool) :
    (registers.writeFlag target value).words32 = registers.words32 := rfl

@[simp] theorem writeFlag_words64 {shape : RegisterShape}
    (registers : RegisterFile shape) (target : FlagRegister shape)
    (value : Bool) :
    (registers.writeFlag target value).words64 = registers.words64 := rfl

end RegisterFile

/-! ## Instruction syntax and explicit fault semantics -/

/-- Width-safe instructions.  No constructor can, for example, place a
32-bit load in a Boolean register or use a byte register as an address. -/
inductive Instruction (shape : RegisterShape) where
  | constByte (target : ByteRegister shape) (value : UInt8)
  | constWord16 (target : Word16Register shape) (value : UInt16)
  | constWord32 (target : Word32Register shape) (value : UInt32)
  | constWord64 (target : Word64Register shape) (value : UInt64)
  | constAddress (target : AddressRegister shape) (value : UInt64)
  | constFlag (target : FlagRegister shape) (value : Bool)
  | copyByte (target source : ByteRegister shape)
  | copyWord16 (target source : Word16Register shape)
  | copyWord32 (target source : Word32Register shape)
  | copyWord64 (target source : Word64Register shape)
  | copyAddress (target source : AddressRegister shape)
  | copyFlag (target source : FlagRegister shape)
  | word32ToAddress (target : AddressRegister shape)
      (source : Word32Register shape)
  | addAddressChecked (target left right : AddressRegister shape)
  | mulAddressChecked (target left right : AddressRegister shape)
  | equalByte (target : FlagRegister shape)
      (left right : ByteRegister shape)
  | equalWord16 (target : FlagRegister shape)
      (left right : Word16Register shape)
  | equalWord32 (target : FlagRegister shape)
      (left right : Word32Register shape)
  | equalWord64 (target : FlagRegister shape)
      (left right : Word64Register shape)
  | equalAddress (target : FlagRegister shape)
      (left right : AddressRegister shape)
  | lessAddress (target : FlagRegister shape)
      (left right : AddressRegister shape)
  | loadByte (target : ByteRegister shape) (address : AddressRegister shape)
  | storeByte (address : AddressRegister shape) (source : ByteRegister shape)
  | loadWord16LE (target : Word16Register shape)
      (address : AddressRegister shape)
  | loadWord32LE (target : Word32Register shape)
      (address : AddressRegister shape)
  | storeWord32LE (address : AddressRegister shape)
      (source : Word32Register shape)
  | loadWord64LE (target : Word64Register shape)
      (address : AddressRegister shape)
  | rejectUnless (condition : FlagRegister shape)
  | branch (condition : FlagRegister shape) (whenTrue whenFalse : Nat)
  | jump (target : Nat)
  | halt (accepted : Bool)
deriving DecidableEq, Repr

structure Program (shape : RegisterShape) where
  code : Array (Instruction shape)
deriving DecidableEq, Repr

inductive Fault where
  | invalidProgramCounter (counter : Nat)
  | invalidBranchTarget (target : Nat)
  | addressOverflow
  | byteReadOutOfBounds
  | byteWriteOutOfBounds
  | word16ReadOutOfBounds
  | word32ReadOutOfBounds
  | word32WriteOutOfBounds
  | word64ReadOutOfBounds
deriving DecidableEq, Repr

/-- Source-level checked address addition with the machine's explicit fault
vocabulary.  Lowering proofs use this operation as meaning; the target
instruction remains `addAddressChecked`. -/
def addAddressDetailed (left right : UInt64) : Except Fault UInt64 :=
  match checkedAdd left right with
  | none => .error .addressOverflow
  | some result => .ok result

/-- Source-level checked address scaling with the machine's explicit fault
vocabulary.  Lowering proofs use this operation as meaning; the target
instruction remains `mulAddressChecked`. -/
def mulAddressDetailed (left right : UInt64) : Except Fault UInt64 :=
  match checkedMul left right with
  | none => .error .addressOverflow
  | some result => .ok result

/-- Source-level checked two-byte load with the machine's explicit fault
vocabulary. -/
def loadWord16Detailed (memory : ByteMemory) (address : UInt64) :
    Except Fault UInt16 :=
  match memory.loadUInt16LE? address with
  | none => .error .word16ReadOutOfBounds
  | some value => .ok value

/-- Source-level checked four-byte load with the machine's explicit fault
vocabulary. -/
def loadWord32Detailed (memory : ByteMemory) (address : UInt64) :
    Except Fault UInt32 :=
  match memory.loadUInt32LE? address with
  | none => .error .word32ReadOutOfBounds
  | some value => .ok value

/-- Source-level checked eight-byte load with the machine's explicit fault
vocabulary. -/
def loadWord64Detailed (memory : ByteMemory) (address : UInt64) :
    Except Fault UInt64 :=
  match memory.loadUInt64LE? address with
  | none => .error .word64ReadOutOfBounds
  | some value => .ok value

/-- Machine states retain registers and memory at every terminal outcome so
that refinement proofs can inspect effects without a hidden global store. -/
inductive MachineState (shape : RegisterShape) where
  | running (counter : Nat) (registers : RegisterFile shape)
      (memory : ByteMemory)
  | halted (accepted : Bool) (registers : RegisterFile shape)
      (memory : ByteMemory)
  | faulted (reason : Fault) (registers : RegisterFile shape)
      (memory : ByteMemory)

namespace MachineState

/-- Terminal observation distinguishes logical rejection (`ok false`) from a
machine fault (`error reason`). -/
def observe {shape : RegisterShape} :
    MachineState shape → Option (Except Fault Bool)
  | .running _ _ _ => none
  | .halted accepted _ _ => some (.ok accepted)
  | .faulted reason _ _ => some (.error reason)

def memory {shape : RegisterShape} : MachineState shape → ByteMemory
  | .running _ _ memory => memory
  | .halted _ _ memory => memory
  | .faulted _ _ memory => memory

def registers {shape : RegisterShape} :
    MachineState shape → RegisterFile shape
  | .running _ registers _ => registers
  | .halted _ registers _ => registers
  | .faulted _ registers _ => registers

end MachineState

/-- Continue at the statically selected next instruction, or fault before a
bad branch target can be fetched. -/
def continueAt {shape : RegisterShape} (program : Program shape)
    (target : Nat) (registers : RegisterFile shape) (memory : ByteMemory) :
    MachineState shape :=
  if target < program.code.size then
    .running target registers memory
  else
    .faulted (.invalidBranchTarget target) registers memory

/-- Execute one already-fetched instruction. -/
def executeInstruction {shape : RegisterShape} (program : Program shape)
    (counter : Nat) (registers : RegisterFile shape) (memory : ByteMemory) :
    Instruction shape → MachineState shape
  | .constByte target value =>
      continueAt program (counter + 1) (registers.writeByte target value) memory
  | .constWord16 target value =>
      continueAt program (counter + 1)
        (registers.writeWord16 target value) memory
  | .constWord32 target value =>
      continueAt program (counter + 1) (registers.writeWord32 target value) memory
  | .constWord64 target value =>
      continueAt program (counter + 1)
        (registers.writeWord64 target value) memory
  | .constAddress target value =>
      continueAt program (counter + 1) (registers.writeAddress target value) memory
  | .constFlag target value =>
      continueAt program (counter + 1) (registers.writeFlag target value) memory
  | .copyByte target source =>
      continueAt program (counter + 1)
        (registers.writeByte target (registers.bytes source)) memory
  | .copyWord16 target source =>
      continueAt program (counter + 1)
        (registers.writeWord16 target (registers.words16 source)) memory
  | .copyWord32 target source =>
      continueAt program (counter + 1)
        (registers.writeWord32 target (registers.words32 source)) memory
  | .copyWord64 target source =>
      continueAt program (counter + 1)
        (registers.writeWord64 target (registers.words64 source)) memory
  | .copyAddress target source =>
      continueAt program (counter + 1)
        (registers.writeAddress target (registers.addresses source)) memory
  | .copyFlag target source =>
      continueAt program (counter + 1)
        (registers.writeFlag target (registers.flags source)) memory
  | .word32ToAddress target source =>
      continueAt program (counter + 1)
        (registers.writeAddress target
          (registers.words32 source).toUInt64) memory
  | .addAddressChecked target left right =>
      match checkedAdd (registers.addresses left) (registers.addresses right) with
      | none => .faulted .addressOverflow registers memory
      | some value =>
          continueAt program (counter + 1)
            (registers.writeAddress target value) memory
  | .mulAddressChecked target left right =>
      match checkedMul (registers.addresses left) (registers.addresses right) with
      | none => .faulted .addressOverflow registers memory
      | some value =>
          continueAt program (counter + 1)
            (registers.writeAddress target value) memory
  | .equalByte target left right =>
      continueAt program (counter + 1)
        (registers.writeFlag target
          (registers.bytes left = registers.bytes right)) memory
  | .equalWord16 target left right =>
      continueAt program (counter + 1)
        (registers.writeFlag target
          (registers.words16 left = registers.words16 right)) memory
  | .equalWord32 target left right =>
      continueAt program (counter + 1)
        (registers.writeFlag target
          (registers.words32 left = registers.words32 right)) memory
  | .equalWord64 target left right =>
      continueAt program (counter + 1)
        (registers.writeFlag target
          (registers.words64 left = registers.words64 right)) memory
  | .equalAddress target left right =>
      continueAt program (counter + 1)
        (registers.writeFlag target
          (registers.addresses left = registers.addresses right)) memory
  | .lessAddress target left right =>
      continueAt program (counter + 1)
        (registers.writeFlag target
          ((registers.addresses left).toNat <
            (registers.addresses right).toNat)) memory
  | .loadByte target address =>
      match memory.loadByte? (registers.addresses address) with
      | none => .faulted .byteReadOutOfBounds registers memory
      | some value =>
          continueAt program (counter + 1)
            (registers.writeByte target value) memory
  | .storeByte address source =>
      match memory.storeByte? (registers.addresses address)
          (registers.bytes source) with
      | none => .faulted .byteWriteOutOfBounds registers memory
      | some updated => continueAt program (counter + 1) registers updated
  | .loadWord16LE target address =>
      match memory.loadUInt16LE? (registers.addresses address) with
      | none => .faulted .word16ReadOutOfBounds registers memory
      | some value =>
          continueAt program (counter + 1)
            (registers.writeWord16 target value) memory
  | .loadWord32LE target address =>
      match memory.loadUInt32LE? (registers.addresses address) with
      | none => .faulted .word32ReadOutOfBounds registers memory
      | some value =>
          continueAt program (counter + 1)
            (registers.writeWord32 target value) memory
  | .storeWord32LE address source =>
      match memory.storeUInt32LE? (registers.addresses address)
          (registers.words32 source) with
      | none => .faulted .word32WriteOutOfBounds registers memory
      | some updated => continueAt program (counter + 1) registers updated
  | .loadWord64LE target address =>
      match memory.loadUInt64LE? (registers.addresses address) with
      | none => .faulted .word64ReadOutOfBounds registers memory
      | some value =>
          continueAt program (counter + 1)
            (registers.writeWord64 target value) memory
  | .rejectUnless condition =>
      if registers.flags condition then
        continueAt program (counter + 1) registers memory
      else
        .halted false registers memory
  | .branch condition whenTrue whenFalse =>
      continueAt program
        (if registers.flags condition then whenTrue else whenFalse)
        registers memory
  | .jump target => continueAt program target registers memory
  | .halt accepted => .halted accepted registers memory

/-- One deterministic fetch/execute transition.  Terminal states stutter. -/
def step {shape : RegisterShape} (program : Program shape) :
    MachineState shape → MachineState shape
  | .running counter registers memory =>
      match program.code[counter]? with
      | none => .faulted (.invalidProgramCounter counter) registers memory
      | some instruction =>
          executeInstruction program counter registers memory instruction
  | terminal@(.halted _ _ _) => terminal
  | terminal@(.faulted _ _ _) => terminal

/-- Relational spelling used by path-valued realization proofs. -/
def Transition {shape : RegisterShape} (program : Program shape)
    (before after : MachineState shape) : Prop :=
  step program before = after

theorem transition_deterministic {shape : RegisterShape}
    (program : Program shape) {before first second : MachineState shape}
    (firstStep : Transition program before first)
    (secondStep : Transition program before second) :
    first = second := by
  rw [Transition] at firstStep secondStep
  exact firstStep.symm.trans secondStep

@[simp] theorem step_halted {shape : RegisterShape}
    (program : Program shape) (accepted : Bool)
    (registers : RegisterFile shape) (memory : ByteMemory) :
    step program (.halted accepted registers memory) =
      .halted accepted registers memory := rfl

@[simp] theorem step_faulted {shape : RegisterShape}
    (program : Program shape) (reason : Fault)
    (registers : RegisterFile shape) (memory : ByteMemory) :
    step program (.faulted reason registers memory) =
      .faulted reason registers memory := rfl

def runSteps {shape : RegisterShape} (program : Program shape) :
    Nat → MachineState shape → MachineState shape
  | 0, state => state
  | fuel + 1, state => runSteps program fuel (step program state)

@[simp] theorem runSteps_zero {shape : RegisterShape}
    (program : Program shape) (state : MachineState shape) :
    runSteps program 0 state = state := rfl

/-- Executing two fuel segments is the same as executing their sum.  This is
the compositional boundary used to prove long generated programs by named
phases instead of expanding one enormous transition term. -/
theorem runSteps_add {shape : RegisterShape} (program : Program shape)
    (first second : Nat) (state : MachineState shape) :
    runSteps program (first + second) state =
      runSteps program second (runSteps program first state) := by
  induction first generalizing state with
  | zero => simp
  | succ first inductionHypothesis =>
      simp only [Nat.succ_add, runSteps]
      exact inductionHypothesis (step program state)

@[simp] theorem runSteps_halted {shape : RegisterShape}
    (program : Program shape) (fuel : Nat) (accepted : Bool)
    (registers : RegisterFile shape) (memory : ByteMemory) :
    runSteps program fuel (.halted accepted registers memory) =
      .halted accepted registers memory := by
  induction fuel with
  | zero => rfl
  | succ fuel inductionHypothesis =>
      simpa only [runSteps, step_halted] using inductionHypothesis

@[simp] theorem runSteps_faulted {shape : RegisterShape}
    (program : Program shape) (fuel : Nat) (reason : Fault)
    (registers : RegisterFile shape) (memory : ByteMemory) :
    runSteps program fuel (.faulted reason registers memory) =
      .faulted reason registers memory := by
  induction fuel with
  | zero => rfl
  | succ fuel inductionHypothesis =>
      simpa only [runSteps, step_faulted] using inductionHypothesis

/-! ## Positive and adversarial instruction programs -/

namespace Canary

def shape : RegisterShape where
  byteCount := 0
  word16Count := 0
  word32Count := 2
  word64Count := 0
  addressCount := 1
  flagCount := 1

def wordSource : Word32Register shape := ⟨0, by decide⟩
def wordLoaded : Word32Register shape := ⟨1, by decide⟩
def address : AddressRegister shape := ⟨0, by decide⟩
def equal : FlagRegister shape := ⟨0, by decide⟩

/-- A nontrivial store/load/compare/branch program.  Its acceptance depends
on the physical little-endian round trip. -/
def roundTripProgram : Program shape where
  code := #[
    .constAddress address 100,
    .constWord32 wordSource 0x04030201,
    .storeWord32LE address wordSource,
    .loadWord32LE wordLoaded address,
    .equalWord32 equal wordSource wordLoaded,
    .branch equal 6 7,
    .halt true,
    .halt false]

def initial : MachineState shape :=
  .running 0 (RegisterFile.zero shape) ByteMemory.fourBytes

def final : MachineState shape := runSteps roundTripProgram 7 initial

theorem roundTrip_accepts :
    final.observe = some (.ok true) := by
  decide

theorem roundTrip_writes_canonical_bytes :
    final.memory.cells = #[1, 2, 3, 4] := by
  decide

def partialProgram : Program shape where
  code := #[
    .constAddress address 101,
    .constWord32 wordSource 7,
    .storeWord32LE address wordSource,
    .halt true]

def partialFinal : MachineState shape :=
  runSteps partialProgram 3 initial

theorem partial_store_faults_without_accepting :
    partialFinal.observe = some (.error .word32WriteOutOfBounds) := by
  decide

def overflowShape : RegisterShape where
  byteCount := 0
  word16Count := 0
  word32Count := 0
  word64Count := 0
  addressCount := 3
  flagCount := 0

def overflowLeft : AddressRegister overflowShape := ⟨0, by decide⟩
def overflowRight : AddressRegister overflowShape := ⟨1, by decide⟩
def overflowTarget : AddressRegister overflowShape := ⟨2, by decide⟩

def overflowProgram : Program overflowShape where
  code := #[
    .constAddress overflowLeft (UInt64.ofNat (UInt64.size - 1)),
    .constAddress overflowRight 1,
    .addAddressChecked overflowTarget overflowLeft overflowRight,
    .halt true]

def overflowInitial : MachineState overflowShape :=
  .running 0 (RegisterFile.zero overflowShape) ByteMemory.fourBytes

theorem address_overflow_faults :
    (runSteps overflowProgram 3 overflowInitial).observe =
      some (.error .addressOverflow) := by
  decide

def badBranchProgram : Program shape where
  code := #[
    .constFlag equal true,
    .branch equal 99 2,
    .halt false]

theorem bad_branch_target_faults :
    (runSteps badBranchProgram 2 initial).observe =
      some (.error (.invalidBranchTarget 99)) := by
  decide

theorem invalid_initial_counter_faults :
    (step roundTripProgram
      (.running 99 (RegisterFile.zero shape) ByteMemory.fourBytes)).observe =
      some (.error (.invalidProgramCounter 99)) := by
  decide

end Canary

#print axioms ByteMemory.rangeOffset?_some_bounds
#print axioms ByteMemory.storeUInt32LE?_wellFormed
#print axioms ByteMemory.getElem?_of_storeUInt32LE?_outside
#print axioms transition_deterministic
#print axioms Canary.roundTrip_accepts
#print axioms Canary.partial_store_faults_without_accepting

end Mettapedia.GSLT.LanguageDef.M0GCCheckedByteMachineIR
