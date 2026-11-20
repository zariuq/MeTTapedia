import Mettapedia.Machines.TIsa.X86P1Sub1Fuel

/-!
# Receipt writeback at an admitted native epilogue

The proof uses the p1 allowance epilogue's actual three instructions. Its
entry address and placement are parameters. R14 loads the budget, subtracts
the remaining allowance held in RBP, and stores the receipt. Other frame
fields and RAX are retained.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000

namespace Mettapedia.Machines.TIsa.X86AllowanceWriteback

open _root_.X86Registers X86Execution X86RegisterRefinement
local instance : MemoryPrimitives := X86Memory.ordinary

abbrev handlers := X86P1Sub1Fuel.Receipt.handlers

def bytes : List Nat := X86P1Sub1Fuel.Controls.writebackBytes.map BitVec.toNat

structure Entry (native : State) extends X86P1Sub1Fuel.Receipt.Facts native where
  origin : X86LegacyFetch.Basis native
  upper : origin.address.toInt + 17 < (2^47 : Int)
  loaded : codeLoaded native origin.address.toInt bytes

def afterLoad {native : State} (entry : Entry native) : State :=
  X86Move.putPointer (put native 14 entry.budget) (address entry.origin.address.toInt 7)

def afterSub {native : State} (entry : Entry native) (flags : BitVec 32) : State :=
  X86Move.putPointer (X86Flags.putFlags (put (afterLoad entry) 14 (entry.budget - entry.remaining))
    (X86Flags.mergeFlags entry.flags flags)) (address entry.origin.address.toInt 10)

def afterStore {native : State} (entry : Entry native) (flags : BitVec 32) : State :=
  X86Move.putPointer (X86WriteWords.storeBytes 8 (afterSub entry flags) entry.receiptAddress
    (entry.budget - entry.remaining)) (address entry.origin.address.toInt 17)

private theorem loadFrame {native : State} (entry : Entry native) :
    RegisterFrame {.r14, .rip} native (afterLoad entry) := by
  exact ((put_frame native 14 entry.budget).trans (pointer_frame _ _)).mono (by simp [key])

private theorem subtractionFrame {native : State} (entry : Entry native) (flags : BitVec 32) :
    X86StateFrame.Frame {.r14, .rflags, .rip} ∅ native (afterSub entry flags) := by
  have middle := X86Funding.GenericMemory.subtract_to_frame 14 (afterLoad entry)
    (entry.budget - entry.remaining) (X86Flags.mergeFlags entry.flags flags)
    (address entry.origin.address.toInt 10)
  exact ((X86StateFrame.registerOnly (loadFrame entry)).trans middle).mono
    (by decide) (by simp)

private theorem atOffset {native : State} (entry : Entry native) (offset : Nat) (within : offset ≤ 17) :
    (address entry.origin.address.toInt offset).toInt = entry.origin.address.toInt + offset :=
  address_toInt _ (BitVec.le_toInt _) entry.upper offset within

private theorem shifted {native : State} (entry : Entry native) (offset index : Nat) (within : offset ≤ 17) :
    address (address entry.origin.address.toInt offset).toInt index =
      address entry.origin.address.toInt (offset + index) := by
  rw [atOffset entry offset within]
  simp only [address, Nat.cast_add, Int.add_assoc]

private theorem load_budget (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (native : State) (entry : Entry native) :
    letI : OtherOpcodeHandlers := handlers other
    letI : VectorOpcodeHandlers := vector
    (Functions.x86_fetch_decode_execute ()).run native = .ok () (afterLoad entry) := by
  let origin := entry.origin
  have first : origin.opcodeAddress = address origin.address.toInt 1 := by
    apply BitVec.eq_of_toInt_eq
    rw [atOffset entry 1 (by decide)]
    exact origin.step1.symm
  have second : origin.modrmAddress = address origin.address.toInt 2 := by
    apply BitVec.eq_of_toInt_eq
    rw [atOffset entry 2 (by decide)]
    exact origin.step2.symm
  have third : origin.next = address origin.address.toInt 3 := by
    apply BitVec.eq_of_toInt_eq
    rw [atOffset entry 3 (by decide), ← origin.step3, ← origin.step2]
    change origin.address.toInt + 2 + 1 = origin.address.toInt + 3
    omega
  refine X86FrameLoad.fetched_frame (X86Arithmetic.linkedHandlers other) vector native 14 origin
    (address origin.address.toInt 7) entry.budgetAddress entry.visible entry.controls
    entry.frame entry.budget entry.flags (160#32) ?_ entry.budgetUpper entry.frameKnown
    entry.controlsKnown entry.flagsKnown entry.visibleKnown entry.quiet entry.budgetEffective entry.budgetAligned
    ?_ ?_ ?_ ?_ entry.budgetPresent
  · rw [third, atOffset entry 3 (by decide), atOffset entry 7 (by decide)]
    omega
  · simpa only [origin, address, Nat.cast_zero, Int.add_zero, BitVec.ofInt_toInt,
      show X86FrameLoad.frameRex (14 : Fin 16) = (76#8) by decide] using entry.loaded 0 76 rfl
  · rw [first]
    exact entry.loaded 1 139 rfl
  · rw [second]
    exact entry.loaded 2 183 rfl
  · intro index within
    rw [third, shifted entry 3 index (by decide)]
    have present := entry.loaded (3 + index) ((160#32).extractLsb' (8 * index) 8).toNat
      (by interval_cases index <;> rfl)
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using present

private theorem subtract_allowance (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (native : State) (entry : Entry native) :
    letI : OtherOpcodeHandlers := handlers other
    letI : VectorOpcodeHandlers := vector
    ∃ flags, (Functions.x86_fetch_decode_execute ()).run (afterLoad entry) = .ok () (afterSub entry flags) := by
  let current := afterLoad entry
  let frame := loadFrame entry
  let origin := X86Execution.rebase native current entry.origin (frame.mono (by decide))
    entry.upper 7 (by decide) (X86FuelPrefix.pointer_rip _ _)
  let window : X86LegacyFetch.Window current (X86Arithmetic.opcode .sub) true 5 14 := {
    toBasis := origin
    prefixByte := by rw [frame.memory]; exact entry.loaded 7 73 rfl
    opcodeByte := by rw [frame.memory]; exact entry.loaded 8 41 rfl
    modrmByte := by rw [frame.memory]; exact entry.loaded 9 238 rfl }
  have budget : lookup current 14 = some entry.budget := by
    simp only [current, afterLoad, X86Move.lookup_putPointer, lookup_put_same]
  exact X86Arithmetic.fetched_register64 (X86FrameLoad.linkedHandlers other) vector .sub current 5 14
    window entry.budget entry.remaining entry.flags ((frame.lookup 5 (by decide)).trans entry.remainingKnown)
    budget ((frame.registers .rflags (by decide)).trans entry.flagsKnown)
    ((frame.registers .log_register_writes (by decide)).trans entry.quiet)

private theorem store_receipt (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (native : State) (entry : Entry native) (flags : BitVec 32) :
    letI : OtherOpcodeHandlers := handlers other
    letI : VectorOpcodeHandlers := vector
    (Functions.x86_fetch_decode_execute ()).run (afterSub entry flags) = .ok () (afterStore entry flags) := by
  let current := afterSub entry flags
  let frame := subtractionFrame entry flags
  let origin := X86StateFrame.rebase native current entry.origin frame (by decide)
    entry.upper 10 (by decide) (X86FuelPrefix.pointer_rip _ _)
  have retained : ∀ address, current.mem.get? address = native.mem.get? address :=
    fun address => frame.memory address (by simp)
  have value : lookup current 14 = some (entry.budget - entry.remaining) := by
    rw [show current = afterSub entry flags from rfl, afterSub, X86Move.lookup_putPointer,
      (flags_frame _ _).lookup 14 (by decide), lookup_put_same]
  have observedFlags : current.regs.get? .rflags = some (X86Flags.mergeFlags entry.flags flags) := by
    rw [show current = afterSub entry flags from rfl, afterSub, (pointer_frame _ _).registers _ (by decide)]
    simp [X86Flags.putFlags]
  refine X86FrameStore.fetched_register (handlers other) vector current 14 origin
    (address entry.origin.address.toInt 17) entry.receiptAddress entry.visible entry.controls entry.frame
    (entry.budget - entry.remaining) (X86Flags.mergeFlags entry.flags flags) (168#32)
    ?_ entry.receiptUpper ((frame.lookup 7 (by decide)).trans entry.frameKnown) value
    ((frame.registers .ctrs (by decide)).trans entry.controlsKnown) observedFlags
    ((frame.registers .seg_visibles (by decide)).trans entry.visibleKnown)
    ((frame.registers .log_register_writes (by decide)).trans entry.quiet)
    entry.receiptEffective entry.receiptAligned ?_ ?_ ?_ ?_
  · change (address entry.origin.address.toInt 13).toInt + 4 = _
    rw [atOffset entry 13 (by decide), atOffset entry 17 (by decide)]
    omega
  · rw [retained]
    exact entry.loaded 10 76 rfl
  · rw [retained]
    exact entry.loaded 11 137 rfl
  · rw [retained]
    exact entry.loaded 12 183 rfl
  · intro index inside
    change current.mem.get? ((address (address entry.origin.address.toInt 13).toInt index).signExtend 52).toNat = _
    rw [retained, shifted entry 13 index (by decide)]
    have present := entry.loaded (13 + index) ((168#32).extractLsb' (8 * index) 8).toNat
      (by interval_cases index <;> rfl)
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using present

theorem writeback_frame {native : State} (entry : Entry native) (flags : BitVec 32) :
    X86StateFrame.Frame {.r14, .rflags, .rip} (X86WriteWords.written entry.receiptAddress (List.range 8))
      native (afterStore entry flags) := by
  have store := X86WriteWords.storeBytes_frame 8 (afterSub entry flags) entry.receiptAddress
    (entry.budget - entry.remaining)
  let stored := X86WriteWords.storeBytes 8 (afterSub entry flags) entry.receiptAddress
    (entry.budget - entry.remaining)
  have step := X86StateFrame.registerOnly (pointer_frame stored (address entry.origin.address.toInt 17))
  exact (((subtractionFrame entry flags).trans store).trans step).mono (by simp) (by simp)

theorem writes_receipt (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (native : State) (entry : Entry native) :
    letI : OtherOpcodeHandlers := handlers other
    letI : VectorOpcodeHandlers := vector
    ∃ flags, (X86FuelPrefix.fetches 3).run native = .ok () (afterStore entry flags) ∧
      (afterStore entry flags).regs.get? .rip = some ((address entry.origin.address.toInt 17).signExtend 64) ∧
      ∀ index < 8, (afterStore entry flags).mem.get? (X86WriteWords.physicalAddress entry.receiptAddress index) =
        some ((entry.budget - entry.remaining).extractLsb' (8 * index) 8) := by
  let : OtherOpcodeHandlers := handlers other
  let : VectorOpcodeHandlers := vector
  obtain ⟨flags, sub⟩ := subtract_allowance other vector native entry
  refine ⟨flags, ?_, X86FuelPrefix.pointer_rip _ _, ?_⟩
  · exact X86FuelPrefix.fetches_cons 2 native _ _ (load_budget other vector native entry)
      (X86FuelPrefix.fetches_cons 1 _ _ _ sub (X86FuelPrefix.fetches_one _ _
        (store_receipt other vector native entry flags)))
  · intro index inside
    rw [afterStore, (pointer_frame _ _).memory]
    exact X86WriteWords.store_word_byte _ _ _ entry.receiptUpper index inside

end Mettapedia.Machines.TIsa.X86AllowanceWriteback
