import Mettapedia.Machines.TIsa.X86AllowanceRestore
import Mettapedia.Machines.TIsa.X86P1Sub1Entry
import Mettapedia.Machines.TIsa.X86CallWrapper

/-!
# Public calls through the allowance prologue and receipt epilogue

An allowance-bearing p1 image opens with the five-register prologue, a sixth
push of RBP and two frame instructions that install `budget - receipt` in RBP.
It closes with three instructions that publish `budget - RBP` to the receipt
word, the RBP pop and the five-register epilogue. Both blocks are proved here
at any placement of their exact bytes, so every image with these blocks shares
one call contract: the entry reaches the body with the allowance installed and
the six saved words on the stack, and a body that returns to the receipt block
reaches the caller with the callee-saved registers restored and the receipt
published. Body execution and its effects remain the body's own obligation.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000

namespace Mettapedia.Machines.TIsa.X86AllowanceCall

open _root_.X86Registers X86Execution X86RegisterRefinement
open X86P1Sub1Exit (SavedStack)
local instance : MemoryPrimitives := X86Memory.ordinary

/-- `mov rbp,[rdi+0xa0]; sub rbp,[rdi+0xa8]`. -/
def setupCode : List Nat := [0x48,0x8b,0xaf,0xa0,0,0,0, 0x48,0x2b,0xaf,0xa8,0,0,0]

/-- `push rbp` followed by the allowance setup: the bytes after the five-register prologue. -/
def entryCode : List Nat := 0x55 :: setupCode

/-- `mov r14,[rdi+0xa0]; sub r14,rbp; mov [rdi+0xa8],r14`. -/
def writebackCode : List Nat := [0x4c,0x8b,0xb7,0xa0,0,0,0, 0x49,0x29,0xee, 0x4c,0x89,0xb7,0xa8,0,0,0]

/-- The receipt writeback followed by the RBP pop and the five-register epilogue. -/
def exitCode : List Nat := writebackCode ++ X86AllowanceRestore.bytes

theorem entry_length : entryCode.length = 15 := rfl
theorem exit_length : exitCode.length = 28 := rfl

/-- The saves agree with the allowance prologue the image layout check requires. -/
theorem saves_match_layout :
    (X86Prologue.expected ++ [0x55]).map (BitVec.ofNat 8) = P1Capture.allowancePrologue := by decide

/-- The restores agree with the allowance epilogue the image layout check requires. -/
theorem restores_match_layout : X86AllowanceRestore.bytes.map (BitVec.ofNat 8) = P1Capture.allowanceEpilogue := by
  decide

/-- The exit block does not begin with the five-register epilogue: the receipt write comes first. -/
theorem exit_not_plain_epilogue : exitCode.take 10 ≠ X86Epilogue.expected := by decide

theorem offset_int (start : BitVec 48) {extent : Nat} (upper : start.toInt + extent < (2 ^ 47 : Int))
    (offset : Nat) (within : offset ≤ extent) : (address start.toInt offset).toInt = start.toInt + offset :=
  address_toInt start.toInt (by simpa using BitVec.le_toInt start) upper offset within

theorem nested_address (start : Int) (offset index : Nat) :
    address (start + offset) index = address start (offset + index) := by
  simp only [address, Nat.cast_add, Int.add_assoc]

/-- The fetch window at `start + offset`. -/
def basisAt {state : State} (start : BitVec 48) (offset : Nat) {extent : Nat}
    (upper : start.toInt + extent < (2 ^ 47 : Int)) (inside : offset + 3 ≤ extent)
    (mode : X86PlainFetch.Facts state)
    (rip : state.regs.get? .rip = some ((address start.toInt offset).signExtend 64)) :
    X86LegacyFetch.Basis state where
  address := address start.toInt offset
  opcodeAddress := address start.toInt (offset + 1)
  modrmAddress := address start.toInt (offset + 2)
  next := address start.toInt (offset + 3)
  control := mode.control
  attributes := mode.attributes
  step1 := by rw [offset_int start upper _ (by omega), offset_int start upper _ (by omega)]; omega
  step2 := by rw [offset_int start upper _ (by omega), offset_int start upper _ (by omega)]; omega
  step3 := by rw [offset_int start upper _ (by omega), offset_int start upper _ inside]; omega
  status := mode.status
  fault := mode.fault
  msrs := mode.msrs
  segments := mode.segments
  longMode := mode.longMode
  codeMode := mode.codeMode
  application := mode.application
  rip := rip

/-- Mode registers survive any frame that writes only data registers. -/
def modeAfter {before after : State} {registers : Finset Register} {written : Finset Nat}
    (mode : X86PlainFetch.Facts before) (frame : X86StateFrame.Frame registers written before after)
    (data : registers ⊆ dataRegisters) : X86PlainFetch.Facts after :=
  let kept (register : Register) (outside : register ∉ dataRegisters) :=
    frame.registers register (fun member => outside (data member))
  { mode with
    status := (kept .ms_reg (by decide)).trans mode.status
    fault := (kept .fault_reg (by decide)).trans mode.fault
    msrs := (kept .msrs (by decide)).trans mode.msrs
    segments := (kept .seg_hidden_attrs (by decide)).trans mode.segments
    application := (kept .app_view (by decide)).trans mode.application }

/-- A displacement word inside loaded code. -/
theorem displacement_bytes {state : State} (start : Int) (bytes : List Nat) (loaded : codeLoaded state start bytes)
    (offset : Nat) (located : (address start offset).toInt = start + offset) (word : BitVec 32)
    (encoded : ∀ index : Fin 4, bytes[offset + index.val]? = some (word.extractLsb' (8 * index.val) 8).toNat)
    (index : Nat) (within : index < 4) :
    state.mem.get? ((address (address start offset).toInt index).signExtend 52).toNat =
      some (word.extractLsb' (8 * index) 8) := by
  rw [located, nested_address]
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using loaded _ _ (encoded ⟨index, within⟩)

namespace Setup

/-- The two allowance instructions at `start`, after the six saves. -/
structure Inputs (state : State) extends X86P1Sub1Fuel.SetupFacts state where
  mode : X86PlainFetch.Facts state
  start : BitVec 48
  upper : start.toInt + 14 < (2 ^ 47 : Int)
  loaded : codeLoaded state start.toInt setupCode
  rip : state.regs.get? .rip = some (start.signExtend 64)

def afterBudget {state : State} (input : Inputs state) : State :=
  X86Move.putPointer (put state 5 input.budget) (address input.start.toInt 7)

def afterAllowance {state : State} (input : Inputs state) (output : BitVec 32) : State :=
  X86Move.putPointer
    (X86Flags.putFlags (put (afterBudget input) 5 (input.budget - input.receipt))
      (X86Flags.mergeFlags input.flags output)) (address input.start.toInt 14)

theorem budget_frame {state : State} (input : Inputs state) :
    X86StateFrame.Frame {.rbp, .rip} ∅ state (afterBudget input) := by
  apply X86StateFrame.registerOnly
  simpa [key, afterBudget] using (X86Execution.put_frame state 5 input.budget).trans
    (X86Execution.pointer_frame _ (address input.start.toInt 7))

theorem allowance_frame {state : State} (input : Inputs state) (output : BitVec 32) :
    X86StateFrame.Frame {.rbp, .rflags, .rip} ∅ state (afterAllowance input output) := by
  have composed := (budget_frame input).trans (X86Funding.GenericMemory.subtract_to_frame 5
    (afterBudget input) (input.budget - input.receipt) (X86Flags.mergeFlags input.flags output)
    (address input.start.toInt 14))
  apply composed.mono
  · intro register member
    simp [key] at member ⊢
    tauto
  · simp

theorem allowance_flags {state : State} (input : Inputs state) (output : BitVec 32) :
    (afterAllowance input output).regs.get? .rflags = some (X86Flags.mergeFlags input.flags output) := by
  rw [afterAllowance, (X86Execution.pointer_frame _ _).registers .rflags (by decide)]
  simp [X86Flags.putFlags]

theorem allowance_control {state : State} (input : Inputs state) (output : BitVec 32) :
    X86ControlFlags.Preserved state (afterAllowance input output) := by
  unfold X86ControlFlags.Preserved
  rw [allowance_flags, input.flagsKnown]
  simp only [Option.map_some, X86ControlFlags.arithmetic_mask]

theorem allowance_value {state : State} (input : Inputs state) (output : BitVec 32) :
    lookup (afterAllowance input output) 5 = some (input.budget - input.receipt) := by
  rw [afterAllowance, X86Move.lookup_putPointer,
    (X86Execution.flags_frame _ _).lookup 5 (by decide), lookup_put_same]

theorem code_byte {state : State} (input : Inputs state) (index : Nat) (value : BitVec 8)
    (present : setupCode[index]? = some value.toNat) :
    state.mem.get? ((address input.start.toInt index).signExtend 52).toNat = some value := by
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using input.loaded index value.toNat present

theorem loads_budget (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (input : Inputs state) :
    letI : OtherOpcodeHandlers := X86P1Sub1Fuel.handlers other
    letI : VectorOpcodeHandlers := vector
    (Functions.x86_fetch_decode_execute ()).run state = .ok () (afterBudget input) := by
  have start : address input.start.toInt 0 = input.start := by simp [address]
  let origin := basisAt input.start 0 input.upper (by decide) input.mode (by rw [start]; exact input.rip)
  have offset3 := offset_int input.start input.upper 3 (by decide)
  have offset7 := offset_int input.start input.upper 7 (by decide)
  refine X86FrameLoad.fetched_frame (X86Funding.GenericMemory.linkedHandlers other) vector state 5
    origin (address input.start.toInt 7) input.budgetAddress input.visible input.controls
    input.frame input.budget input.flags (160#32) ?_ input.budgetUpper input.frameKnown
    input.controlsKnown input.flagsKnown input.visibleKnown input.quiet input.budgetEffective input.budgetAligned
    (code_byte input 0 _ rfl) (code_byte input 1 _ rfl) (code_byte input 2 _ rfl) ?_ input.budgetPresent
  · change (address input.start.toInt 3).toInt + 4 = (address input.start.toInt 7).toInt
    omega
  · exact displacement_bytes input.start.toInt setupCode input.loaded 3 offset3 (160#32)
      (by intro index; fin_cases index <;> rfl)

theorem subtracts_receipt (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (input : Inputs state) :
    letI : OtherOpcodeHandlers := X86P1Sub1Fuel.handlers other
    letI : VectorOpcodeHandlers := vector
    ∃ output, (Functions.x86_fetch_decode_execute ()).run (afterBudget input) =
      .ok () (afterAllowance input output) := by
  let middle := afterBudget input
  have frame := budget_frame input
  let mode : X86PlainFetch.Facts middle := modeAfter input.mode frame (by decide)
  let origin := basisAt input.start 7 input.upper (by decide) mode (X86FuelPrefix.pointer_rip _ _)
  have offset10 := offset_int input.start input.upper 10 (by decide)
  have offset14 := offset_int input.start input.upper 14 (by decide)
  have loaded : codeLoaded middle input.start.toInt setupCode :=
    frame.codeLoaded _ _ input.loaded (by intros; simp)
  have known : lookup middle 5 = some input.budget := by
    simp only [middle, afterBudget, X86Move.lookup_putPointer, lookup_put_same]
  have codeByte (index : Nat) (value : BitVec 8) (present : setupCode[index]? = some value.toNat) :
      middle.mem.get? ((address input.start.toInt index).signExtend 52).toNat = some value := by
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using loaded index value.toNat present
  refine X86Funding.GenericMemory.fetched_subtract_to 5 (X86FrameLoad.linkedHandlers other) vector
    middle origin (address input.start.toInt 14) input.receiptAddress input.visible input.controls
    input.frame input.budget input.receipt input.flags (168#32) ?_ input.receiptUpper
    ((frame.lookup 7 (by decide)).trans input.frameKnown) known
    ((frame.registers .ctrs (by decide)).trans input.controlsKnown)
    ((frame.registers .rflags (by decide)).trans input.flagsKnown)
    ((frame.registers .seg_visibles (by decide)).trans input.visibleKnown)
    ((frame.registers .log_register_writes (by decide)).trans input.quiet)
    input.receiptEffective input.receiptAligned (codeByte 7 _ rfl) (codeByte 8 _ rfl) (codeByte 9 _ rfl) ?_ ?_
  · change (address input.start.toInt 10).toInt + 4 = (address input.start.toInt 14).toInt
    omega
  · exact displacement_bytes input.start.toInt setupCode loaded 10 offset10 (168#32)
      (by intro index; fin_cases index <;> rfl)
  · intro index inside
    rw [frame.memory _ (by simp)]
    exact input.receiptPresent index inside

theorem initializes (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (input : Inputs state) :
    letI : OtherOpcodeHandlers := X86P1Sub1Fuel.handlers other
    letI : VectorOpcodeHandlers := vector
    ∃ output, (X86FuelPrefix.fetches 2).run state = .ok () (afterAllowance input output) := by
  let : OtherOpcodeHandlers := X86P1Sub1Fuel.handlers other
  let : VectorOpcodeHandlers := vector
  obtain ⟨output, second⟩ := subtracts_receipt other vector state input
  exact ⟨output, X86FuelPrefix.fetches_then 1 1 state (afterBudget input) _
    (X86FuelPrefix.fetches_one _ _ (loads_budget other vector state input))
    (X86FuelPrefix.fetches_one _ _ second)⟩

end Setup

namespace Writeback

/-- The three receipt instructions at `start`, before the RBP pop. -/
structure Inputs (state : State) extends X86P1Sub1Fuel.Receipt.Facts state where
  mode : X86PlainFetch.Facts state
  start : BitVec 48
  upper : start.toInt + 17 < (2 ^ 47 : Int)
  loaded : codeLoaded state start.toInt writebackCode
  rip : state.regs.get? .rip = some (start.signExtend 64)

def afterBudget {state : State} (input : Inputs state) : State :=
  X86Move.putPointer (put state 14 input.budget) (address input.start.toInt 7)

def afterDifference {state : State} (input : Inputs state) (output : BitVec 32) : State :=
  X86Move.putPointer
    (X86Flags.putFlags (put (afterBudget input) 14 (input.budget - input.remaining))
      (X86Flags.mergeFlags input.flags output)) (address input.start.toInt 10)

noncomputable def afterWrite {state : State} (input : Inputs state) (output : BitVec 32) : State :=
  X86Move.putPointer (X86WriteWords.storeBytes 8 (afterDifference input output)
    input.receiptAddress (input.budget - input.remaining)) (address input.start.toInt 17)

theorem budget_frame {state : State} (input : Inputs state) :
    X86StateFrame.Frame {.r14, .rip} ∅ state (afterBudget input) := by
  apply X86StateFrame.registerOnly
  have step := (X86Execution.put_frame state 14 input.budget).trans
    (X86Execution.pointer_frame _ (address input.start.toInt 7))
  apply step.mono
  simp [key]

theorem difference_frame {state : State} (input : Inputs state) (output : BitVec 32) :
    X86StateFrame.Frame {.r14, .rflags, .rip} ∅ state (afterDifference input output) := by
  have step := X86Funding.GenericMemory.subtract_to_frame 14 (afterBudget input)
    (input.budget - input.remaining) (X86Flags.mergeFlags input.flags output) (address input.start.toInt 10)
  apply ((budget_frame input).trans step).mono
  · intro register member
    simp [key] at member ⊢
    tauto
  · simp

theorem loads_budget (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (input : Inputs state) :
    letI : OtherOpcodeHandlers := X86P1Sub1Fuel.Receipt.handlers other
    letI : VectorOpcodeHandlers := vector
    (Functions.x86_fetch_decode_execute ()).run state = .ok () (afterBudget input) := by
  have start : address input.start.toInt 0 = input.start := by simp [address]
  let origin := basisAt input.start 0 input.upper (by decide) input.mode (by rw [start]; exact input.rip)
  have offset3 := offset_int input.start input.upper 3 (by decide)
  have offset7 := offset_int input.start input.upper 7 (by decide)
  have codeByte (index : Nat) (value : BitVec 8) (present : writebackCode[index]? = some value.toNat) :
      state.mem.get? ((address input.start.toInt index).signExtend 52).toNat = some value := by
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using input.loaded index value.toNat present
  refine X86FrameLoad.fetched_frame (X86Arithmetic.linkedHandlers other) vector state 14
    origin (address input.start.toInt 7) input.budgetAddress input.visible input.controls
    input.frame input.budget input.flags (160#32) ?_ input.budgetUpper input.frameKnown
    input.controlsKnown input.flagsKnown input.visibleKnown input.quiet input.budgetEffective input.budgetAligned
    (codeByte 0 _ rfl) (codeByte 1 _ rfl) (codeByte 2 _ rfl) ?_ input.budgetPresent
  · change (address input.start.toInt 3).toInt + 4 = (address input.start.toInt 7).toInt
    omega
  · exact displacement_bytes input.start.toInt writebackCode input.loaded 3 offset3 (160#32)
      (by intro index; fin_cases index <;> rfl)

theorem subtracts_remaining (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (input : Inputs state) :
    letI : OtherOpcodeHandlers := X86P1Sub1Fuel.Receipt.handlers other
    letI : VectorOpcodeHandlers := vector
    ∃ output, (Functions.x86_fetch_decode_execute ()).run (afterBudget input) =
      .ok () (afterDifference input output) := by
  let current := afterBudget input
  have frame := budget_frame input
  let origin := basisAt input.start 7 input.upper (by decide) (modeAfter input.mode frame (by decide))
    (X86FuelPrefix.pointer_rip _ _)
  have loaded : codeLoaded current input.start.toInt writebackCode :=
    frame.codeLoaded _ _ input.loaded (by intros; simp)
  have codeByte (index : Nat) (value : BitVec 8) (present : writebackCode[index]? = some value.toNat) :
      current.mem.get? ((address input.start.toInt index).signExtend 52).toNat = some value := by
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using loaded index value.toNat present
  let window : X86LegacyFetch.Window current (X86Arithmetic.opcode .sub) true 5 14 := {
    toBasis := origin
    prefixByte := codeByte 7 _ rfl
    opcodeByte := codeByte 8 _ rfl
    modrmByte := codeByte 9 _ rfl }
  have budget : lookup current 14 = some input.budget := by
    simp only [current, afterBudget, X86Move.lookup_putPointer, lookup_put_same]
  exact X86Arithmetic.fetched_register64 (X86FrameLoad.linkedHandlers other) vector .sub current 5 14
    window input.budget input.remaining input.flags ((frame.lookup 5 (by decide)).trans input.remainingKnown)
    budget ((frame.registers .rflags (by decide)).trans input.flagsKnown)
    ((frame.registers .log_register_writes (by decide)).trans input.quiet)

theorem stores_receipt (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (input : Inputs state) (output : BitVec 32) :
    letI : OtherOpcodeHandlers := X86P1Sub1Fuel.Receipt.handlers other
    letI : VectorOpcodeHandlers := vector
    (Functions.x86_fetch_decode_execute ()).run (afterDifference input output) = .ok () (afterWrite input output) := by
  let current := afterDifference input output
  have frame := difference_frame input output
  let origin := basisAt input.start 10 input.upper (by decide) (modeAfter input.mode frame (by decide))
    (X86FuelPrefix.pointer_rip _ _)
  have loaded : codeLoaded current input.start.toInt writebackCode :=
    frame.codeLoaded _ _ input.loaded (by intros; simp)
  have codeByte (index : Nat) (value : BitVec 8) (present : writebackCode[index]? = some value.toNat) :
      current.mem.get? ((address input.start.toInt index).signExtend 52).toNat = some value := by
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using loaded index value.toNat present
  have value : lookup current 14 = some (input.budget - input.remaining) := by
    rw [show current = afterDifference input output from rfl, afterDifference, X86Move.lookup_putPointer,
      (X86Execution.flags_frame _ _).lookup 14 (by decide), lookup_put_same]
  have flags : current.regs.get? .rflags = some (X86Flags.mergeFlags input.flags output) := by
    rw [show current = afterDifference input output from rfl, afterDifference,
      (X86Execution.pointer_frame _ _).registers _ (by decide)]
    simp [X86Flags.putFlags]
  have offset13 := offset_int input.start input.upper 13 (by decide)
  have offset17 := offset_int input.start input.upper 17 (by decide)
  refine X86FrameStore.fetched_register (X86P1Sub1Fuel.Receipt.handlers other) vector current 14 origin
    (address input.start.toInt 17) input.receiptAddress input.visible input.controls input.frame
    (input.budget - input.remaining) (X86Flags.mergeFlags input.flags output) (168#32) ?_ input.receiptUpper
    ((frame.lookup 7 (by decide)).trans input.frameKnown) value
    ((frame.registers .ctrs (by decide)).trans input.controlsKnown) flags
    ((frame.registers .seg_visibles (by decide)).trans input.visibleKnown)
    ((frame.registers .log_register_writes (by decide)).trans input.quiet)
    input.receiptEffective input.receiptAligned (codeByte 10 _ rfl) (codeByte 11 _ rfl) (codeByte 12 _ rfl) ?_
  · change (address input.start.toInt 13).toInt + 4 = (address input.start.toInt 17).toInt
    omega
  · exact displacement_bytes input.start.toInt writebackCode loaded 13 offset13 (168#32)
      (by intro index; fin_cases index <;> rfl)

theorem write_frame {state : State} (input : Inputs state) (output : BitVec 32) :
    X86StateFrame.Frame {.r14, .rflags, .rip} (X86WriteWords.written input.receiptAddress (List.range 8))
      state (afterWrite input output) := by
  let stored := X86WriteWords.storeBytes 8 (afterDifference input output) input.receiptAddress
    (input.budget - input.remaining)
  have write := X86WriteWords.storeBytes_frame 8 (afterDifference input output) input.receiptAddress
    (input.budget - input.remaining)
  have advance := X86StateFrame.registerOnly (X86Execution.pointer_frame stored (address input.start.toInt 17))
  apply (((difference_frame input output).trans write).trans advance).mono
  · simp
  · simp

theorem written_byte {state : State} (input : Inputs state) (output : BitVec 32) (index : Nat) (within : index < 8) :
    (afterWrite input output).mem.get? (X86WriteWords.physicalAddress input.receiptAddress index) =
      some ((input.budget - input.remaining).extractLsb' (8 * index) 8) := by
  rw [afterWrite, (X86Execution.pointer_frame _ _).memory]
  exact X86WriteWords.store_word_byte (afterDifference input output) input.receiptAddress
    (input.budget - input.remaining) input.receiptUpper index within

theorem flags_after_write {state : State} (input : Inputs state) (output : BitVec 32) :
    (afterWrite input output).regs.get? .rflags = some (X86Flags.mergeFlags input.flags output) := by
  rw [afterWrite, (X86Execution.pointer_frame _ _).registers .rflags (by decide),
    (X86WriteWords.storeBytes_frame 8 _ _ _).registers .rflags (by simp),
    afterDifference, (X86Execution.pointer_frame _ _).registers .rflags (by decide)]
  simp [X86Flags.putFlags]

theorem publishes (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (input : Inputs state) :
    letI : OtherOpcodeHandlers := X86P1Sub1Fuel.Receipt.handlers other
    letI : VectorOpcodeHandlers := vector
    ∃ output, (X86FuelPrefix.fetches 3).run state = .ok () (afterWrite input output) ∧
      (afterWrite input output).regs.get? .rip = some ((address input.start.toInt 17).signExtend 64) ∧
      X86StateFrame.Frame {.r14, .rflags, .rip} (X86WriteWords.written input.receiptAddress (List.range 8))
        state (afterWrite input output) ∧
      ∀ index < 8, (afterWrite input output).mem.get? (X86WriteWords.physicalAddress input.receiptAddress index) =
        some ((input.budget - input.remaining).extractLsb' (8 * index) 8) := by
  let : OtherOpcodeHandlers := X86P1Sub1Fuel.Receipt.handlers other
  let : VectorOpcodeHandlers := vector
  obtain ⟨output, subtract⟩ := subtracts_remaining other vector state input
  have load := X86FuelPrefix.fetches_one _ _ (loads_budget other vector state input)
  have sub := X86FuelPrefix.fetches_one _ _ subtract
  have store := X86FuelPrefix.fetches_one _ _ (stores_receipt other vector state input output)
  exact ⟨output, X86FuelPrefix.fetches_then 2 1 state (afterDifference input output) _
    (X86FuelPrefix.fetches_then 1 1 state (afterBudget input) _ load sub) store,
    X86FuelPrefix.pointer_rip _ _, write_frame input output, written_byte input output⟩

end Writeback

abbrev spillBytes (fiveBottom bottom : BitVec 48) : Finset Nat :=
  X86Prologue.writes fiveBottom ∪ X86WriteWords.written bottom (List.range 8)

abbrev receiptBytes (address : BitVec 48) : Finset Nat := X86WriteWords.written address (List.range 8)

/-- Observations at a public allowance call: the caller's stack and registers, the allowance
frame words, and the placed entry and exit blocks. -/
structure Inputs (state : State) where
  prologue : X86Prologue.Inputs state
  bottom : BitVec 48
  savedRbp : Word
  rbpKnown : lookup state 5 = some savedRbp
  step : bottom.toInt + 8 = prologue.bottom.toInt
  aligned : bottom &&& (7#48) = 0#48
  codeUpper : prologue.code.toInt + 24 < (2 ^ 47 : Int)
  entryLoaded : codeLoaded state (prologue.code.toInt + 9) entryCode
  entrySafe : ∀ index byte, entryCode[index]? = some byte →
    ((address (prologue.code.toInt + 9) index).signExtend 52).toNat ∉ spillBytes prologue.bottom bottom
  fuel : X86P1Sub1Fuel.SetupFacts state
  budgetSafe : ∀ n < 8, X86WriteWords.physicalAddress fuel.budgetAddress n ∉ spillBytes prologue.bottom bottom
  receiptSafe : ∀ n < 8, X86WriteWords.physicalAddress fuel.receiptAddress n ∉ spillBytes prologue.bottom bottom
  exit : BitVec 48
  exitUpper : exit.toInt + 28 < (2 ^ 47 : Int)
  exitLoaded : codeLoaded state exit.toInt exitCode
  exitSafe : ∀ index byte, exitCode[index]? = some byte →
    ((address exit.toInt index).signExtend 52).toNat ∉ spillBytes prologue.bottom bottom

namespace Inputs

variable {state : State} (call : Inputs state)

noncomputable def saved : State :=
  X86P1Sub1Allowance.afterSaves state call.prologue call.bottom call.savedRbp

theorem saved_frame : X86StateFrame.Frame {.rsp, .rip} (spillBytes call.prologue.bottom call.bottom) state call.saved :=
  X86P1Sub1Allowance.six_saves_frame state call.prologue call.bottom call.savedRbp

theorem code_offset (offset : Nat) (within : offset ≤ 24) :
    (address call.prologue.code.toInt offset).toInt = call.prologue.code.toInt + offset :=
  offset_int call.prologue.code call.codeUpper offset within

theorem saves (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := X86Stack.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    (X86FuelPrefix.fetches 6).run state = .ok () call.saved := by
  let : OtherOpcodeHandlers := X86Stack.linkedHandlers other
  let : VectorOpcodeHandlers := vector
  let middle := X86Prologue.finished state call.prologue
  have frame := X86Prologue.finished_frame state call.prologue
  have rip : middle.regs.get? .rip = some ((address call.prologue.code.toInt 9).signExtend 64) := by
    simpa [middle, X86Prologue.stage, X86Prologue.offset, X86Prologue.codeAt] using
      X86Prologue.stage_rip state call.prologue (5 : Fin 6)
  have stackKnown : lookup middle 4 = some (call.prologue.bottom.signExtend 64) := by
    simpa [middle, X86Prologue.stage, X86Prologue.stackAt, address, BitVec.ofInt_toInt] using
      X86Prologue.stage_stack state call.prologue (5 : Fin 6)
  have pushByte : middle.mem.get? ((address call.prologue.code.toInt 9).signExtend 52).toNat = some (X86Stack.pushOpcode 5) := by
    have loaded := frame.codeLoaded _ _ call.entryLoaded
      (fun index byte present => fun member => call.entrySafe index byte present (Finset.mem_union_left _ member))
    have byte := loaded 0 0x55 rfl
    have point : address (call.prologue.code.toInt + 9) 0 = address call.prologue.code.toInt 9 := by
      unfold address
      congr 1
      omega
    rw [point] at byte
    rw [byte]
    rfl
  have fetch := X86Stack.fetched_push other vector middle 5 (X86Prologue.stageContext state call.prologue (5 : Fin 6))
    (address call.prologue.code.toInt 9) (address call.prologue.code.toInt 9) (address call.prologue.code.toInt 10) call.prologue.bottom call.bottom
    call.savedRbp call.prologue.visible call.prologue.controls call.prologue.flags (by simp) (by
      rw [call.code_offset 9 (by decide), call.code_offset 10 (by decide)]
      simp [X86Stack.pushLength]
      omega) call.step
    (by rw [call.step]; have bound := call.prologue.stackUpper; omega) rip stackKnown
    ((frame.lookup 5 (by decide)).trans call.rbpKnown)
    ((frame.registers .ctrs (by decide)).trans call.prologue.controlsKnown)
    ((frame.registers .rflags (by decide)).trans call.prologue.flagsKnown)
    ((frame.registers .seg_visibles (by decide)).trans call.prologue.visibleKnown)
    ((frame.registers .log_register_writes (by decide)).trans call.prologue.quiet) call.aligned
    (fun high => (high (by decide)).elim) pushByte
  exact X86FuelPrefix.fetches_then 5 1 state middle call.saved
    (X86Prologue.executes other vector state call.prologue) (X86FuelPrefix.fetches_one _ _ fetch)

noncomputable def setup : Setup.Inputs call.saved := by
  let framed := call.saved_frame
  let data : ({.rsp, .rip} : Finset Register) ⊆ dataRegisters := by decide
  refine {
    toSetupFacts :=
      { call.fuel with
        frameKnown := (framed.lookup 7 (by decide)).trans call.fuel.frameKnown
        budgetPresent := fun n h => (framed.memory _ (call.budgetSafe n h)).trans (call.fuel.budgetPresent n h)
        receiptPresent := fun n h => (framed.memory _ (call.receiptSafe n h)).trans (call.fuel.receiptPresent n h)
        visibleKnown := (framed.registers .seg_visibles (by decide)).trans call.fuel.visibleKnown
        controlsKnown := (framed.registers .ctrs (by decide)).trans call.fuel.controlsKnown
        flagsKnown := (framed.registers .rflags (by decide)).trans call.fuel.flagsKnown
        quiet := (framed.registers .log_register_writes (by decide)).trans call.fuel.quiet }
    mode := modeAfter call.prologue.context framed data
    start := address call.prologue.code.toInt 10
    upper := by rw [call.code_offset 10 (by decide)]; have := call.codeUpper; omega
    loaded := ?_
    rip := ?_ }
  · have loaded := framed.codeLoaded _ _ call.entryLoaded call.entrySafe
    have tail := X86FetchEntry.codeLoaded_right call.saved _ [0x55] setupCode loaded
    rw [call.code_offset 10 (by decide)]
    simpa [Int.add_assoc] using tail
  · rw [saved, X86P1Sub1Allowance.afterSaves, X86Stack.pushResult, X86FuelPrefix.pointer_rip,
      X86P1Sub1Allowance.save_offset]

/-- The body state: six saves done and the allowance installed in RBP. -/
noncomputable def entered (output : BitVec 32) : State := Setup.afterAllowance call.setup output

theorem entered_frame (output : BitVec 32) :
    X86StateFrame.Frame {.rsp, .rip, .rbp, .rflags} (spillBytes call.prologue.bottom call.bottom)
      state (call.entered output) :=
  (call.saved_frame.trans (Setup.allowance_frame call.setup output)).mono (by decide) (by simp)

theorem entered_rip (output : BitVec 32) :
    (call.entered output).regs.get? .rip = some ((address call.prologue.code.toInt 24).signExtend 64) := by
  rw [entered, Setup.afterAllowance, X86FuelPrefix.pointer_rip]
  congr 2
  change address (address call.prologue.code.toInt 10).toInt 14 = _
  rw [call.code_offset 10 (by decide), nested_address]

theorem entered_allowance (output : BitVec 32) :
    lookup (call.entered output) 5 = some (call.fuel.budget - call.fuel.receipt) :=
  Setup.allowance_value call.setup output

theorem entered_flags (output : BitVec 32) :
    (call.entered output).regs.get? .rflags = some (X86Flags.mergeFlags call.fuel.flags output) :=
  Setup.allowance_flags call.setup output

theorem entered_control (output : BitVec 32) : X86ControlFlags.Preserved state (call.entered output) := by
  have saved : X86ControlFlags.Preserved state call.saved := by
    unfold X86ControlFlags.Preserved
    rw [call.saved_frame.registers .rflags (by decide)]
  exact saved.trans (Setup.allowance_control call.setup output)

noncomputable def enteredMode (output : BitVec 32) : X86PlainFetch.Facts (call.entered output) :=
  modeAfter call.prologue.context (call.entered_frame output) (by decide)

/-- The six saved words at the body state. -/
noncomputable def stack (output : BitVec 32) : SavedStack (call.entered output) :=
  let prior := X86P1Sub1Entry.savedStack state call.prologue call.bottom call.savedRbp call.step call.aligned
  let frame := Setup.allowance_frame call.setup output
  { prior with
    current := (frame.lookup 4 (by decide)).trans prior.current
    bottomBytes := fun index within => (frame.memory _ (by simp)).trans (prior.bottomBytes index within)
    present := fun slot index within => (frame.memory _ (by simp)).trans (prior.present slot index within) }

theorem enters (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := X86Stack.linkedHandlers (X86P1Sub1Fuel.handlers other)
    letI : VectorOpcodeHandlers := vector
    ∃ output, (X86FuelPrefix.fetches 8).run state = .ok () (call.entered output) := by
  let : OtherOpcodeHandlers := X86Stack.linkedHandlers (X86P1Sub1Fuel.handlers other)
  let : VectorOpcodeHandlers := vector
  have saves := call.saves (X86P1Sub1Fuel.handlers other) vector
  obtain ⟨output, setup⟩ := Setup.initializes (X86Stack.linkedHandlers other) vector call.saved call.setup
  exact ⟨output, X86FuelPrefix.fetches_then 6 2 state call.saved _ saves setup⟩

end Inputs

/-- Registers a body may change; RSP and the frame register RDI are kept for the exit block. -/
abbrev bodyRegisters : Finset Register :=
  {.rax, .rbx, .rcx, .rdx, .rsi, .rbp, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15, .rflags, .rip}

/-- A body run from the entered state that reaches the exit block. -/
structure Exit {state : State} (call : Inputs state) (output : BitVec 32) (written : Finset Nat) (body : State) where
  frame : X86StateFrame.Frame bodyRegisters written (call.entered output) body
  remaining : Word
  remainingKnown : lookup body 5 = some remaining
  flags : BitVec 32
  flagsKnown : body.regs.get? .rflags = some flags
  budgetSafe : ∀ n < 8, X86WriteWords.physicalAddress call.fuel.budgetAddress n ∉ written
  bottomSafe : ∀ n < 8, X86WriteWords.physicalAddress call.bottom n ∉ written ∪ receiptBytes call.fuel.receiptAddress
  savedSafe : ∀ slot : Fin 6, ∀ n < 8,
    X86WriteWords.physicalAddress (address call.prologue.bottom.toInt (8 * slot.val)) n ∉
      written ∪ receiptBytes call.fuel.receiptAddress
  exitSafe : ∀ index byte, exitCode[index]? = some byte →
    ((address call.exit.toInt index).signExtend 52).toNat ∉ written ∪ receiptBytes call.fuel.receiptAddress
  pointer : body.regs.get? .rip = some (call.exit.signExtend 64)

/-- Caller-visible result of a complete allowance call. -/
structure Result {state : State} (call : Inputs state) (written : Finset Nat) (remaining : Word)
    (body after : State) : Prop where
  pointer : after.regs.get? .rip = some (call.prologue.returnAddress.signExtend 64)
  stackPointer : lookup after 4 = some ((address call.bottom.toInt 56).signExtend 64)
  rbp : lookup after 5 = some call.savedRbp
  saved : ∀ slot : Fin 5, lookup after (X86Epilogue.target slot) = some (X86Prologue.epilogueSaved call.prologue slot)
  value : lookup after 0 = lookup body 0
  receipt : ∀ n < 8, after.mem.get? (X86WriteWords.physicalAddress call.fuel.receiptAddress n) =
    some ((call.fuel.budget - remaining).extractLsb' (8 * n) 8)
  tail : X86StateFrame.Frame (insert .rbp (insert .r14 (insert .rflags X86Epilogue.clobbers)))
    (receiptBytes call.fuel.receiptAddress) body after
  frame : X86StateFrame.Frame X86CallWrapper.callerRegisters
    (spillBytes call.prologue.bottom call.bottom ∪ written ∪ receiptBytes call.fuel.receiptAddress) state after

namespace Inputs

variable {state : State} (call : Inputs state)

/-- Receipt facts at the exit block. -/
noncomputable def writeback {output : BitVec 32} {written : Finset Nat} {body : State}
    (exit : Exit call output written body) : Writeback.Inputs body :=
  let entered := call.entered_frame output
  let framed := exit.frame
  let fuel := call.fuel
  let kept (register : Register) (outside : register ∉ dataRegisters) :=
    (framed.registers register (fun member => outside ((show bodyRegisters ⊆ dataRegisters from by decide) member))).trans
      (entered.registers register (fun member => outside ((show ({.rsp, .rip, .rbp, .rflags} : Finset Register) ⊆
        dataRegisters from by decide) member)))
  { frame := fuel.frame
    frameKnown := (framed.lookup 7 (by decide)).trans ((entered.lookup 7 (by decide)).trans fuel.frameKnown)
    budgetAddress := fuel.budgetAddress
    budgetUpper := fuel.budgetUpper
    budgetEffective := fuel.budgetEffective
    budgetAligned := fuel.budgetAligned
    budget := fuel.budget
    budgetPresent := fun n h => (framed.memory _ (exit.budgetSafe n h)).trans
      ((entered.memory _ (call.budgetSafe n h)).trans (fuel.budgetPresent n h))
    receiptAddress := fuel.receiptAddress
    receiptUpper := fuel.receiptUpper
    receiptEffective := fuel.receiptEffective
    receiptAligned := fuel.receiptAligned
    remaining := exit.remaining
    remainingKnown := exit.remainingKnown
    visible := fuel.visible
    controls := fuel.controls
    flags := exit.flags
    visibleKnown := (kept .seg_visibles (by decide)).trans fuel.visibleKnown
    controlsKnown := (kept .ctrs (by decide)).trans fuel.controlsKnown
    flagsKnown := exit.flagsKnown
    quiet := (kept .log_register_writes (by decide)).trans fuel.quiet
    mode := modeAfter (call.enteredMode output) framed (by decide)
    start := call.exit
    upper := by have := call.exitUpper; omega
    loaded := by
      have first := entered.codeLoaded _ _ call.exitLoaded call.exitSafe
      have second := framed.codeLoaded _ _ first
        (fun index byte present member => exit.exitSafe index byte present (Finset.mem_union_left _ member))
      exact X86FetchEntry.codeLoaded_left body _ writebackCode X86AllowanceRestore.bytes second
    rip := exit.pointer }

theorem restore_bytes {output : BitVec 32} {written : Finset Nat} {body : State}
    (exit : Exit call output written body) (later : State)
    (receiptFrame : X86StateFrame.Frame {.r14, .rflags, .rip} (receiptBytes call.fuel.receiptAddress) body later) :
    codeLoaded later (address call.exit.toInt 17).toInt X86AllowanceRestore.bytes := by
  have first := (call.entered_frame output).codeLoaded _ _ call.exitLoaded call.exitSafe
  have second := exit.frame.codeLoaded _ _ first
    (fun index byte present member => exit.exitSafe index byte present (Finset.mem_union_left _ member))
  have third := receiptFrame.codeLoaded _ _ second
    (fun index byte present member => exit.exitSafe index byte present (Finset.mem_union_right _ member))
  have right := X86FetchEntry.codeLoaded_right later _ writebackCode X86AllowanceRestore.bytes third
  rw [offset_int call.exit call.exitUpper 17 (by decide)]
  exact right

/-- The six saved words survive the body and the receipt write. -/
noncomputable def exitStack {output : BitVec 32} {written : Finset Nat} {body later : State}
    (exit : Exit call output written body)
    (receiptFrame : X86StateFrame.Frame {.r14, .rflags, .rip} (receiptBytes call.fuel.receiptAddress) body later) :
    SavedStack later :=
  let prior := call.stack output
  let joined := (exit.frame.trans receiptFrame)
  { prior with
    current := (joined.lookup 4 (by decide)).trans prior.current
    bottomBytes := fun index within => (joined.memory _ (exit.bottomSafe index within)).trans (prior.bottomBytes index within)
    present := fun slot index within => (joined.memory _ (exit.savedSafe slot index within)).trans
      (prior.present slot index within) }

theorem saved_registers_restored (after : State)
    (saved : ∀ slot : Fin 5, lookup after (X86Epilogue.target slot) = some (X86Prologue.epilogueSaved call.prologue slot))
    (rbp : lookup after 5 = some call.savedRbp) :
    ∀ register ∈ insert .rbp X86CallWrapper.savedRegisters, after.regs.get? register = state.regs.get? register := by
  intro register member
  rcases Finset.mem_insert.mp member with same | member
  · subst register
    exact X86CallWrapper.lookup_register_equal state after 5 (rbp.trans call.rbpKnown.symm)
  · obtain ⟨index, rfl⟩ := X86CallWrapper.saved_enumeration register member
    have restored : lookup after (X86Prologue.source index) = some (call.prologue.saved index) := by
      fin_cases index
      · exact saved 4
      · exact saved 3
      · exact saved 2
      · exact saved 1
      · exact saved 0
    exact X86CallWrapper.lookup_register_equal state after _ (restored.trans (call.prologue.savedKnown index).symm)

abbrev exitDispatch (other : OtherOpcodeHandlers) : OtherOpcodeHandlers :=
  X86P1Sub1Fuel.Receipt.handlers (X86Stack.linkedHandlers other)

/-- The exit block publishes the receipt and returns to the caller in ten fetched instructions. -/
theorem returns (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    {output : BitVec 32} {written : Finset Nat} {body : State} (exit : Exit call output written body) :
    letI : OtherOpcodeHandlers := exitDispatch other
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 10).run body = .ok () after ∧ Result call written exit.remaining body after := by
  let : OtherOpcodeHandlers := exitDispatch other
  let : VectorOpcodeHandlers := vector
  let receipt := call.writeback exit
  obtain ⟨flagsOutput, published, publishedRip, receiptFrame, receiptBytesWritten⟩ :=
    Writeback.publishes (X86Stack.linkedHandlers other) vector body receipt
  let middle := Writeback.afterWrite receipt flagsOutput
  have middleFrame : X86StateFrame.Frame {.r14, .rflags, .rip} (receiptBytes call.fuel.receiptAddress) body middle :=
    receiptFrame
  let saved := call.exitStack exit middleFrame
  let kept (register : Register) (outside : register ∉ ({.r14, .rflags, .rip} : Finset Register)) :=
    middleFrame.registers register outside
  let entry : X86AllowanceRestore.Entry middle := {
    toSavedStack := saved
    mode := modeAfter receipt.mode middleFrame (by decide)
    code := address call.exit.toInt 17
    codeUpper := by rw [offset_int call.exit call.exitUpper 17 (by decide)]; have := call.exitUpper; omega
    rip := publishedRip
    loaded := call.restore_bytes exit middle middleFrame
    visible := receipt.visible
    controls := receipt.controls
    flags := X86Flags.mergeFlags receipt.flags flagsOutput
    visibleKnown := (kept .seg_visibles (by decide)).trans receipt.visibleKnown
    controlsKnown := (kept .ctrs (by decide)).trans receipt.controlsKnown
    flagsKnown := Writeback.flags_after_write receipt flagsOutput
    quiet := (kept .log_register_writes (by decide)).trans receipt.quiet }
  obtain ⟨after, restored, restoreFrame, pointer, stackPointer, rbp, savedRead⟩ :=
    X86AllowanceRestore.restores (X86P1Sub1Fuel.Receipt.handlers other) vector middle entry
  have tail : X86StateFrame.Frame (insert .rbp (insert .r14 (insert .rflags X86Epilogue.clobbers)))
      (receiptBytes call.fuel.receiptAddress) body after :=
    (middleFrame.trans (X86StateFrame.registerOnly restoreFrame)).mono (by decide) (by simp)
  have rbpRestored : lookup after 5 = some call.savedRbp := rbp
  have savedRestored : ∀ slot : Fin 5, lookup after (X86Epilogue.target slot) =
      some (X86Prologue.epilogueSaved call.prologue slot) := savedRead
  have allFrame := ((call.entered_frame output).trans exit.frame).trans tail
  refine ⟨after, X86FuelPrefix.fetches_then 3 7 body middle after published restored, ?_⟩
  refine {
    pointer := pointer
    stackPointer := ?_
    rbp := rbpRestored
    saved := savedRestored
    value := tail.lookup 0 (by decide)
    receipt := fun n h => (restoreFrame.memory ▸ receiptBytesWritten n h)
    tail := tail
    frame := ?_ }
  · rw [stackPointer]
    congr 2
    change address call.prologue.bottom.toInt 48 = address call.bottom.toInt 56
    unfold address
    congr 1
    have := call.step
    omega
  · have cover : ({.rsp, .rip, .rbp, .rflags} ∪ bodyRegisters ∪
        insert .rbp (insert .r14 (insert .rflags X86Epilogue.clobbers)) : Finset Register) ⊆
        X86CallWrapper.callerRegisters ∪ insert .rbp X86CallWrapper.savedRegisters := by decide
    refine { allFrame with registers := fun register outside => ?_ }
    by_cases kept : register ∈ insert .rbp X86CallWrapper.savedRegisters
    · exact call.saved_registers_restored after savedRestored rbpRestored register kept
    · apply allFrame.registers register
      intro member
      rcases Finset.mem_union.mp (cover member) with caller | saved
      · exact outside caller
      · exact kept saved

/-- A complete call under one handler table that dispatches the exit block: the entry, a body of
`count` fetches ending at the exit block, and the exit. -/
theorem executes (handlers : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (output : BitVec 32) (written : Finset Nat) (body : State) (count : Nat)
    (entered : (@X86FuelPrefix.fetches handlers vector 8).run state = .ok () (call.entered output))
    (bodyRun : (@X86FuelPrefix.fetches handlers vector count).run (call.entered output) = .ok () body)
    (exit : Exit call output written body) (exitLinked : exitDispatch handlers = handlers) :
    ∃ after, (@X86FuelPrefix.fetches handlers vector (8 + count + 10)).run state = .ok () after ∧
      Result call written exit.remaining body after := by
  have returned := call.returns handlers vector exit
  rw [exitLinked] at returned
  obtain ⟨after, last, result⟩ := returned
  exact ⟨after, @X86FuelPrefix.fetches_then handlers vector (8 + count) 10 state body after
    (@X86FuelPrefix.fetches_then handlers vector 8 count state _ body entered bodyRun) last, result⟩

end Inputs

end Mettapedia.Machines.TIsa.X86AllowanceCall
