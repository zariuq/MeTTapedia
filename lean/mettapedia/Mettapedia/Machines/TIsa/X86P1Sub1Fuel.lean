import Mettapedia.Machines.TIsa.X86Funding
import Mettapedia.Machines.TIsa.X86P1Sub1Allowance
import Mettapedia.Machines.TIsa.X86FrameStore
import Mettapedia.Machines.TIsa.X86ControlFlags

/-!
# Allowance and receipt in the committed `sub1` image

The two instructions after the six saves read the budget and receipt words
and install their difference in RBP. Both fetches use the captured bytes
and the pinned Sail decoder. On exit, three instructions recover the
cumulative receipt from the budget and the remaining allowance.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option Elab.async false

namespace Mettapedia.Machines.TIsa.X86P1Sub1Fuel

open _root_.X86Registers X86Execution X86RegisterRefinement X86P1Sub1Allowance
local instance : MemoryPrimitives := X86Memory.ordinary

abbrev handlers (other : OtherOpcodeHandlers) : OtherOpcodeHandlers :=
  X86Funding.GenericMemory.linkedHandlers (X86FrameLoad.linkedHandlers other)

def basis {state : State} (base : BitVec 48) (offset : Nat)
    (upper : base.toInt + sub1.size < (2 ^ 47 : Int)) (inside : offset + 3 ≤ sub1.size)
    (mode : X86PlainFetch.Facts state)
    (rip : state.regs.get? .rip = some ((address base.toInt offset).signExtend 64)) :
    X86LegacyFetch.Basis state where
  address := address base.toInt offset
  opcodeAddress := address base.toInt (offset + 1)
  modrmAddress := address base.toInt (offset + 2)
  next := address base.toInt (offset + 3)
  control := mode.control
  attributes := mode.attributes
  step1 := by rw [code_int base upper _ (by omega), code_int base upper _ (by omega)]; omega
  step2 := by rw [code_int base upper _ (by omega), code_int base upper _ (by omega)]; omega
  step3 := by rw [code_int base upper _ (by omega), code_int base upper _ inside]; omega
  status := mode.status
  fault := mode.fault
  msrs := mode.msrs
  segments := mode.segments
  longMode := mode.longMode
  codeMode := mode.codeMode
  application := mode.application
  rip := rip

structure SetupFacts (state : State) where
  frame : Word
  frameKnown : lookup state 7 = some frame
  budgetAddress : BitVec 48
  budgetUpper : budgetAddress.toInt + 8 ≤ (2 ^ 47 : Int)
  budgetEffective : frame + (160#64) = budgetAddress.signExtend 64
  budgetAligned : budgetAddress &&& (7#48) = (0#48)
  budget : Word
  budgetPresent : ∀ index < 8,
    state.mem.get? ((address budgetAddress.toInt index).signExtend 52).toNat =
      some (budget.extractLsb' (8 * index) 8)
  receiptAddress : BitVec 48
  receiptUpper : receiptAddress.toInt + 8 ≤ (2 ^ 47 : Int)
  receiptEffective : frame + (168#64) = receiptAddress.signExtend 64
  receiptAligned : receiptAddress &&& (7#48) = (0#48)
  receipt : Word
  receiptPresent : ∀ index < 8,
    state.mem.get? ((address receiptAddress.toInt index).signExtend 52).toNat =
      some (receipt.extractLsb' (8 * index) 8)
  visible : Vector (BitVec 16) 6
  controls : Vector (BitVec 64) 17
  flags : BitVec 32
  visibleKnown : state.regs.get? .seg_visibles = some visible
  controlsKnown : state.regs.get? .ctrs = some controls
  flagsKnown : state.regs.get? .rflags = some flags
  quiet : state.regs.get? .log_register_writes = some false

structure Inputs (state : State) extends SetupFacts state where
  mode : X86PlainFetch.Facts state
  base : BitVec 48
  codeUpper : base.toInt + sub1.size < (2 ^ 47 : Int)
  placed : X86CodePlacement.Placed state base.toInt sub1.view
  rip : state.regs.get? .rip = some ((address base.toInt 10).signExtend 64)

def afterBudget {state : State} (input : Inputs state) : State :=
  X86Move.putPointer (put state 5 input.budget) (address input.base.toInt 17)

def afterAllowance {state : State} (input : Inputs state) (output : BitVec 32) : State :=
  X86Move.putPointer
    (X86Flags.putFlags (put (afterBudget input) 5 (input.budget - input.receipt))
      (X86Flags.mergeFlags input.flags output)) (address input.base.toInt 24)

theorem budget_frame {state : State} (input : Inputs state) :
    X86StateFrame.Frame {.rbp, .rip} ∅ state (afterBudget input) := by
  apply X86StateFrame.registerOnly
  simpa [key, afterBudget] using (X86Execution.put_frame state 5 input.budget).trans
    (X86Execution.pointer_frame _ (address input.base.toInt 17))

theorem allowance_frame {state : State} (input : Inputs state) (output : BitVec 32) :
    X86StateFrame.Frame {.rbp, .rflags, .rip} ∅ state (afterAllowance input output) := by
  have composed := (budget_frame input).trans (X86Funding.GenericMemory.subtract_to_frame 5
    (afterBudget input) (input.budget - input.receipt) (X86Flags.mergeFlags input.flags output)
    (address input.base.toInt 24))
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

private theorem budget_disp (index : Fin 4) :
    sub1.view.read (13 + index.val) = some ((160#32).extractLsb' (8 * index.val) 8) := by
  fin_cases index <;> kernel_reflexivity

private theorem receipt_disp (index : Fin 4) :
    sub1.view.read (20 + index.val) = some ((168#32).extractLsb' (8 * index.val) 8) := by
  fin_cases index <;> kernel_reflexivity

theorem loads_budget (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (input : Inputs state) :
    letI : OtherOpcodeHandlers := handlers other
    letI : VectorOpcodeHandlers := vector
    (Functions.x86_fetch_decode_execute ()).run state = .ok () (afterBudget input) := by
  have length : (13 : Nat) ≤ sub1.size := by rw [exported_identity.2.2]; decide
  let origin := basis input.base 10 input.codeUpper length input.mode input.rip
  have offset13 := code_int input.base input.codeUpper 13 length
  have offset17 := code_int input.base input.codeUpper 17 (by rw [exported_identity.2.2]; decide)
  refine X86FrameLoad.fetched_frame (X86Funding.GenericMemory.linkedHandlers other) vector state 5
    origin (address input.base.toInt 17) input.budgetAddress input.visible input.controls
    input.frame input.budget input.flags (160#32) ?_ input.budgetUpper input.frameKnown
    input.controlsKnown input.flagsKnown input.visibleKnown input.quiet input.budgetEffective input.budgetAligned
    ?_ ?_ ?_ ?_ input.budgetPresent
  · change (address input.base.toInt 13).toInt + 4 = (address input.base.toInt 17).toInt
    omega
  · exact input.placed 10 _ (by kernel_reflexivity)
  · exact input.placed 11 _ (by kernel_reflexivity)
  · exact input.placed 12 _ (by kernel_reflexivity)
  · intro index inside
    have byte := input.placed (13 + index) _ (budget_disp ⟨index, inside⟩)
    change state.mem.get? ((address (address input.base.toInt 13).toInt index).signExtend 52).toNat = _
    rw [offset13]
    simpa only [address, Int.natCast_add, Int.add_assoc] using byte

theorem subtracts_receipt (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (input : Inputs state) :
    letI : OtherOpcodeHandlers := handlers other
    letI : VectorOpcodeHandlers := vector
    ∃ output, (Functions.x86_fetch_decode_execute ()).run (afterBudget input) =
      .ok () (afterAllowance input output) := by
  let middle := afterBudget input
  have frame := budget_frame input
  let mode : X86PlainFetch.Facts middle := { input.mode with
    status := (frame.registers .ms_reg (by decide)).trans input.mode.status
    fault := (frame.registers .fault_reg (by decide)).trans input.mode.fault
    msrs := (frame.registers .msrs (by decide)).trans input.mode.msrs
    segments := (frame.registers .seg_hidden_attrs (by decide)).trans input.mode.segments
    application := (frame.registers .app_view (by decide)).trans input.mode.application }
  have length : (20 : Nat) ≤ sub1.size := by rw [exported_identity.2.2]; decide
  let origin := basis input.base 17 input.codeUpper length mode (X86FuelPrefix.pointer_rip _ _)
  have offset20 := code_int input.base input.codeUpper 20 length
  have offset24 := code_int input.base input.codeUpper 24 (by rw [exported_identity.2.2]; decide)
  have placed : X86CodePlacement.Placed middle input.base.toInt sub1.view :=
    X86CodePlacement.Placed.preserved _ _ input.placed frame (by simp)
  have known : lookup middle 5 = some input.budget := by
    simp only [middle, afterBudget, X86Move.lookup_putPointer, lookup_put_same]
  refine X86Funding.GenericMemory.fetched_subtract_to 5 (X86FrameLoad.linkedHandlers other) vector
    middle origin (address input.base.toInt 24) input.receiptAddress input.visible input.controls
    input.frame input.budget input.receipt input.flags (168#32) ?_ input.receiptUpper
    ((frame.lookup 7 (by decide)).trans input.frameKnown) known
    ((frame.registers .ctrs (by decide)).trans input.controlsKnown)
    ((frame.registers .rflags (by decide)).trans input.flagsKnown)
    ((frame.registers .seg_visibles (by decide)).trans input.visibleKnown)
    ((frame.registers .log_register_writes (by decide)).trans input.quiet)
    input.receiptEffective input.receiptAligned ?_ ?_ ?_ ?_ ?_
  · change (address input.base.toInt 20).toInt + 4 = (address input.base.toInt 24).toInt
    omega
  · exact placed 17 _ (by kernel_reflexivity)
  · exact placed 18 _ (by kernel_reflexivity)
  · exact placed 19 _ (by kernel_reflexivity)
  · intro index inside
    have byte := placed (20 + index) _ (receipt_disp ⟨index, inside⟩)
    change middle.mem.get? ((address (address input.base.toInt 20).toInt index).signExtend 52).toNat = _
    rw [offset20]
    simpa only [address, Int.natCast_add, Int.add_assoc] using byte
  · intro index inside
    rw [frame.memory _ (by simp)]
    exact input.receiptPresent index inside

theorem initializes (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (input : Inputs state) :
    letI : OtherOpcodeHandlers := handlers other
    letI : VectorOpcodeHandlers := vector
    ∃ output, (X86FuelPrefix.fetches 2).run state = .ok () (afterAllowance input output) := by
  let : OtherOpcodeHandlers := handlers other
  let : VectorOpcodeHandlers := vector
  obtain ⟨output, second⟩ := subtracts_receipt other vector state input
  exact ⟨output, X86FuelPrefix.fetches_then 1 1 state (afterBudget input) _
    (X86FuelPrefix.fetches_one _ _ (loads_budget other vector state input))
    (X86FuelPrefix.fetches_one _ _ second)⟩

theorem initialized_allowance {state : State} (input : Inputs state) (output : BitVec 32) :
    lookup (afterAllowance input output) 5 = some (input.budget - input.receipt) := by
  rw [afterAllowance, X86Move.lookup_putPointer,
    (X86Execution.flags_frame _ _).lookup 5 (by decide), lookup_put_same]

theorem initialized_charge {state : State} (input : Inputs state) (output : BitVec 32)
    (grade : Funding.Grade) (valid : input.receipt.toNat ≤ input.budget.toNat) :
    lookup (afterAllowance input output) 5 = some (input.budget - input.receipt) ∧
      (Funding.available input.budget input.receipt grade = true ↔
        grade.word.toNat ≤ (input.budget - input.receipt).toNat) :=
  ⟨initialized_allowance input output, Funding.available_sub_iff input.budget input.receipt grade valid⟩

abbrev entryHandlers (other : OtherOpcodeHandlers) : OtherOpcodeHandlers :=
  X86Stack.linkedHandlers (handlers other)

theorem enters_body (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers) (state : State)
    (five : X86Prologue.Inputs state) (bottom : BitVec 48) (rbp : Word)
    (upper : five.code.toInt + sub1.size < (2 ^ 47 : Int))
    (placed : X86CodePlacement.Placed state five.code.toInt sub1.view)
    (outside : ∀ index byte, sub1.view.read index = some byte →
      ((address five.code.toInt index).signExtend 52).toNat ∉ X86Prologue.writes five.bottom)
    (stackStep : bottom.toInt + 8 = five.bottom.toInt)
    (aligned : bottom &&& (7#48) = (0#48)) (saved : lookup state 5 = some rbp)
    (input : Inputs (afterSaves state five bottom rbp)) (base : input.base = five.code) :
    letI : OtherOpcodeHandlers := entryHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ output,
      (X86FuelPrefix.fetches 8).run state = .ok () (afterAllowance input output) ∧
      (afterAllowance input output).regs.get? .rip = some ((address five.code.toInt 24).signExtend 64) ∧
      lookup (afterAllowance input output) 5 = some (input.budget - input.receipt) ∧
      X86StateFrame.Frame {.rsp, .rip, .rbp, .rflags}
        (X86Prologue.writes five.bottom ∪ X86WriteWords.written bottom (List.range 8))
        state (afterAllowance input output) := by
  let : OtherOpcodeHandlers := entryHandlers other
  let : VectorOpcodeHandlers := vector
  have saves := six_saves (handlers other) vector state five bottom rbp upper placed outside stackStep aligned saved
  obtain ⟨output, setup⟩ := initializes (X86Stack.linkedHandlers other) vector (afterSaves state five bottom rbp) input
  refine ⟨output, X86FuelPrefix.fetches_then 6 2 state (afterSaves state five bottom rbp) _ saves setup,
    ?_, initialized_allowance input output, ?_⟩
  · simp only [afterAllowance, X86FuelPrefix.pointer_rip, base]
  · apply ((six_saves_frame state five bottom rbp).trans (allowance_frame input output)).mono
    · intro register member
      simp at member ⊢
      tauto
    · simp

namespace Receipt

abbrev handlers (other : OtherOpcodeHandlers) : OtherOpcodeHandlers :=
  X86FrameLoad.linkedHandlers (X86Arithmetic.linkedHandlers other)

structure Facts (state : State) where
  frame : Word
  frameKnown : lookup state 7 = some frame
  budgetAddress : BitVec 48
  budgetUpper : budgetAddress.toInt + 8 ≤ (2 ^ 47 : Int)
  budgetEffective : frame + (160#64) = budgetAddress.signExtend 64
  budgetAligned : budgetAddress &&& (7#48) = (0#48)
  budget : Word
  budgetPresent : ∀ index < 8,
    state.mem.get? (X86WriteWords.physicalAddress budgetAddress index) =
      some (budget.extractLsb' (8 * index) 8)
  receiptAddress : BitVec 48
  receiptUpper : receiptAddress.toInt + 8 ≤ (2 ^ 47 : Int)
  receiptEffective : frame + (168#64) = receiptAddress.signExtend 64
  receiptAligned : receiptAddress &&& (7#48) = (0#48)
  remaining : Word
  remainingKnown : lookup state 5 = some remaining
  visible : Vector (BitVec 16) 6
  controls : Vector (BitVec 64) 17
  flags : BitVec 32
  visibleKnown : state.regs.get? .seg_visibles = some visible
  controlsKnown : state.regs.get? .ctrs = some controls
  flagsKnown : state.regs.get? .rflags = some flags
  quiet : state.regs.get? .log_register_writes = some false

structure Inputs (state : State) extends Facts state where
  mode : X86PlainFetch.Facts state
  base : BitVec 48
  codeUpper : base.toInt + sub1.size < (2 ^ 47 : Int)
  placed : X86CodePlacement.Placed state base.toInt sub1.view
  rip : state.regs.get? .rip = some ((address base.toInt 1568).signExtend 64)

def Facts.transport {before after : State} {regWrites : Finset Register} {byteWrites : Finset Nat}
    (input : Facts before) (framed : X86StateFrame.Frame regWrites byteWrites before after)
    (dataOnly : regWrites ⊆ dataRegisters) (frameFixed : key 7 ∉ regWrites) (allowanceFixed : key 5 ∉ regWrites)
    (budgetFixed : ∀ index < 8, X86WriteWords.physicalAddress input.budgetAddress index ∉ byteWrites)
    (flags : BitVec 32) (flagsKnown : after.regs.get? .rflags = some flags) : Facts after :=
  let preserves (reg : Register) (apart : reg ∉ dataRegisters) :=
    framed.registers reg (fun written => apart (dataOnly written))
  { input with
    frameKnown := (framed.lookup 7 frameFixed).trans input.frameKnown
    remainingKnown := (framed.lookup 5 allowanceFixed).trans input.remainingKnown
    budgetPresent := fun i inside => (framed.memory _ (budgetFixed i inside)).trans (input.budgetPresent i inside)
    controlsKnown := (preserves .ctrs (by decide)).trans input.controlsKnown
    visibleKnown := (preserves .seg_visibles (by decide)).trans input.visibleKnown
    flags := flags
    flagsKnown := flagsKnown
    quiet := (preserves .log_register_writes (by decide)).trans input.quiet }

private theorem inside (offset : Nat) (bound : offset ≤ 1585) : offset ≤ sub1.size := by
  rw [exported_identity.2.2]
  omega

def afterBudget {state : State} (input : Inputs state) : State :=
  X86Move.putPointer (put state 14 input.budget) (address input.base.toInt 1575)

def afterDifference {state : State} (input : Inputs state) (output : BitVec 32) : State :=
  X86Move.putPointer
    (X86Flags.putFlags (put (afterBudget input) 14 (input.budget - input.remaining))
      (X86Flags.mergeFlags input.flags output)) (address input.base.toInt 1578)

noncomputable def afterWrite {state : State} (input : Inputs state) (output : BitVec 32) : State :=
  X86Move.putPointer (X86WriteWords.storeBytes 8 (afterDifference input output)
    input.receiptAddress (input.budget - input.remaining)) (address input.base.toInt restoreOffset)

private theorem budget_frame {state : State} (input : Inputs state) :
    X86StateFrame.Frame {.r14, .rip} ∅ state (afterBudget input) := by
  apply X86StateFrame.registerOnly
  have step := (X86Execution.put_frame state 14 input.budget).trans
    (X86Execution.pointer_frame _ (address input.base.toInt 1575))
  apply step.mono
  simp [key]

private theorem difference_frame {state : State} (input : Inputs state) (output : BitVec 32) :
    X86StateFrame.Frame {.r14, .rflags, .rip} ∅ state (afterDifference input output) := by
  have step := X86Funding.GenericMemory.subtract_to_frame 14 (afterBudget input)
    (input.budget - input.remaining) (X86Flags.mergeFlags input.flags output) (address input.base.toInt 1578)
  apply ((budget_frame input).trans step).mono
  · intro register member
    simp [key] at member ⊢
    tauto
  · simp

private def nextMode {state current : State} (mode : X86PlainFetch.Facts state)
    (frame : X86StateFrame.Frame {.r14, .rflags, .rip} ∅ state current) :
    X86PlainFetch.Facts current := { mode with
  status := (frame.registers .ms_reg (by decide)).trans mode.status
  fault := (frame.registers .fault_reg (by decide)).trans mode.fault
  msrs := (frame.registers .msrs (by decide)).trans mode.msrs
  segments := (frame.registers .seg_hidden_attrs (by decide)).trans mode.segments
  application := (frame.registers .app_view (by decide)).trans mode.application }

private theorem budget_disp (index : Fin 4) :
    sub1.view.read (1571 + index.val) = some ((160#32).extractLsb' (8 * index.val) 8) := by
  fin_cases index <;> kernel_reflexivity

private theorem receipt_disp (index : Fin 4) :
    sub1.view.read (1581 + index.val) = some ((168#32).extractLsb' (8 * index.val) 8) := by
  fin_cases index <;> kernel_reflexivity

theorem loads_budget (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (input : Inputs state) :
    letI : OtherOpcodeHandlers := handlers other
    letI : VectorOpcodeHandlers := vector
    (Functions.x86_fetch_decode_execute ()).run state = .ok () (afterBudget input) := by
  let origin := basis input.base 1568 input.codeUpper (inside 1571 (by decide)) input.mode input.rip
  have atDisp := code_int input.base input.codeUpper 1571 (inside 1571 (by decide))
  have atNext := code_int input.base input.codeUpper 1575 (inside 1575 (by decide))
  refine X86FrameLoad.fetched_frame (X86Arithmetic.linkedHandlers other) vector state 14
    origin (address input.base.toInt 1575) input.budgetAddress input.visible input.controls
    input.frame input.budget input.flags (160#32) ?_ input.budgetUpper input.frameKnown
    input.controlsKnown input.flagsKnown input.visibleKnown input.quiet input.budgetEffective input.budgetAligned
    ?_ ?_ ?_ ?_ input.budgetPresent
  · change (address input.base.toInt 1571).toInt + 4 = (address input.base.toInt 1575).toInt
    omega
  · exact input.placed 1568 _ (by kernel_reflexivity)
  · exact input.placed 1569 _ (by kernel_reflexivity)
  · exact input.placed 1570 _ (by kernel_reflexivity)
  · intro index within
    have byte := input.placed (1571 + index) _ (budget_disp ⟨index, within⟩)
    change state.mem.get? ((address (address input.base.toInt 1571).toInt index).signExtend 52).toNat = _
    rw [atDisp]
    simpa only [address, Int.natCast_add, Int.add_assoc] using byte

theorem subtracts_remaining (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (input : Inputs state) :
    letI : OtherOpcodeHandlers := handlers other
    letI : VectorOpcodeHandlers := vector
    ∃ output, (Functions.x86_fetch_decode_execute ()).run (afterBudget input) =
      .ok () (afterDifference input output) := by
  let current := afterBudget input
  have frame := budget_frame input
  let origin := basis input.base 1575 input.codeUpper (inside 1578 (by decide))
    (nextMode input.mode (frame.mono (by simp) (by simp))) (X86FuelPrefix.pointer_rip _ _)
  have placed := X86CodePlacement.Placed.preserved _ _ input.placed frame (by simp)
  let window : X86LegacyFetch.Window current (X86Arithmetic.opcode .sub) true 5 14 := {
    toBasis := origin
    prefixByte := placed 1575 _ (by kernel_reflexivity)
    opcodeByte := placed 1576 _ (by kernel_reflexivity)
    modrmByte := placed 1577 _ (by kernel_reflexivity) }
  have budget : lookup current 14 = some input.budget := by
    simp only [current, afterBudget, X86Move.lookup_putPointer, lookup_put_same]
  exact X86Arithmetic.fetched_register64 (X86FrameLoad.linkedHandlers other) vector .sub current 5 14
    window input.budget input.remaining input.flags ((frame.lookup 5 (by decide)).trans input.remainingKnown)
    budget ((frame.registers .rflags (by decide)).trans input.flagsKnown)
    ((frame.registers .log_register_writes (by decide)).trans input.quiet)

theorem stores_receipt (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (input : Inputs state) (output : BitVec 32) :
    letI : OtherOpcodeHandlers := handlers other
    letI : VectorOpcodeHandlers := vector
    (Functions.x86_fetch_decode_execute ()).run (afterDifference input output) = .ok () (afterWrite input output) := by
  let current := afterDifference input output
  have frame := difference_frame input output
  let origin := basis input.base 1578 input.codeUpper (inside 1581 (by decide))
    (nextMode input.mode frame) (X86FuelPrefix.pointer_rip _ _)
  have placed := X86CodePlacement.Placed.preserved _ _ input.placed frame (by simp)
  have value : lookup current 14 = some (input.budget - input.remaining) := by
    rw [show current = afterDifference input output from rfl, afterDifference, X86Move.lookup_putPointer,
      (X86Execution.flags_frame _ _).lookup 14 (by decide), lookup_put_same]
  have flags : current.regs.get? .rflags = some (X86Flags.mergeFlags input.flags output) := by
    rw [show current = afterDifference input output from rfl, afterDifference,
      (X86Execution.pointer_frame _ _).registers _ (by decide)]
    simp [X86Flags.putFlags]
  have atDisp := code_int input.base input.codeUpper 1581 (inside 1581 (by decide))
  have atNext := code_int input.base input.codeUpper 1585 (inside 1585 (by decide))
  rw [afterWrite, restore_offset]
  refine X86FrameStore.fetched_register (handlers other) vector current 14 origin
    (address input.base.toInt 1585) input.receiptAddress input.visible input.controls input.frame
    (input.budget - input.remaining) (X86Flags.mergeFlags input.flags output) (168#32) ?_ input.receiptUpper
    ((frame.lookup 7 (by decide)).trans input.frameKnown) value
    ((frame.registers .ctrs (by decide)).trans input.controlsKnown) flags
    ((frame.registers .seg_visibles (by decide)).trans input.visibleKnown)
    ((frame.registers .log_register_writes (by decide)).trans input.quiet)
    input.receiptEffective input.receiptAligned ?_ ?_ ?_ ?_
  · change (address input.base.toInt 1581).toInt + 4 = (address input.base.toInt 1585).toInt
    omega
  · exact placed 1578 _ (by kernel_reflexivity)
  · exact placed 1579 _ (by kernel_reflexivity)
  · exact placed 1580 _ (by kernel_reflexivity)
  · intro index within
    have byte := placed (1581 + index) _ (receipt_disp ⟨index, within⟩)
    change current.mem.get? ((address (address input.base.toInt 1581).toInt index).signExtend 52).toNat = _
    rw [atDisp]
    simpa only [address, Int.natCast_add, Int.add_assoc] using byte

theorem write_frame {state : State} (input : Inputs state) (output : BitVec 32) :
    X86StateFrame.Frame {.r14, .rflags, .rip} (X86WriteWords.written input.receiptAddress (List.range 8))
      state (afterWrite input output) := by
  let stored := X86WriteWords.storeBytes 8 (afterDifference input output) input.receiptAddress
    (input.budget - input.remaining)
  have write := X86WriteWords.storeBytes_frame 8 (afterDifference input output) input.receiptAddress
    (input.budget - input.remaining)
  have advance := X86StateFrame.registerOnly (X86Execution.pointer_frame stored (address input.base.toInt restoreOffset))
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
    letI : OtherOpcodeHandlers := handlers other
    letI : VectorOpcodeHandlers := vector
    ∃ output, (X86FuelPrefix.fetches 3).run state = .ok () (afterWrite input output) ∧
      (afterWrite input output).regs.get? .rip = some ((address input.base.toInt restoreOffset).signExtend 64) ∧
      X86StateFrame.Frame {.r14, .rflags, .rip} (X86WriteWords.written input.receiptAddress (List.range 8))
        state (afterWrite input output) ∧
      ∀ index < 8, (afterWrite input output).mem.get? (X86WriteWords.physicalAddress input.receiptAddress index) =
        some ((input.budget - input.remaining).extractLsb' (8 * index) 8) := by
  let : OtherOpcodeHandlers := handlers other
  let : VectorOpcodeHandlers := vector
  obtain ⟨output, subtract⟩ := subtracts_remaining other vector state input
  have load := X86FuelPrefix.fetches_one _ _ (loads_budget other vector state input)
  have sub := X86FuelPrefix.fetches_one _ _ subtract
  have store := X86FuelPrefix.fetches_one _ _ (stores_receipt other vector state input output)
  exact ⟨output, X86FuelPrefix.fetches_then 2 1 state (afterDifference input output) _
    (X86FuelPrefix.fetches_then 1 1 state (afterBudget input) _ load sub) store,
    X86FuelPrefix.pointer_rip _ _, write_frame input output, written_byte input output⟩

theorem receipt_value {state : State} (input : Inputs state) (spent : Word)
    (balance : input.remaining.toNat + spent.toNat = input.budget.toNat) :
    input.budget - input.remaining = spent := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; omega)]
  omega

end Receipt

namespace Controls

def setupBytes : List NativeImage.Byte :=
  [0x48, 0x8b, 0xaf, 0xa0, 0, 0, 0, 0x48, 0x2b, 0xaf, 0xa8, 0, 0, 0]

theorem setup_exact : NativeImage.readRange? sub1.view 10 14 = some setupBytes := by
  kernel_reflexivity

theorem changed_budget_offset :
    (NativeImage.readRange? (X86P1Sub1Allowance.Controls.patch sub1.view 13) 10 14 == some setupBytes) = false := by
  kernel_reflexivity

theorem changed_receipt_offset :
    (NativeImage.readRange? (X86P1Sub1Allowance.Controls.patch sub1.view 20) 10 14 == some setupBytes) = false := by
  kernel_reflexivity

def writebackBytes : List NativeImage.Byte :=
  [0x4c, 0x8b, 0xb7, 0xa0, 0, 0, 0, 0x49, 0x29, 0xee, 0x4c, 0x89, 0xb7, 0xa8, 0, 0, 0]

theorem writeback_exact : NativeImage.readRange? sub1.view 1568 17 = some writebackBytes := by
  kernel_reflexivity

theorem changed_receipt_store_offset :
    (NativeImage.readRange? (X86P1Sub1Allowance.Controls.patch sub1.view 1581) 1568 17 ==
      some writebackBytes) = false := by
  kernel_reflexivity

end Controls

end Mettapedia.Machines.TIsa.X86P1Sub1Fuel

#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Fuel.loads_budget
#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Fuel.subtracts_receipt
#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Fuel.initializes
#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Fuel.allowance_frame
#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Fuel.initialized_charge
#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Fuel.enters_body
#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Fuel.Controls.setup_exact
#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Fuel.Controls.changed_budget_offset
#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Fuel.Controls.changed_receipt_offset
#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Fuel.Receipt.loads_budget
#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Fuel.Receipt.subtracts_remaining
#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Fuel.Receipt.stores_receipt
#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Fuel.Receipt.write_frame
#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Fuel.Receipt.written_byte
#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Fuel.Receipt.publishes
#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Fuel.Receipt.receipt_value
#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Fuel.Controls.writeback_exact
#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Fuel.Controls.changed_receipt_store_offset
