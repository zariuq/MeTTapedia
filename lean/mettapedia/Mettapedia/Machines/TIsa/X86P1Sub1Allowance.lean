import Mettapedia.Machines.TIsa.P1JsonImport
import Mettapedia.Machines.TIsa.X86CodePlacement
import Mettapedia.Machines.TIsa.X86Prologue
import Mettapedia.Tools.KernelReflexivity

/-!
# The allowance register in the captured `sub1` image

The wrapper saves and restores RBP at the checked offsets of the exported
image. The fetched instructions use the existing Sail stack handlers, with
the opcode bytes supplied by code placement and the captured image.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option Elab.async false

namespace Mettapedia.Machines.TIsa.X86P1Sub1Allowance

open _root_.X86Registers P1Capture X86Execution X86RegisterRefinement
local instance : MemoryPrimitives := X86Memory.ordinary

noncomputable def captured : AllowanceBundle :=
  tisa_p1_allowance_bundle% "../../../tcalc/tisa/manifests/tisa_x86_p1_programs_v2.json"

theorem exported_count : captured.bundle.programs.length = 15 := by kernel_reflexivity

noncomputable def sub1 : Program := captured.bundle.programs[11]'(by rw [exported_count]; decide)

theorem exported_identity : sub1.name = "mm_sub1_leaf" ∧ sub1.id = 11 ∧ sub1.size = 1596 := by
  constructor
  · kernel_reflexivity
  · constructor <;> kernel_reflexivity

theorem exported_boundary : captured.bundle.boundary.checkAllowance captured.allowanceRegister = true := by
  kernel_reflexivity

theorem exported_image : sub1.allowanceImageCheck = true := by kernel_reflexivity

theorem exported_source_checks : captured.bundle.programs.all Program.sourceCheck = true := by
  kernel_reflexivity

theorem exported_image_checks : captured.bundle.programs.all Program.allowanceImageCheck = true := by
  kernel_reflexivity

def saveOffset : Nat := NativeImage.prologue.length

noncomputable def restoreOffset : Nat := sub1.size - allowanceEpilogue.length

theorem save_offset : saveOffset = 9 := by decide

theorem restore_offset : restoreOffset = 1585 := by kernel_reflexivity

theorem save_byte : sub1.view.read saveOffset = some 0x55 := by kernel_reflexivity

theorem restore_byte : sub1.view.read restoreOffset = some 0x5d := by kernel_reflexivity

theorem leading_save_bytes : NativeImage.readRange? sub1.view 0 X86Prologue.expected.length =
    some (X86Prologue.expected.map (BitVec.ofNat 8)) := by kernel_reflexivity

theorem trailing_restore_bytes :
    NativeImage.readRange? sub1.view (restoreOffset + 1) X86Epilogue.expected.length =
      some (X86Epilogue.expected.map (BitVec.ofNat 8)) := by kernel_reflexivity

theorem code_int (base : BitVec 48) (upper : base.toInt + sub1.size < (2 ^ 47 : Int))
    (offset : Nat) (within : offset ≤ sub1.size) :
    (address base.toInt offset).toInt = base.toInt + offset :=
  address_toInt (extent := sub1.size) base.toInt (by simpa using BitVec.le_toInt base) upper offset within

theorem saves_rbp (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (context : X86PlainFetch.Facts state) (base stack bottom : BitVec 48) (value : Word)
    (visible : Vector (BitVec 16) 6) (controls : Vector (BitVec 64) 17) (flags : BitVec 32)
    (codeUpper : base.toInt + sub1.size < (2 ^ 47 : Int))
    (placed : X86CodePlacement.Placed state base.toInt sub1.view)
    (stackStep : bottom.toInt + 8 = stack.toInt) (stackUpper : bottom.toInt + 8 ≤ (2 ^ 47 : Int))
    (rip : state.regs.get? .rip = some ((address base.toInt saveOffset).signExtend 64))
    (stackKnown : lookup state 4 = some (stack.signExtend 64)) (rbpKnown : lookup state 5 = some value)
    (controlsKnown : state.regs.get? .ctrs = some controls) (flagsKnown : state.regs.get? .rflags = some flags)
    (visibleKnown : state.regs.get? .seg_visibles = some visible) (quiet : state.regs.get? .log_register_writes = some false)
    (aligned : bottom &&& (7#48) = (0#48)) :
    letI : OtherOpcodeHandlers := X86Stack.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    (Functions.x86_fetch_decode_execute ()).run state =
      .ok () (X86Stack.pushResult state value bottom (address base.toInt (saveOffset + 1))) := by
  refine X86Stack.fetched_push other vector state 5 context
    (address base.toInt saveOffset) (address base.toInt saveOffset) (address base.toInt (saveOffset + 1))
    stack bottom value visible controls flags ?_ ?_ stackStep stackUpper rip stackKnown rbpKnown
    controlsKnown flagsKnown visibleKnown quiet aligned ?_ ?_
  · simp
  · rw [code_int base codeUpper, code_int base codeUpper]
    · simp [X86Stack.pushLength, Int.add_assoc]
    all_goals (rw [save_offset, exported_identity.2.2]; decide)
  · intro high
    exact high (by decide) |>.elim
  · exact placed saveOffset _ save_byte

theorem restores_rbp (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (context : X86PlainFetch.Facts state) (base bottom stack : BitVec 48) (saved : Word)
    (visible : Vector (BitVec 16) 6) (controls : Vector (BitVec 64) 17) (flags : BitVec 32)
    (codeUpper : base.toInt + sub1.size < (2 ^ 47 : Int))
    (placed : X86CodePlacement.Placed state base.toInt sub1.view)
    (stackStep : bottom.toInt + 8 = stack.toInt) (stackUpper : bottom.toInt + 8 ≤ (2 ^ 47 : Int))
    (rip : state.regs.get? .rip = some ((address base.toInt restoreOffset).signExtend 64))
    (stackKnown : lookup state 4 = some (bottom.signExtend 64))
    (controlsKnown : state.regs.get? .ctrs = some controls) (flagsKnown : state.regs.get? .rflags = some flags)
    (visibleKnown : state.regs.get? .seg_visibles = some visible) (quiet : state.regs.get? .log_register_writes = some false)
    (aligned : bottom &&& (7#48) = (0#48))
    (present : ∀ index < 8, state.mem.get? (X86WriteWords.physicalAddress bottom index) =
      some (saved.extractLsb' (8 * index) 8)) :
    letI : OtherOpcodeHandlers := X86Stack.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    (Functions.x86_fetch_decode_execute ()).run state =
      .ok () (X86Stack.popResult state 5 saved stack (address base.toInt (restoreOffset + 1))) := by
  refine X86Stack.fetched_pop other vector state 5 context
    (address base.toInt restoreOffset) (address base.toInt restoreOffset) (address base.toInt (restoreOffset + 1))
    bottom stack saved visible controls flags ?_ ?_ stackStep stackUpper rip stackKnown
    controlsKnown flagsKnown visibleKnown quiet aligned ?_ ?_ present
  · simp
  · rw [code_int base codeUpper, code_int base codeUpper]
    · simp [X86Stack.popLength, Int.add_assoc]
    all_goals (rw [restore_offset, exported_identity.2.2]; decide)
  · intro high
    exact high (by decide) |>.elim
  · exact placed restoreOffset _ restore_byte

theorem placed_leading_saves (state : State) (base : BitVec 48)
    (placed : X86CodePlacement.Placed state base.toInt sub1.view) :
    codeLoaded state base.toInt X86Prologue.expected := by
  simpa using X86CodePlacement.range_code state base.toInt sub1.view 0
    X86Prologue.expected placed leading_save_bytes

def afterSaves (state : State) (five : X86Prologue.Inputs state) (bottom : BitVec 48) (rbp : Word) : State :=
  X86Stack.pushResult (X86Prologue.finished state five) rbp bottom
    (address five.code.toInt (saveOffset + 1))

theorem six_saves (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers) (state : State)
    (five : X86Prologue.Inputs state) (bottom : BitVec 48) (rbp : Word)
    (codeUpper : five.code.toInt + sub1.size < (2 ^ 47 : Int))
    (placed : X86CodePlacement.Placed state five.code.toInt sub1.view)
    (codeOutside : ∀ index byte, sub1.view.read index = some byte →
      ((address five.code.toInt index).signExtend 52).toNat ∉ X86Prologue.writes five.bottom)
    (stackStep : bottom.toInt + 8 = five.bottom.toInt)
    (aligned : bottom &&& (7#48) = (0#48)) (rbpKnown : lookup state 5 = some rbp) :
    letI : OtherOpcodeHandlers := X86Stack.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    (X86FuelPrefix.fetches 6).run state = .ok () (afterSaves state five bottom rbp) := by
  let : OtherOpcodeHandlers := X86Stack.linkedHandlers other
  let : VectorOpcodeHandlers := vector
  let middle := X86Prologue.finished state five
  have frame := X86Prologue.finished_frame state five
  have rip : middle.regs.get? .rip = some ((address five.code.toInt saveOffset).signExtend 64) := by
    simpa [middle, X86Prologue.stage, X86Prologue.offset, X86Prologue.codeAt, save_offset] using
      X86Prologue.stage_rip state five (5 : Fin 6)
  have stackKnown : lookup middle 4 = some (five.bottom.signExtend 64) := by
    simpa [middle, X86Prologue.stage, X86Prologue.stackAt, address, BitVec.ofInt_toInt] using
      X86Prologue.stage_stack state five (5 : Fin 6)
  have fetch := saves_rbp other vector middle (X86Prologue.stageContext state five (5 : Fin 6))
    five.code five.bottom bottom rbp five.visible five.controls five.flags codeUpper
    (X86CodePlacement.Placed.preserved five.code.toInt sub1.view placed frame codeOutside)
    stackStep (by rw [stackStep]; have bound := five.stackUpper; omega) rip stackKnown
    ((frame.lookup 5 (by decide)).trans rbpKnown)
    ((frame.registers .ctrs (by decide)).trans five.controlsKnown)
    ((frame.registers .rflags (by decide)).trans five.flagsKnown)
    ((frame.registers .seg_visibles (by decide)).trans five.visibleKnown)
    ((frame.registers .log_register_writes (by decide)).trans five.quiet) aligned
  exact X86FuelPrefix.fetches_then 5 1 state middle (afterSaves state five bottom rbp)
    (X86Prologue.executes other vector state five) (X86FuelPrefix.fetches_one _ _ fetch)

theorem six_saves_frame (state : State) (five : X86Prologue.Inputs state) (bottom : BitVec 48) (rbp : Word) :
    X86StateFrame.Frame {.rsp, .rip}
      (X86Prologue.writes five.bottom ∪ X86WriteWords.written bottom (List.range 8))
      state (afterSaves state five bottom rbp) := by
  simpa only [afterSaves, Finset.union_self] using (X86Prologue.finished_frame state five).trans
    (X86Stack.push_frame _ rbp bottom (address five.code.toInt (saveOffset + 1)))

noncomputable def afterRbp (state : State) (base stack : BitVec 48) (rbp : Word) : State :=
  X86Stack.popResult state 5 rbp stack (address base.toInt (restoreOffset + 1))

structure RestoreInputs (state : State) where
  context : X86PlainFetch.Facts state
  base : BitVec 48
  bottom : BitVec 48
  stack : BitVec 48
  rbp : Word
  codeUpper : base.toInt + sub1.size < (2 ^ 47 : Int)
  placed : X86CodePlacement.Placed state base.toInt sub1.view
  stackStep : bottom.toInt + 8 = stack.toInt
  stackUpper : bottom.toInt + 8 ≤ (2 ^ 47 : Int)
  rip : state.regs.get? .rip = some ((address base.toInt restoreOffset).signExtend 64)
  stackKnown : lookup state 4 = some (bottom.signExtend 64)
  visible : Vector (BitVec 16) 6
  controls : Vector (BitVec 64) 17
  flags : BitVec 32
  controlsKnown : state.regs.get? .ctrs = some controls
  flagsKnown : state.regs.get? .rflags = some flags
  visibleKnown : state.regs.get? .seg_visibles = some visible
  quiet : state.regs.get? .log_register_writes = some false
  aligned : bottom &&& (7#48) = (0#48)
  present : ∀ index < 8, state.mem.get? (X86WriteWords.physicalAddress bottom index) =
    some (rbp.extractLsb' (8 * index) 8)
  remaining : X86Epilogue.FrameFacts (afterRbp state base stack rbp)
  remainingStack : remaining.stack = stack

noncomputable def lastRestores {state : State} (input : RestoreInputs state) :
    X86Epilogue.Inputs (afterRbp state input.base input.stack input.rbp) := by
  let code := address input.base.toInt (restoreOffset + 1)
  let middle := afterRbp state input.base input.stack input.rbp
  have location : code.toInt = input.base.toInt + (restoreOffset + 1 : Nat) :=
    code_int input.base input.codeUpper _ (by rw [restore_offset, exported_identity.2.2]; decide)
  have upper : code.toInt + 10 < (2 ^ 47 : Int) := by
    rw [location, restore_offset]
    have bound := input.codeUpper
    rw [exported_identity.2.2] at bound
    omega
  have frame := X86Stack.pop_frame state 5 input.rbp input.stack code
  have placed : X86CodePlacement.Placed middle input.base.toInt sub1.view :=
    X86CodePlacement.Placed.preserved _ _ input.placed (X86StateFrame.registerOnly frame) (by simp)
  exact { input.remaining with
    code := code
    codeUpper := upper
    loaded := X86CodePlacement.code_of_read_range middle input.base.toInt sub1.view _ code
      X86Epilogue.expected location placed trailing_restore_bytes
    rip := X86FuelPrefix.pointer_rip _ _
    context := { input.context with
      status := (frame.registers .ms_reg (by decide)).trans input.context.status
      fault := (frame.registers .fault_reg (by decide)).trans input.context.fault
      msrs := (frame.registers .msrs (by decide)).trans input.context.msrs
      segments := (frame.registers .seg_hidden_attrs (by decide)).trans input.context.segments
      application := (frame.registers .app_view (by decide)).trans input.context.application } }

noncomputable def afterRestores {state : State} (input : RestoreInputs state) : State :=
  X86Epilogue.finished (afterRbp state input.base input.stack input.rbp) (lastRestores input)

theorem six_restores (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers) (state : State)
    (input : RestoreInputs state) :
    letI : OtherOpcodeHandlers := X86Stack.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    (X86FuelPrefix.fetches 7).run state = .ok () (afterRestores input) := by
  let : OtherOpcodeHandlers := X86Stack.linkedHandlers other
  let : VectorOpcodeHandlers := vector
  let middle := afterRbp state input.base input.stack input.rbp
  have first := restores_rbp other vector state input.context input.base input.bottom input.stack input.rbp
    input.visible input.controls input.flags input.codeUpper input.placed input.stackStep input.stackUpper
    input.rip input.stackKnown input.controlsKnown input.flagsKnown input.visibleKnown input.quiet
    input.aligned input.present
  exact X86FuelPrefix.fetches_then 1 6 state middle (afterRestores input)
    (X86FuelPrefix.fetches_one _ _ first) (X86Epilogue.executes other vector middle (lastRestores input))

theorem restore_result {state : State} (input : RestoreInputs state) :
    lookup (afterRestores input) 5 = some input.rbp ∧
    (∀ index, lookup (afterRestores input) (X86Epilogue.target index) = some (input.remaining.saved index)) ∧
    (afterRestores input).regs.get? .rip = some (input.remaining.returnAddress.signExtend 64) ∧
    lookup (afterRestores input) 4 = some ((address input.bottom.toInt 56).signExtend 64) ∧
    (afterRestores input).mem = state.mem ∧
    lookup (afterRestores input) 0 = lookup state 0 ∧
    (afterRestores input).regs.get? .rflags = state.regs.get? .rflags := by
  let middle := afterRbp state input.base input.stack input.rbp
  have firstFrame := X86Stack.pop_frame state 5 input.rbp input.stack (address input.base.toInt (restoreOffset + 1))
  have last := X86Epilogue.finished_result middle (lastRestores input)
  refine ⟨?_, last.saved, last.pointer, ?_, last.frame.memory.trans firstFrame.memory,
    last.rax.trans (firstFrame.lookup 0 (by decide)),
    (last.frame.registers .rflags (by decide)).trans (firstFrame.registers .rflags (by decide))⟩
  · exact (last.frame.lookup 5 (by decide)).trans (X86Stack.pop_value _ _ _ _ _)
  · have stack : (lastRestores input).stack = input.stack := input.remainingStack
    have atEnd : X86Epilogue.stackAt (lastRestores input) 6 = address input.bottom.toInt 56 := by
      unfold X86Epilogue.stackAt address
      rw [stack]
      congr 1
      have step := input.stackStep
      simp only [Nat.cast_ofNat, Nat.reduceMul]
      omega
    simpa only [afterRestores, middle, atEnd] using last.stackPointer

namespace Controls

def patch (view : NativeImage.View) (offset : Nat) : NativeImage.View :=
  ⟨view.size, fun index => if index = offset then some 0x90 else view.read index⟩

theorem wrong_save_byte :
    sub1.allowanceImageCheckOn (patch sub1.view saveOffset) = false := by
  kernel_reflexivity

theorem wrong_restore_byte :
    sub1.allowanceImageCheckOn (patch sub1.view restoreOffset) = false := by
  kernel_reflexivity

theorem wrong_allowance_register : captured.bundle.boundary.checkAllowance "r15" = false := by
  kernel_reflexivity

theorem wrong_flag_template :
    (sub1.spans[3]?.map fun span =>
      { span with kind := "IF-FLAGS" }.allowanceSourceCheck sub1.source.body) = some false := by
  kernel_reflexivity

end Controls

end Mettapedia.Machines.TIsa.X86P1Sub1Allowance

#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Allowance.exported_boundary
#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Allowance.exported_image
#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Allowance.exported_source_checks
#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Allowance.exported_image_checks
#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Allowance.saves_rbp
#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Allowance.restores_rbp
#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Allowance.six_saves
#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Allowance.six_saves_frame
#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Allowance.six_restores
#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Allowance.restore_result
#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Allowance.Controls.wrong_save_byte
#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Allowance.Controls.wrong_restore_byte
#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Allowance.Controls.wrong_allowance_register
#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Allowance.Controls.wrong_flag_template
