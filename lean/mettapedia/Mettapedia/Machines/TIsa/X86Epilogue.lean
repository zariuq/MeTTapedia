import Mettapedia.Machines.TIsa.X86Stack
import Mettapedia.Machines.TIsa.X86FuelPrefix
import Mettapedia.Machines.TIsa.X86CodePlacement

/-!
# The complete public epilogue in the pinned x86 model

Six full fetched instructions execute the ten actual bytes: POP r15, r14,
r13, r12 and rbx, followed by C3 RET. Explicit stack words supply the saved
register values and canonical caller address. The final contract restores
those five values, advances RSP by forty-eight bytes, preserves RAX/flags and
all memory, and returns to the caller. No handler execution is assumed.

Concrete controls restore high-bit values and refuse a result leaving r12
unrestored. These are epilogue contracts. The prologue must separately prove
that its saved words represent caller registers; complete source/compiler and
physical memory-installation correspondence remain open.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Mettapedia.Machines.TIsa.X86Epilogue
open _root_.X86Registers X86RegisterRefinement X86Execution
local instance : MemoryPrimitives := X86Memory.ordinary

def expected : List Nat := [0x41, 0x5f, 0x41, 0x5e, 0x41, 0x5d, 0x41, 0x5c, 0x5b, 0xc3]
def target (index : Fin 5) : Fin 16 := #[15, 14, 13, 12, 3][index.val]'(by exact index.isLt)
def offset (index : Fin 6) : Nat := if index.val < 5 then 2 * index.val else 9

structure FrameFacts (state : State) where
  stack : BitVec 48
  stackUpper : stack.toInt + 48 < (2 ^ 47 : Int)
  stackKnown : lookup state 4 = some (stack.signExtend 64)
  saved : Fin 5 → Word
  returnAddress : BitVec 48
  visible : Vector (BitVec 16) 6
  controls : Vector (BitVec 64) 17
  flags : BitVec 32
  visibleKnown : state.regs.get? .seg_visibles = some visible
  controlsKnown : state.regs.get? .ctrs = some controls
  flagsKnown : state.regs.get? .rflags = some flags
  quiet : state.regs.get? .log_register_writes = some false
  aligned : ∀ slot : Fin 6, address stack.toInt (8 * slot.val) &&& (7#48) = (0#48)
  present : ∀ slot : Fin 6, ∀ byte < 8,
    state.mem.get? (X86WriteWords.physicalAddress (address stack.toInt (8 * slot.val)) byte) =
      some ((if within : slot.val < 5 then saved ⟨slot.val, within⟩ else returnAddress.signExtend 64).extractLsb' (8 * byte) 8)

structure Inputs (state : State) extends FrameFacts state where
  context : X86PlainFetch.Facts state
  code : BitVec 48
  codeUpper : code.toInt + 10 < (2 ^ 47 : Int)
  loaded : codeLoaded state code.toInt expected
  rip : state.regs.get? .rip = some (code.signExtend 64)

def stackAt {state : State} (input : Inputs state) (slot : Nat) : BitVec 48 := address input.stack.toInt (8 * slot)
def codeAt {state : State} (input : Inputs state) (atOffset : Nat) : BitVec 48 := address input.code.toInt atOffset

theorem stack_int {state : State} (input : Inputs state) (slot : Nat) (within : slot ≤ 6) :
    (stackAt input slot).toInt = input.stack.toInt + 8 * slot :=
  address_toInt (extent := 48) input.stack.toInt (by simpa using BitVec.le_toInt input.stack) input.stackUpper
    (8 * slot) (by omega)

theorem code_int {state : State} (input : Inputs state) (atOffset : Nat) (within : atOffset ≤ 10) :
    (codeAt input atOffset).toInt = input.code.toInt + atOffset :=
  address_toInt (extent := 10) input.code.toInt (by simpa using BitVec.le_toInt input.code) input.codeUpper atOffset within

def first (state : State) (input : Inputs state) : State :=
  X86Stack.popResult state 15 (input.saved 0) (stackAt input 1) (codeAt input 2)
def second (state : State) (input : Inputs state) : State :=
  X86Stack.popResult (first state input) 14 (input.saved 1) (stackAt input 2) (codeAt input 4)
def third (state : State) (input : Inputs state) : State :=
  X86Stack.popResult (second state input) 13 (input.saved 2) (stackAt input 3) (codeAt input 6)
def fourth (state : State) (input : Inputs state) : State :=
  X86Stack.popResult (third state input) 12 (input.saved 3) (stackAt input 4) (codeAt input 8)
def fifth (state : State) (input : Inputs state) : State :=
  X86Stack.popResult (fourth state input) 3 (input.saved 4) (stackAt input 5) (codeAt input 9)
def finished (state : State) (input : Inputs state) : State := X86Stack.retResult (fifth state input) (stackAt input 6) input.returnAddress

def stage (state : State) (input : Inputs state) (index : Fin 6) : State := match index.val with
  | 0 => state | 1 => first state input | 2 => second state input | 3 => third state input
  | 4 => fourth state input | _ => fifth state input

def clobbers : Finset Register := {.rbx, .r12, .r13, .r14, .r15, .rsp, .rip}
theorem clobbers_data : clobbers ⊆ dataRegisters := by decide

theorem pop_clobbers (state : State) (index : Fin 5) (value : Word) (stack code : BitVec 48) :
    RegisterFrame clobbers state (X86Stack.popResult state (target index) value stack code) :=
  (X86Stack.pop_frame state (target index) value stack code).mono (by revert index; decide)

theorem stage_frame (state : State) (input : Inputs state) (index : Fin 6) :
    RegisterFrame clobbers state (stage state input index) := by
  have one : RegisterFrame clobbers state (first state input) := pop_clobbers state 0 _ _ _
  have two : RegisterFrame clobbers state (second state input) := by
    simpa [second, target] using one.trans (pop_clobbers (first state input) 1 (input.saved 1) _ _)
  have three : RegisterFrame clobbers state (third state input) := by
    simpa [third, target] using two.trans (pop_clobbers (second state input) 2 (input.saved 2) _ _)
  have four : RegisterFrame clobbers state (fourth state input) := by
    simpa [fourth, target] using three.trans (pop_clobbers (third state input) 3 (input.saved 3) _ _)
  have five : RegisterFrame clobbers state (fifth state input) := by
    simpa [fifth, target] using four.trans (pop_clobbers (fourth state input) 4 (input.saved 4) _ _)
  fin_cases index
  · exact RegisterFrame.refl _ state
  · exact one
  · exact two
  · exact three
  · exact four
  · exact five

theorem stage_rip (state : State) (input : Inputs state) (index : Fin 6) :
    (stage state input index).regs.get? .rip = some ((codeAt input (offset index)).signExtend 64) := by
  fin_cases index
  · simpa [stage, codeAt, offset, address, BitVec.ofInt_toInt] using input.rip
  all_goals exact X86FuelPrefix.pointer_rip _ _

theorem stage_stack (state : State) (input : Inputs state) (index : Fin 6) :
    lookup (stage state input index) 4 = some ((stackAt input index.val).signExtend 64) := by
  fin_cases index
  · simpa [stage, stackAt, address, BitVec.ofInt_toInt] using input.stackKnown
  · exact X86Stack.pop_stack _ 15 _ _ _ (by decide)
  · exact X86Stack.pop_stack _ 14 _ _ _ (by decide)
  · exact X86Stack.pop_stack _ 13 _ _ _ (by decide)
  · exact X86Stack.pop_stack _ 12 _ _ _ (by decide)
  · exact X86Stack.pop_stack _ 3 _ _ _ (by decide)

def stageContext (state : State) (input : Inputs state) (index : Fin 6) : X86PlainFetch.Facts (stage state input index) :=
  let frame := (stage_frame state input index).mono clobbers_data
  { input.context with
    status := (frame.registers .ms_reg (by decide)).trans input.context.status
    fault := (frame.registers .fault_reg (by decide)).trans input.context.fault
    msrs := (frame.registers .msrs (by decide)).trans input.context.msrs
    segments := (frame.registers .seg_hidden_attrs (by decide)).trans input.context.segments
    application := (frame.registers .app_view (by decide)).trans input.context.application }

def currentIndex (index : Fin 5) : Fin 6 := ⟨index.val, by omega⟩
def nextIndex (index : Fin 5) : Fin 6 := ⟨index.val + 1, by omega⟩
def opcodeOffset (index : Fin 5) : Nat := if index.val < 4 then 2 * index.val + 1 else 8

theorem offset_bound : ∀ index : Fin 6, offset index ≤ 10 := by decide
theorem opcode_bound : ∀ index : Fin 5, opcodeOffset index ≤ 10 := by decide
theorem pop_offsets : ∀ index : Fin 5,
    offset (currentIndex index) + X86Stack.popLength (target index) = offset (nextIndex index) := by decide
theorem opcode_offsets : ∀ index : Fin 5,
    opcodeOffset index = offset (currentIndex index) + (if (target index).val < 8 then 0 else 1) := by decide

theorem stage_next (state : State) (input : Inputs state) (index : Fin 5) :
    stage state input (nextIndex index) = X86Stack.popResult (stage state input (currentIndex index))
      (target index) (input.saved index) (stackAt input (index.val + 1)) (codeAt input (offset (nextIndex index))) := by
  fin_cases index <;> simp [stage, currentIndex, nextIndex, offset, target, first, second, third, fourth, fifth]

theorem pop_at (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (input : Inputs state) (index : Fin 5) :
    letI : OtherOpcodeHandlers := X86Stack.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    Step (stage state input (currentIndex index)) (stage state input (nextIndex index)) := by
  let : OtherOpcodeHandlers := X86Stack.linkedHandlers other
  let : VectorOpcodeHandlers := vector
  have frame := stage_frame state input (currentIndex index)
  rw [stage_next]
  apply X86Stack.fetched_pop other vector (stage state input (currentIndex index)) (target index)
    (stageContext state input (currentIndex index)) (codeAt input (offset (currentIndex index)))
    (codeAt input (opcodeOffset index)) (codeAt input (offset (nextIndex index)))
    (stackAt input index.val) (stackAt input (index.val + 1)) (input.saved index) input.visible input.controls input.flags
  · rw [code_int input _ (opcode_bound index), code_int input _ (offset_bound _)]
    have located := opcode_offsets index
    by_cases low : (target index).val < 8
    · simp only [low, ite_true] at located ⊢; omega
    · simp only [low, ite_false] at located ⊢; omega
  · rw [code_int input _ (offset_bound _), code_int input _ (offset_bound _)]
    have advance := pop_offsets index
    omega
  · rw [stack_int input index.val (by omega), stack_int input (index.val + 1) (by omega)]
    omega
  · rw [stack_int input index.val (by omega)]
    have := input.stackUpper
    have := index.isLt
    omega
  · exact stage_rip state input (currentIndex index)
  · exact stage_stack state input (currentIndex index)
  · exact (frame.registers .ctrs (by decide)).trans input.controlsKnown
  · exact (frame.registers .rflags (by decide)).trans input.flagsKnown
  · exact (frame.registers .seg_visibles (by decide)).trans input.visibleKnown
  · exact (frame.registers .log_register_writes (by decide)).trans input.quiet
  · exact input.aligned (currentIndex index)
  · fin_cases index
    · intro _; exact frame.code_preserved _ _ input.loaded 0 65 rfl
    · intro _; exact frame.code_preserved _ _ input.loaded 2 65 rfl
    · intro _; exact frame.code_preserved _ _ input.loaded 4 65 rfl
    · intro _; exact frame.code_preserved _ _ input.loaded 6 65 rfl
    · intro impossible; exact False.elim (impossible (by decide))
  · fin_cases index
    · exact frame.code_preserved _ _ input.loaded 1 95 rfl
    · exact frame.code_preserved _ _ input.loaded 3 94 rfl
    · exact frame.code_preserved _ _ input.loaded 5 93 rfl
    · exact frame.code_preserved _ _ input.loaded 7 92 rfl
    · exact frame.code_preserved _ _ input.loaded 8 91 rfl
  · intro byte within
    rw [frame.memory]
    have known := input.present (currentIndex index) byte within
    simpa [currentIndex, stackAt, index.isLt] using known

theorem ret_at (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (input : Inputs state) :
    letI : OtherOpcodeHandlers := X86Stack.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    Step (fifth state input) (finished state input) := by
  have frame : RegisterFrame clobbers state (fifth state input) := stage_frame state input (5 : Fin 6)
  apply X86Stack.fetched_ret other vector (fifth state input) (stageContext state input 5)
    (codeAt input 9) (codeAt input 10) (stackAt input 5) (stackAt input 6) input.returnAddress
    input.visible input.controls input.flags
  · rw [code_int input 9 (by decide), code_int input 10 (by decide)]; omega
  · rw [stack_int input 5 (by decide), stack_int input 6 (by decide)]; omega
  · rw [stack_int input 5 (by decide)]; have := input.stackUpper; omega
  · exact X86FuelPrefix.pointer_rip _ _
  · exact stage_stack state input 5
  · exact (frame.registers .ctrs (by decide)).trans input.controlsKnown
  · exact (frame.registers .rflags (by decide)).trans input.flagsKnown
  · exact (frame.registers .seg_visibles (by decide)).trans input.visibleKnown
  · exact (frame.registers .log_register_writes (by decide)).trans input.quiet
  · exact input.aligned 5
  · exact frame.code_preserved _ _ input.loaded 9 195 rfl
  · intro byte within
    rw [frame.memory]
    exact input.present 5 byte within

theorem executes (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers) (state : State) (input : Inputs state) :
    letI : OtherOpcodeHandlers := X86Stack.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    (X86FuelPrefix.fetches 6).run state = .ok () (finished state input) := by
  let : OtherOpcodeHandlers := X86Stack.linkedHandlers other
  let : VectorOpcodeHandlers := vector
  exact X86FuelPrefix.fetches_cons 5 state (first state input) (finished state input) (pop_at other vector state input 0)
    (X86FuelPrefix.fetches_cons 4 _ _ _ (pop_at other vector state input 1)
      (X86FuelPrefix.fetches_cons 3 _ _ _ (pop_at other vector state input 2)
        (X86FuelPrefix.fetches_cons 2 _ _ _ (pop_at other vector state input 3)
          (X86FuelPrefix.fetches_cons 1 _ _ _ (pop_at other vector state input 4)
            (X86FuelPrefix.fetches_one _ _ (ret_at other vector state input))))))

theorem finished_frame (state : State) (input : Inputs state) : RegisterFrame clobbers state (finished state input) := by
  apply ((stage_frame state input (5 : Fin 6)).trans
    (X86Stack.ret_frame (fifth state input) (stackAt input 6) input.returnAddress)).mono
  intro register present
  simp only [clobbers, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at present ⊢
  tauto

theorem finished_restores (state : State) (input : Inputs state) (index : Fin 5) :
    lookup (finished state input) (target index) = some (input.saved index) := by
  fin_cases index <;> simp [target, finished, fifth, fourth, third, second, first,
    X86Stack.ret_other, X86Stack.pop_other, X86Stack.pop_value]

structure Result (state : State) (input : Inputs state) (after : State) : Prop where
  pointer : after.regs.get? .rip = some (input.returnAddress.signExtend 64)
  stackPointer : lookup after 4 = some ((stackAt input 6).signExtend 64)
  saved : ∀ index : Fin 5, lookup after (target index) = some (input.saved index)
  frame : RegisterFrame clobbers state after
  rax : lookup after 0 = lookup state 0
  flags : after.regs.get? .rflags = some input.flags

theorem finished_result (state : State) (input : Inputs state) : Result state input (finished state input) :=
  ⟨X86FuelPrefix.pointer_rip _ _, X86Stack.ret_stack _ _ _, finished_restores state input,
    finished_frame state input, (finished_frame state input).lookup 0 (by decide),
    ((finished_frame state input).registers .rflags (by decide)).trans input.flagsKnown⟩

theorem any_run_refines (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (input : Inputs state) (after : State) :
    letI : OtherOpcodeHandlers := X86Stack.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    (X86FuelPrefix.fetches 6).run state = .ok () after → Result state input after := by
  intro observed
  have same := (EStateM.Result.ok.inj ((executes other vector state input).symm.trans observed)).2
  simpa only [same] using finished_result state input

theorem Result.image_preserved {state after : State} {input : Inputs state} (correct : Result state input after)
    (base : Int) (view : NativeImage.View) (placed : X86CodePlacement.Placed state base view) :
    X86CodePlacement.Placed after base view := by
  intro index byte present
  rw [correct.frame.memory]
  exact placed index byte present

namespace Controls
private def modeControl : Vector (BitVec 64) 7 :=
  Vector.ofFn (fun index => if index.val = 0 then (0x400#64) else (0#64))
private def attributes : Vector (BitVec 16) 6 :=
  Vector.ofFn (fun index => if index.val = 1 then (0x200#16) else (0#16))
private def visible : Vector (BitVec 16) 6 := Vector.replicate 6 (0#16)
private def controls : Vector (BitVec 64) 17 := Vector.replicate 17 (0#64)
private def saved (index : Fin 5) : Word := #[0xfedcba9876543210#64, 0x0123456789abcdef#64, 42#64, 99#64, 7#64][index.val]'(by exact index.isLt)
private def wordAt (slot : Fin 6) : Word := if within : slot.val < 5 then saved ⟨slot.val, within⟩ else (0x3000#64)
private def cells : List (Nat × BitVec 8) :=
  (List.range 10).map (fun index => (4096 + index, BitVec.ofNat 8 ((expected[index]?).getD 0))) ++
  (List.finRange 6).flatMap (fun slot => (List.range 8).map (fun byte =>
    (8192 + 8 * slot.val + byte, (wordAt slot).extractLsb' (8 * byte) 8))) ++ [(8240, 42#8)]
private theorem distinct : cells.Pairwise (fun left right => (left.1 == right.1) = false) := by
  have keys : (cells.map Prod.fst).Nodup := by
    simp only [cells, List.map_append, List.map_map, List.map_flatMap, Function.comp_def]
    decide
  simpa only [List.nodup_iff_pairwise_ne, List.pairwise_map, beq_eq_false_iff_ne] using keys
private def before : State :=
  let registers := (∅ : Std.ExtDHashMap Register RegisterType).insert .ms_reg false
  let registers := registers.insert .fault_reg false
  let registers := registers.insert .msrs modeControl
  let registers := registers.insert .seg_hidden_attrs attributes
  let registers := registers.insert .app_view true
  let registers := registers.insert .rip (0x1000#64)
  let registers := registers.insert .rsp (0x2000#64)
  let registers := registers.insert .rax (4#64)
  let registers := registers.insert .ctrs controls
  let registers := registers.insert .rflags (0#32)
  let registers := registers.insert .seg_visibles visible
  let registers := registers.insert .log_register_writes false
  ⟨registers, (), Std.ExtHashMap.ofList cells, (), 0, #[]⟩
private theorem cell (key : Nat) (byte : BitVec 8) (present : (key, byte) ∈ cells) :
    before.mem.get? key = some byte := Std.ExtHashMap.getElem?_ofList_of_mem (by simp) distinct present

private def input : Inputs before where
  context := {
    control := modeControl, attributes := attributes
    status := by simp [before, Std.ExtDHashMap.get?_insert]
    fault := by simp [before, Std.ExtDHashMap.get?_insert]
    msrs := by simp [before, Std.ExtDHashMap.get?_insert]
    segments := by simp [before, Std.ExtDHashMap.get?_insert]
    longMode := by decide
    codeMode := by decide
    application := by simp [before, Std.ExtDHashMap.get?_insert] }
  code := 0x1000#48
  codeUpper := by decide
  loaded := by
    intro index byte present
    have within : index < 10 := (List.getElem?_eq_some_iff.mp present).choose
    have member : (4096 + index, BitVec.ofNat 8 byte) ∈ cells := by
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_map.mpr
      refine ⟨index, List.mem_range.mpr within, ?_⟩
      simp only [present, Option.getD_some]
    have got := cell (4096 + index) (BitVec.ofNat 8 byte) member
    interval_cases index <;> exact got
  rip := by simp [before, Std.ExtDHashMap.get?_insert]
  stack := 0x2000#48
  stackUpper := by decide
  stackKnown := by simp [before, lookup, key, cast_eq, Std.ExtDHashMap.get?_insert]; rfl
  saved := saved
  returnAddress := 0x3000#48
  visible := visible
  controls := controls
  flags := 0#32
  visibleKnown := by simp [before, Std.ExtDHashMap.get?_insert]
  controlsKnown := by simp [before, Std.ExtDHashMap.get?_insert]
  flagsKnown := by simp [before, Std.ExtDHashMap.get?_insert]
  quiet := by simp [before]
  aligned := by intro slot; fin_cases slot <;> decide
  present := by
    intro slot byte within
    have member : (8192 + 8 * slot.val + byte, (wordAt slot).extractLsb' (8 * byte) 8) ∈ cells := by
      apply List.mem_append_left
      apply List.mem_append_right
      apply List.mem_flatMap.mpr
      refine ⟨slot, List.mem_finRange _, ?_⟩
      exact List.mem_map.mpr ⟨byte, List.mem_range.mpr within, rfl⟩
    have got := cell _ _ member
    fin_cases slot <;> interval_cases byte <;> exact got

theorem restores_and_returns (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := X86Stack.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 6).run before = .ok () after ∧
      after.regs.get? .rip = some (0x3000#64) ∧ lookup after 4 = some (0x2030#64) ∧
      lookup after 15 = some (0xfedcba9876543210#64) ∧ lookup after 14 = some (0x0123456789abcdef#64) ∧
      lookup after 13 = some (42#64) ∧ lookup after 12 = some (99#64) ∧ lookup after 3 = some (7#64) ∧
      lookup after 0 = some (4#64) ∧ after.mem = before.mem := by
  have correct := finished_result before input
  refine ⟨_, executes other vector before input, correct.pointer, correct.stackPointer,
    correct.saved 0, correct.saved 1, correct.saved 2, correct.saved 3, correct.saved 4, ?_, correct.frame.memory⟩
  rw [correct.rax]
  simp [before, lookup, key, cast_eq, Std.ExtDHashMap.get?_insert]
  rfl

theorem unrestored_register_refused (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (after : State) (wrong : lookup after 12 = some (0#64)) :
    letI : OtherOpcodeHandlers := X86Stack.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    (X86FuelPrefix.fetches 6).run before ≠ .ok () after := by
  intro observed
  obtain ⟨proved, run, _, _, _, _, _, restored, _, _, _⟩ := restores_and_returns other vector
  have same := (EStateM.Result.ok.inj (run.symm.trans observed)).2
  rw [same, wrong] at restored
  contradiction

end Controls
end Mettapedia.Machines.TIsa.X86Epilogue

#print axioms Mettapedia.Machines.TIsa.X86Epilogue.executes
#print axioms Mettapedia.Machines.TIsa.X86Epilogue.finished_result
#print axioms Mettapedia.Machines.TIsa.X86Epilogue.any_run_refines
#print axioms Mettapedia.Machines.TIsa.X86Epilogue.Result.image_preserved
#print axioms Mettapedia.Machines.TIsa.X86Epilogue.Controls.restores_and_returns
#print axioms Mettapedia.Machines.TIsa.X86Epilogue.Controls.unrestored_register_refused
