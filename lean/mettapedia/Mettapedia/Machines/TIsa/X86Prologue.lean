import Mettapedia.Machines.TIsa.X86Stack
import Mettapedia.Machines.TIsa.X86Epilogue
import Mettapedia.Machines.TIsa.X86FuelPrefix
import Mettapedia.Machines.TIsa.X86CodePlacement

/-!
# The public native prologue establishes saved-stack provenance

Five original fetched PUSH instructions execute the emitted nine-byte prefix.
The forty saved bytes contain the caller's actual RBX and R12--R15 values,
in the order consumed by the epilogue. The caller return address and every
location outside those bytes survive. Register and flag frames keep caller
facts available without expanding predecessor states.

The saved-word and return-address proofs construct the existing epilogue's
stack facts. Body/control composition, complete ABI calls, source admission
and full native compiler refinement remain separate obligations.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Mettapedia.Machines.TIsa.X86Prologue
open _root_.X86Registers X86RegisterRefinement X86Execution X86Stack
local instance : MemoryPrimitives := X86Memory.ordinary

def expected : List Nat := [0x53, 0x41, 0x54, 0x41, 0x55, 0x41, 0x56, 0x41, 0x57]
def source (index : Fin 5) : Fin 16 := #[3, 12, 13, 14, 15][index.val]'(by exact index.isLt)
def offset (index : Fin 6) : Nat := if index.val = 0 then 0 else 2 * index.val - 1
def writes (bottom : BitVec 48) : Finset Nat := X86WriteWords.written bottom (List.range 40)

structure Inputs (state : State) where
  bottom : BitVec 48
  stackUpper : bottom.toInt + 48 < (2 ^ 47 : Int)
  stackKnown : lookup state 4 = some ((address bottom.toInt 40).signExtend 64)
  saved : Fin 5 → Word
  savedKnown : ∀ index, lookup state (source index) = some (saved index)
  returnAddress : BitVec 48
  returnBytes : ∀ byte < 8,
    state.mem.get? (X86WriteWords.physicalAddress (address bottom.toInt 40) byte) =
      some ((returnAddress.signExtend 64).extractLsb' (8 * byte) 8)
  visible : Vector (BitVec 16) 6
  controls : Vector (BitVec 64) 17
  flags : BitVec 32
  visibleKnown : state.regs.get? .seg_visibles = some visible
  controlsKnown : state.regs.get? .ctrs = some controls
  flagsKnown : state.regs.get? .rflags = some flags
  quiet : state.regs.get? .log_register_writes = some false
  aligned : ∀ slot : Fin 6, address bottom.toInt (8 * slot.val) &&& (7#48) = (0#48)
  context : X86PlainFetch.Facts state
  code : BitVec 48
  codeUpper : code.toInt + 9 < (2 ^ 47 : Int)
  loaded : codeLoaded state code.toInt expected
  rip : state.regs.get? .rip = some (code.signExtend 64)
  codeOutside : ∀ index byte, expected[index]? = some byte →
    ((address code.toInt index).signExtend 52).toNat ∉ writes bottom

def stackAt {state : State} (input : Inputs state) (slot : Nat) : BitVec 48 :=
  address input.bottom.toInt (8 * slot)
def codeAt {state : State} (input : Inputs state) (atOffset : Nat) : BitVec 48 :=
  address input.code.toInt atOffset

theorem stack_int {state : State} (input : Inputs state) (slot : Nat) (within : slot ≤ 6) :
    (stackAt input slot).toInt = input.bottom.toInt + 8 * slot :=
  address_toInt (extent := 48) input.bottom.toInt (by simpa using BitVec.le_toInt input.bottom)
    input.stackUpper (8 * slot) (by omega)

theorem code_int {state : State} (input : Inputs state) (atOffset : Nat) (within : atOffset ≤ 9) :
    (codeAt input atOffset).toInt = input.code.toInt + atOffset :=
  address_toInt (extent := 9) input.code.toInt (by simpa using BitVec.le_toInt input.code)
    input.codeUpper atOffset within

theorem stack_byte {state : State} (input : Inputs state) (slot byte : Nat) (within : slot ≤ 6) :
    X86WriteWords.physicalAddress (stackAt input slot) byte =
      X86WriteWords.physicalAddress input.bottom (8 * slot + byte) := by
  unfold X86WriteWords.physicalAddress
  rw [stack_int input slot within]
  simp [address, Int.add_assoc]

theorem word_subset {state : State} (input : Inputs state) (slot count : Nat)
    (inside : slot < count) (bounded : count ≤ 6) :
    X86WriteWords.written (stackAt input slot) (List.range 8) ⊆
      X86WriteWords.written input.bottom (List.range (8 * count)) := by
  intro key present
  simp only [X86WriteWords.written, List.mem_toFinset, List.mem_map] at present ⊢
  obtain ⟨byte, within, rfl⟩ := present
  refine ⟨8 * slot + byte, List.mem_range.mpr (by have := List.mem_range.mp within; omega), ?_⟩
  exact (stack_byte input slot byte (by omega)).symm

def first (state : State) (input : Inputs state) : State :=
  pushResult state (input.saved 0) (stackAt input 4) (codeAt input 1)
def second (state : State) (input : Inputs state) : State :=
  pushResult (first state input) (input.saved 1) (stackAt input 3) (codeAt input 3)
def third (state : State) (input : Inputs state) : State :=
  pushResult (second state input) (input.saved 2) (stackAt input 2) (codeAt input 5)
def fourth (state : State) (input : Inputs state) : State :=
  pushResult (third state input) (input.saved 3) (stackAt input 1) (codeAt input 7)
def finished (state : State) (input : Inputs state) : State :=
  pushResult (fourth state input) (input.saved 4) (stackAt input 0) (codeAt input 9)

def stage (state : State) (input : Inputs state) (index : Fin 6) : State := match index.val with
  | 0 => state | 1 => first state input | 2 => second state input | 3 => third state input
  | 4 => fourth state input | _ => finished state input

theorem push_within (current state : State) (input : Inputs state) (slot count : Nat)
    (inside : slot < count) (bounded : count ≤ 6) (value : Word) (code : BitVec 48) :
    X86StateFrame.Frame {.rsp, .rip} (X86WriteWords.written input.bottom (List.range (8 * count)))
      current (pushResult current value (stackAt input slot) code) :=
  (push_frame current value _ code).mono (Finset.Subset.refl _) (word_subset input slot count inside bounded)

theorem stage_frame (state : State) (input : Inputs state) (index : Fin 6) :
    X86StateFrame.Frame {.rsp, .rip} (writes input.bottom) state (stage state input index) := by
  have one := push_within state state input 4 5 (by decide) (by decide) (input.saved 0) (codeAt input 1)
  have two : X86StateFrame.Frame {.rsp, .rip} (writes input.bottom) state (second state input) := by
    simpa only [writes, second, Finset.union_self] using
      one.trans (push_within (first state input) state input 3 5 (by decide) (by decide) (input.saved 1) (codeAt input 3))
  have three : X86StateFrame.Frame {.rsp, .rip} (writes input.bottom) state (third state input) := by
    simpa only [writes, third, Finset.union_self] using
      two.trans (push_within (second state input) state input 2 5 (by decide) (by decide) (input.saved 2) (codeAt input 5))
  have four : X86StateFrame.Frame {.rsp, .rip} (writes input.bottom) state (fourth state input) := by
    simpa only [writes, fourth, Finset.union_self] using
      three.trans (push_within (third state input) state input 1 5 (by decide) (by decide) (input.saved 3) (codeAt input 7))
  have five : X86StateFrame.Frame {.rsp, .rip} (writes input.bottom) state (finished state input) := by
    simpa only [writes, finished, Finset.union_self] using
      four.trans (push_within (fourth state input) state input 0 5 (by decide) (by decide) (input.saved 4) (codeAt input 9))
  fin_cases index
  · exact X86StateFrame.Frame.refl _ _ _
  · exact one
  · exact two
  · exact three
  · exact four
  · exact five

def stageContext (state : State) (input : Inputs state) (index : Fin 6) :
    X86PlainFetch.Facts (stage state input index) :=
  let frame := stage_frame state input index
  { input.context with
    status := (frame.registers .ms_reg (by decide)).trans input.context.status
    fault := (frame.registers .fault_reg (by decide)).trans input.context.fault
    msrs := (frame.registers .msrs (by decide)).trans input.context.msrs
    segments := (frame.registers .seg_hidden_attrs (by decide)).trans input.context.segments
    application := (frame.registers .app_view (by decide)).trans input.context.application }

theorem stage_rip (state : State) (input : Inputs state) (index : Fin 6) :
    (stage state input index).regs.get? .rip = some ((codeAt input (offset index)).signExtend 64) := by
  fin_cases index
  · simpa [stage, offset, codeAt, address, BitVec.ofInt_toInt] using input.rip
  all_goals exact X86FuelPrefix.pointer_rip _ _

theorem stage_stack (state : State) (input : Inputs state) (index : Fin 6) :
    lookup (stage state input index) 4 = some ((stackAt input (5 - index.val)).signExtend 64) := by
  fin_cases index
  · exact input.stackKnown
  all_goals exact push_stack _ _ _ _

def currentIndex (index : Fin 5) : Fin 6 := ⟨index.val, by omega⟩
def nextIndex (index : Fin 5) : Fin 6 := ⟨index.val + 1, by omega⟩
def opcodeOffset (index : Fin 5) : Nat :=
  offset (currentIndex index) + (if (source index).val < 8 then 0 else 1)

theorem offset_bound : ∀ index : Fin 6, offset index ≤ 9 := by decide
theorem opcode_bound : ∀ index : Fin 5, opcodeOffset index ≤ 9 := by decide
theorem push_offsets : ∀ index : Fin 5,
    offset (currentIndex index) + pushLength (source index) = offset (nextIndex index) := by decide

theorem stage_next (state : State) (input : Inputs state) (index : Fin 5) :
    stage state input (nextIndex index) = pushResult (stage state input (currentIndex index))
      (input.saved index) (stackAt input (4 - index.val)) (codeAt input (offset (nextIndex index))) := by
  fin_cases index <;> rfl

theorem code_at {state current : State} (input : Inputs state)
    (frame : X86StateFrame.Frame {.rsp, .rip} (writes input.bottom) state current)
    (index byte : Nat) (present : expected[index]? = some byte) :
    current.mem.get? ((address input.code.toInt index).signExtend 52).toNat = some (BitVec.ofNat 8 byte) :=
  frame.codeLoaded _ _ input.loaded input.codeOutside index byte present

theorem push_at (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (input : Inputs state) (index : Fin 5) :
    letI : OtherOpcodeHandlers := X86Stack.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    Step (stage state input (currentIndex index)) (stage state input (nextIndex index)) := by
  let : OtherOpcodeHandlers := X86Stack.linkedHandlers other
  let : VectorOpcodeHandlers := vector
  have frame := stage_frame state input (currentIndex index)
  rw [stage_next]
  apply fetched_push other vector (stage state input (currentIndex index)) (source index)
    (stageContext state input (currentIndex index)) (codeAt input (offset (currentIndex index)))
    (codeAt input (opcodeOffset index)) (codeAt input (offset (nextIndex index)))
    (stackAt input (5 - index.val)) (stackAt input (4 - index.val)) (input.saved index)
    input.visible input.controls input.flags
  · rw [code_int input _ (opcode_bound index), code_int input _ (offset_bound _)]
    simp only [opcodeOffset, Int.natCast_add]
    split <;> simp_all [Int.add_assoc]
  · rw [code_int input _ (offset_bound _), code_int input _ (offset_bound _)]
    have advance := push_offsets index
    omega
  · rw [stack_int input (4 - index.val) (by omega), stack_int input (5 - index.val) (by omega)]
    have := index.isLt
    omega
  · rw [stack_int input (4 - index.val) (by omega)]
    have := input.stackUpper
    have := index.isLt
    omega
  · exact stage_rip state input (currentIndex index)
  · exact stage_stack state input (currentIndex index)
  · exact (frame.lookup (source index) (by fin_cases index <;> decide)).trans (input.savedKnown index)
  · exact (frame.registers .ctrs (by decide)).trans input.controlsKnown
  · exact (frame.registers .rflags (by decide)).trans input.flagsKnown
  · exact (frame.registers .seg_visibles (by decide)).trans input.visibleKnown
  · exact (frame.registers .log_register_writes (by decide)).trans input.quiet
  · exact input.aligned ⟨4 - index.val, by omega⟩
  · intro high
    fin_cases index
    · contradiction
    all_goals exact code_at input frame _ _ rfl
  · fin_cases index <;> exact code_at input frame _ _ rfl

theorem executes (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (input : Inputs state) :
    letI : OtherOpcodeHandlers := X86Stack.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    (X86FuelPrefix.fetches 5).run state = .ok () (finished state input) := by
  let : OtherOpcodeHandlers := X86Stack.linkedHandlers other
  let : VectorOpcodeHandlers := vector
  exact X86FuelPrefix.fetches_cons 4 state (first state input) (finished state input) (push_at other vector state input 0)
    (X86FuelPrefix.fetches_cons 3 _ _ _ (push_at other vector state input 1)
      (X86FuelPrefix.fetches_cons 2 _ _ _ (push_at other vector state input 2)
        (X86FuelPrefix.fetches_cons 1 _ _ _ (push_at other vector state input 3)
          (X86FuelPrefix.fetches_one _ _ (push_at other vector state input 4)))))


theorem byte_outside {state : State} (input : Inputs state) (count byte : Nat)
    (after : count ≤ byte) (within : byte < 48) :
    X86WriteWords.physicalAddress input.bottom byte ∉
      X86WriteWords.written input.bottom (List.range count) := by
  intro present
  simp only [X86WriteWords.written, List.mem_toFinset, List.mem_map] at present
  obtain ⟨other, inside, same⟩ := present
  have earlier := List.mem_range.mp inside
  have equal := X86WriteWords.physicalAddress_injective 48 input.bottom (by have := input.stackUpper; omega)
    other byte (by omega) within same
  omega

theorem tail_frame (state : State) (input : Inputs state) (slot : Fin 5) :
    X86StateFrame.Frame {.rsp, .rip} (X86WriteWords.written input.bottom (List.range (8 * slot.val)))
      (stage state input ⟨5 - slot.val, by omega⟩) (finished state input) := by
  fin_cases slot
  · exact X86StateFrame.Frame.refl _ _ _
  · exact push_within (fourth state input) state input 0 1 (by decide) (by decide) (input.saved 4) (codeAt input 9)
  · have a := push_within (third state input) state input 1 2 (by decide) (by decide) (input.saved 3) (codeAt input 7)
    have b := push_within (fourth state input) state input 0 2 (by decide) (by decide) (input.saved 4) (codeAt input 9)
    simpa only [stage, finished, fourth, Finset.union_self] using a.trans b
  · have a := push_within (second state input) state input 2 3 (by decide) (by decide) (input.saved 2) (codeAt input 5)
    have b := push_within (third state input) state input 1 3 (by decide) (by decide) (input.saved 3) (codeAt input 7)
    have c := push_within (fourth state input) state input 0 3 (by decide) (by decide) (input.saved 4) (codeAt input 9)
    simpa only [stage, finished, fourth, third, Finset.union_self] using a.trans (b.trans c)
  · have a := push_within (first state input) state input 3 4 (by decide) (by decide) (input.saved 1) (codeAt input 3)
    have b := push_within (second state input) state input 2 4 (by decide) (by decide) (input.saved 2) (codeAt input 5)
    have c := push_within (third state input) state input 1 4 (by decide) (by decide) (input.saved 3) (codeAt input 7)
    have d := push_within (fourth state input) state input 0 4 (by decide) (by decide) (input.saved 4) (codeAt input 9)
    simpa only [stage, finished, fourth, third, second, Finset.union_self] using a.trans (b.trans (c.trans d))

theorem just_written (state : State) (input : Inputs state) (index : Fin 5) :
    (stage state input (nextIndex index)).mem =
      (X86WriteWords.storeBytes 8 (stage state input (currentIndex index))
        (stackAt input (4 - index.val)) (input.saved index)).mem := by
  rw [stage_next]
  exact push_memory _ _ _ _

theorem saved_bytes (state : State) (input : Inputs state) (slot : Fin 5) (byte : Nat) (within : byte < 8) :
    (finished state input).mem.get? (X86WriteWords.physicalAddress (stackAt input slot.val) byte) =
      some ((input.saved ⟨4 - slot.val, by omega⟩).extractLsb' (8 * byte) 8) := by
  have outside : X86WriteWords.physicalAddress (stackAt input slot.val) byte ∉
      X86WriteWords.written input.bottom (List.range (8 * slot.val)) := by
    rw [stack_byte input slot.val byte (by omega)]
    exact byte_outside input _ _ (by omega) (by have := slot.isLt; omega)
  let index : Fin 5 := ⟨4 - slot.val, by omega⟩
  have after : nextIndex index = ⟨5 - slot.val, by omega⟩ := by
    apply Fin.ext
    dsimp [nextIndex, index]
    have := slot.isLt
    omega
  have atSlot : 4 - index.val = slot.val := by dsimp [index]; have := slot.isLt; omega
  have memory := just_written state input index
  rw [after, atSlot] at memory
  rw [(tail_frame state input slot).memory _ outside, memory]
  exact X86WriteWords.store_word_byte _ (stackAt input slot.val) _
    (by rw [stack_int input slot.val (by omega)]; have := input.stackUpper; have := slot.isLt; omega) byte within

theorem finished_frame (state : State) (input : Inputs state) :
    X86StateFrame.Frame {.rsp, .rip} (writes input.bottom) state (finished state input) := by
  simpa only [stage] using stage_frame state input (5 : Fin 6)

theorem return_bytes (state : State) (input : Inputs state) (byte : Nat) (within : byte < 8) :
    (finished state input).mem.get? (X86WriteWords.physicalAddress (stackAt input 5) byte) =
      some ((input.returnAddress.signExtend 64).extractLsb' (8 * byte) 8) := by
  have outside : X86WriteWords.physicalAddress (stackAt input 5) byte ∉ writes input.bottom := by
    rw [stack_byte input 5 byte (by decide)]
    exact byte_outside input _ _ (by omega) (by omega)
  rw [(finished_frame state input).memory _ outside]
  exact input.returnBytes byte within

def epilogueSaved {state : State} (input : Inputs state) (index : Fin 5) : Word :=
  input.saved ⟨4 - index.val, by omega⟩

theorem saved_source : ∀ index : Fin 5,
    source ⟨4 - index.val, by omega⟩ = X86Epilogue.target index := by decide

def epilogueStackFacts (state : State) (input : Inputs state) :
    X86Epilogue.FrameFacts (finished state input) where
  stack := input.bottom
  stackUpper := input.stackUpper
  stackKnown := by
    simpa [stage, stackAt, address, BitVec.ofInt_toInt] using stage_stack state input (5 : Fin 6)
  saved := epilogueSaved input
  returnAddress := input.returnAddress
  visible := input.visible
  controls := input.controls
  flags := input.flags
  visibleKnown := ((stage_frame state input 5).registers .seg_visibles (by decide)).trans input.visibleKnown
  controlsKnown := ((stage_frame state input 5).registers .ctrs (by decide)).trans input.controlsKnown
  flagsKnown := ((stage_frame state input 5).registers .rflags (by decide)).trans input.flagsKnown
  quiet := ((stage_frame state input 5).registers .log_register_writes (by decide)).trans input.quiet
  aligned := input.aligned
  present slot byte within := by
    by_cases saved : slot.val < 5
    · simpa only [saved, dite_true, epilogueSaved, stackAt] using saved_bytes state input ⟨slot.val, saved⟩ byte within
    · have last : slot.val = 5 := by have := slot.isLt; omega
      simpa [last, stackAt] using return_bytes state input byte within


structure Result (state : State) (input : Inputs state) (after : State) : Prop where
  pointer : after.regs.get? .rip = some ((codeAt input 9).signExtend 64)
  stackPointer : lookup after 4 = some (input.bottom.signExtend 64)
  saved : ∀ slot : Fin 5, ∀ byte < 8,
    after.mem.get? (X86WriteWords.physicalAddress (stackAt input slot.val) byte) =
      some ((epilogueSaved input slot).extractLsb' (8 * byte) 8)
  returnBytes : ∀ byte < 8,
    after.mem.get? (X86WriteWords.physicalAddress (stackAt input 5) byte) =
      some ((input.returnAddress.signExtend 64).extractLsb' (8 * byte) 8)
  frame : X86StateFrame.Frame {.rsp, .rip} (writes input.bottom) state after
  flags : after.regs.get? .rflags = some input.flags

theorem finished_result (state : State) (input : Inputs state) : Result state input (finished state input) where
  pointer := by simpa [stage, offset] using stage_rip state input (5 : Fin 6)
  stackPointer := (epilogueStackFacts state input).stackKnown
  saved := saved_bytes state input
  returnBytes := return_bytes state input
  frame := finished_frame state input
  flags := ((finished_frame state input).registers .rflags (by decide)).trans input.flagsKnown

theorem any_run_refines (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (input : Inputs state) (after : State) :
    letI : OtherOpcodeHandlers := X86Stack.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    (X86FuelPrefix.fetches 5).run state = .ok () after → Result state input after := by
  let : OtherOpcodeHandlers := X86Stack.linkedHandlers other
  let : VectorOpcodeHandlers := vector
  intro observed
  have same := (EStateM.Result.ok.inj ((executes other vector state input).symm.trans observed)).2
  subst after
  exact finished_result state input

namespace Controls
private def modeControl : Vector (BitVec 64) 7 :=
  Vector.ofFn (fun index => if index.val = 0 then (0x400#64) else (0#64))
private def attributes : Vector (BitVec 16) 6 :=
  Vector.ofFn (fun index => if index.val = 1 then (0x200#16) else (0#16))
private def visible : Vector (BitVec 16) 6 := Vector.replicate 6 (0#16)
private def controls : Vector (BitVec 64) 17 := Vector.replicate 17 (0#64)
private def saved (index : Fin 5) : Word :=
  #[7#64, 99#64, 42#64, 0x0123456789abcdef#64, 0xfedcba9876543210#64][index.val]'(by exact index.isLt)
private def cells : List (Nat × BitVec 8) :=
  (List.range 9).map (fun index => (4096 + index, BitVec.ofNat 8 ((expected[index]?).getD 0))) ++
  (List.range 10).map (fun index => (4105 + index, BitVec.ofNat 8 ((X86Epilogue.expected[index]?).getD 0))) ++
  (List.range 48).map (fun index => (8192 + index, if index < 40 then (0#8) else
    (0x3000#64).extractLsb' (8 * (index - 40)) 8)) ++ [(8191, 91#8), (8240, 42#8)]

private theorem distinct : cells.Pairwise (fun left right => (left.1 == right.1) = false) := by
  have keys : (cells.map Prod.fst).Nodup := by
    simp only [cells, List.map_append, List.map_map, Function.comp_def]
    decide
  simpa only [List.nodup_iff_pairwise_ne, List.pairwise_map, beq_eq_false_iff_ne] using keys

private def before : State :=
  let registers := (∅ : Std.ExtDHashMap Register RegisterType).insert .ms_reg false
  let registers := registers.insert .fault_reg false
  let registers := registers.insert .msrs modeControl
  let registers := registers.insert .seg_hidden_attrs attributes
  let registers := registers.insert .app_view true
  let registers := registers.insert .rip (0x1000#64)
  let registers := registers.insert .rsp (0x2028#64)
  let registers := registers.insert .rbx (saved 0)
  let registers := registers.insert .r12 (saved 1)
  let registers := registers.insert .r13 (saved 2)
  let registers := registers.insert .r14 (saved 3)
  let registers := registers.insert .r15 (saved 4)
  let registers := registers.insert .rax (4#64)
  let registers := registers.insert .ctrs controls
  let registers := registers.insert .rflags (0#32)
  let registers := registers.insert .seg_visibles visible
  let registers := registers.insert .log_register_writes false
  ⟨registers, (), Std.ExtHashMap.ofList cells, (), 0, #[]⟩

private theorem cell (key : Nat) (byte : BitVec 8) (present : (key, byte) ∈ cells) :
    before.mem.get? key = some byte :=
  Std.ExtHashMap.getElem?_ofList_of_mem (by simp) distinct present

private def input : Inputs before where
  bottom := 0x2000#48
  stackUpper := by decide
  stackKnown := by simp [before, lookup, key, cast_eq, Std.ExtDHashMap.get?_insert]; rfl
  saved := saved
  savedKnown := by
    intro index
    fin_cases index <;> simp [before, lookup, source, key, cast_eq, Std.ExtDHashMap.get?_insert] <;> rfl
  returnAddress := 0x3000#48
  returnBytes := by
    intro byte within
    have member : (8192 + (40 + byte), (0x3000#64).extractLsb' (8 * byte) 8) ∈ cells := by
      apply List.mem_append_left
      apply List.mem_append_right
      apply List.mem_map.mpr
      refine ⟨40 + byte, List.mem_range.mpr (by omega), ?_⟩
      simp [show ¬40 + byte < 40 from by omega]
    have got := cell _ _ member
    interval_cases byte <;> exact got
  visible := visible
  controls := controls
  flags := 0#32
  visibleKnown := by simp [before, Std.ExtDHashMap.get?_insert]
  controlsKnown := by simp [before, Std.ExtDHashMap.get?_insert]
  flagsKnown := by simp [before, Std.ExtDHashMap.get?_insert]
  quiet := by simp [before]
  aligned := by intro slot; fin_cases slot <;> decide
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
    have within : index < 9 := (List.getElem?_eq_some_iff.mp present).choose
    have member : (4096 + index, BitVec.ofNat 8 byte) ∈ cells := by
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_map.mpr
      refine ⟨index, List.mem_range.mpr within, ?_⟩
      simp only [present, Option.getD_some]
    have got := cell _ _ member
    interval_cases index <;> exact got
  rip := by simp [before, Std.ExtDHashMap.get?_insert]
  codeOutside := by
    intro index byte present member
    have within : index < 9 := (List.getElem?_eq_some_iff.mp present).choose
    simp only [writes, X86WriteWords.written, List.mem_toFinset, List.mem_map] at member
    obtain ⟨stackByte, inside, same⟩ := member
    have bounded := List.mem_range.mp inside
    interval_cases index <;> interval_cases stackByte <;> contradiction

theorem saves_initial_registers (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := X86Stack.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 5).run before = .ok () after ∧
      after.regs.get? .rip = some (4105#64) ∧ lookup after 4 = some (8192#64) ∧
      after.mem.get? 8192 = some (0x10#8) ∧ after.mem.get? 8199 = some (0xfe#8) ∧
      after.mem.get? 8224 = some (7#8) ∧ after.mem.get? 8233 = some (0x30#8) ∧
      lookup after 0 = some (4#64) := by
  have correct := finished_result before input
  refine ⟨_, executes other vector before input, correct.pointer, correct.stackPointer,
    correct.saved 0 0 (by decide), correct.saved 0 7 (by decide), correct.saved 4 0 (by decide),
    correct.returnBytes 1 (by decide), ?_⟩
  rw [correct.frame.lookup 0 (by decide)]
  simp [before, lookup, key, cast_eq, Std.ExtDHashMap.get?_insert]
  rfl

theorem stale_stack_word_refused (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (after : State) (wrong : after.mem.get? 8192 = some (0#8)) :
    letI : OtherOpcodeHandlers := X86Stack.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    (X86FuelPrefix.fetches 5).run before ≠ .ok () after := by
  let : OtherOpcodeHandlers := X86Stack.linkedHandlers other
  let : VectorOpcodeHandlers := vector
  intro observed
  obtain ⟨proved, run, _, _, stored, _⟩ := saves_initial_registers other vector
  have same := (EStateM.Result.ok.inj (run.symm.trans observed)).2
  rw [same, wrong] at stored
  contradiction

theorem changed_return_address_refused (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (after : State) (wrong : after.mem.get? 8233 = some (0#8)) :
    letI : OtherOpcodeHandlers := X86Stack.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    (X86FuelPrefix.fetches 5).run before ≠ .ok () after := by
  let : OtherOpcodeHandlers := X86Stack.linkedHandlers other
  let : VectorOpcodeHandlers := vector
  intro observed
  obtain ⟨proved, run, _, _, _, _, _, returned, _⟩ := saves_initial_registers other vector
  have same := (EStateM.Result.ok.inj (run.symm.trans observed)).2
  rw [same, wrong] at returned
  contradiction


theorem wrapper_fixture :
    ∃ state, ∃ prepared : Inputs state,
      (codeAt prepared 9).toInt + 10 < (2 ^ 47 : Int) ∧
      codeLoaded state (codeAt prepared 9).toInt X86Epilogue.expected ∧
      (∀ index byte, X86Epilogue.expected[index]? = some byte →
        ((address (codeAt prepared 9).toInt index).signExtend 52).toNat ∉ writes prepared.bottom) ∧
      prepared.returnAddress = (0x3000#48) ∧ prepared.bottom = (0x2000#48) ∧
      prepared.saved 4 = (0xfedcba9876543210#64) ∧ lookup state 0 = some (4#64) := by
  refine ⟨before, input, by decide, ?_, ?_, rfl, rfl, rfl, ?_⟩
  · intro index byte present
    have within : index < 10 := (List.getElem?_eq_some_iff.mp present).choose
    have member : (4105 + index, BitVec.ofNat 8 byte) ∈ cells := by
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_right
      apply List.mem_map.mpr
      refine ⟨index, List.mem_range.mpr within, ?_⟩
      simp only [present, Option.getD_some]
    have got := cell _ _ member
    interval_cases index <;> exact got
  · intro index byte present member
    have within : index < 10 := (List.getElem?_eq_some_iff.mp present).choose
    simp only [writes, X86WriteWords.written, List.mem_toFinset, List.mem_map] at member
    obtain ⟨stackByte, inside, same⟩ := member
    have bounded := List.mem_range.mp inside
    interval_cases index <;> interval_cases stackByte <;> contradiction
  · simp [before, lookup, key, cast_eq, Std.ExtDHashMap.get?_insert]
    rfl

end Controls

end Mettapedia.Machines.TIsa.X86Prologue

#print axioms Mettapedia.Machines.TIsa.X86Prologue.executes
#print axioms Mettapedia.Machines.TIsa.X86Prologue.saved_bytes
#print axioms Mettapedia.Machines.TIsa.X86Prologue.return_bytes
#print axioms Mettapedia.Machines.TIsa.X86Prologue.epilogueStackFacts
#print axioms Mettapedia.Machines.TIsa.X86Prologue.Controls.saves_initial_registers
#print axioms Mettapedia.Machines.TIsa.X86Prologue.Controls.stale_stack_word_refused
#print axioms Mettapedia.Machines.TIsa.X86Prologue.Controls.changed_return_address_refused
#print axioms Mettapedia.Machines.TIsa.X86Prologue.Controls.wrapper_fixture
