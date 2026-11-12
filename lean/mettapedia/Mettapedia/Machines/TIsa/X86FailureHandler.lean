import Mettapedia.Machines.TIsa.X86OutcomeLoad
import Mettapedia.Machines.TIsa.X86FuelPrefix
import Mettapedia.Machines.TIsa.X86CodePlacement
import Mettapedia.Machines.TIsa.Outcome

/-!
# Complete emitted failure handlers through the epilogue boundary

The twenty-eight-byte handler is the actual B8 immediate load, sign-extended
C7 status store, register return-value store and patched E9 jump. Four full
fetch/decode/execute steps establish the outcome in RAX and both eight-byte
frame fields. Exact register/byte frames preserve flags, other memory and any
caller image protected from those writes.

The proof is generic over loaded bytes, canonical code/data locations and
explicit separation. Concrete exhaustion controls overwrite old sentinels,
preserve the next frame field and refuse leaving the old return value.
Independent store and readback contracts keep composition shallow.

The public stack-restoring epilogue, OS memory installation, actual source
admission and complete emitter refinement remain separate obligations.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Mettapedia.Machines.TIsa.X86FailureHandler
open _root_.X86Registers X86RegisterRefinement X86Execution
local instance : MemoryPrimitives := X86Memory.ordinary

noncomputable abbrev linkedHandlers (other : OtherOpcodeHandlers) : OtherOpcodeHandlers :=
  X86UnconditionalJump.linked (X86FrameStore.linkedHandlers other)

theorem stores_installed (other : OtherOpcodeHandlers) :
    X86FrameStore.linkedHandlers (linkedHandlers other) = linkedHandlers other := rfl
theorem jump_installed (other : OtherOpcodeHandlers) :
    X86UnconditionalJump.linked (linkedHandlers other) = linkedHandlers other := rfl

def expected (value displacement : BitVec 32) : List Nat :=
  [0xb8, (value.extractLsb' 0 8).toNat, (value.extractLsb' 8 8).toNat,
    (value.extractLsb' 16 8).toNat, (value.extractLsb' 24 8).toNat,
    0x48, 0xc7, 0x87, 0x90, 0, 0, 0,
    (value.extractLsb' 0 8).toNat, (value.extractLsb' 8 8).toNat,
    (value.extractLsb' 16 8).toNat, (value.extractLsb' 24 8).toNat,
    0x48, 0x89, 0x87, 0x98, 0, 0, 0, 0xe9,
    (displacement.extractLsb' 0 8).toNat, (displacement.extractLsb' 8 8).toNat,
    (displacement.extractLsb' 16 8).toNat, (displacement.extractLsb' 24 8).toNat]

structure FrameFacts (state : State) where
  frame : Word
  statusAddress : BitVec 48
  resultAddress : BitVec 48
  statusUpper : statusAddress.toInt + 8 ≤ (2 ^ 47 : Int)
  resultUpper : resultAddress.toInt + 8 ≤ (2 ^ 47 : Int)
  statusEffective : frame + (0x90#32).signExtend 64 = statusAddress.signExtend 64
  resultEffective : frame + (0x98#32).signExtend 64 = resultAddress.signExtend 64
  statusAligned : statusAddress &&& (7#48) = (0#48)
  resultAligned : resultAddress &&& (7#48) = (0#48)
  visible : Vector (BitVec 16) 6
  controls : Vector (BitVec 64) 17
  flags : BitVec 32
  frameKnown : lookup state 7 = some frame
  controlsKnown : state.regs.get? .ctrs = some controls
  visibleKnown : state.regs.get? .seg_visibles = some visible
  flagsKnown : state.regs.get? .rflags = some flags
  quiet : state.regs.get? .log_register_writes = some false
  statusOutside : ∀ index < 8, X86WriteWords.physicalAddress statusAddress index ∉
    X86WriteWords.written resultAddress (List.range 8)

structure Inputs (state : State) (value : BitVec 32) extends X86LegacyFetch.Basis state, FrameFacts state where
  displacement : BitVec 32
  epilogue : BitVec 48
  upper : address.toInt + 28 < (2 ^ 47 : Int)
  jump : epilogue.toInt = address.toInt + 28 + displacement.toInt
  loaded : codeLoaded state address.toInt (expected value displacement)
  codeOutside : ∀ index byte, (expected value displacement)[index]? = some byte →
    ((X86Execution.address address.toInt index).signExtend 52).toNat ∉
      X86WriteWords.written statusAddress (List.range 8) ∪ X86WriteWords.written resultAddress (List.range 8)

def writes {state : State} {value : BitVec 32} (input : Inputs state value) : Finset Nat :=
  X86WriteWords.written input.statusAddress (List.range 8) ∪ X86WriteWords.written input.resultAddress (List.range 8)

theorem offset_int {state : State} {value : BitVec 32} (input : Inputs state value)
    (offset : Nat) (within : offset ≤ 28) :
    (address input.address.toInt offset).toInt = input.address.toInt + offset :=
  address_toInt _ (by simpa using BitVec.le_toInt input.address) input.upper offset within

theorem nested_address {state : State} {value : BitVec 32} (input : Inputs state value)
    (offset index : Nat) (within : offset ≤ 28) :
    address (address input.address.toInt offset).toInt index = address input.address.toInt (offset + index) := by
  rw [offset_int input offset within]
  simp only [address, Int.natCast_add, Int.add_assoc]

theorem code_at {before current : State} {value : BitVec 32} (input : Inputs before value)
    (frame : X86StateFrame.Frame {.rax, .rip} (writes input) before current)
    (index byte : Nat) (present : (expected value input.displacement)[index]? = some byte) :
    current.mem.get? ((address input.address.toInt index).signExtend 52).toNat = some (BitVec.ofNat 8 byte) :=
  frame.codeLoaded _ _ input.loaded input.codeOutside index byte present

def loaded (state : State) (base : Int) (value : BitVec 32) : State :=
  X86Move.putPointer (put state 0 (value.zeroExtend 64)) (address base 5)
def statusStored (state : State) {value : BitVec 32} (input : Inputs state value) : State :=
  X86Move.putPointer (X86WriteWords.storeBytes 8 (loaded state input.address.toInt value)
    input.statusAddress (value.signExtend 64)) (address input.address.toInt 16)
def resultStored (state : State) {value : BitVec 32} (input : Inputs state value) : State :=
  X86Move.putPointer (X86WriteWords.storeBytes 8 (statusStored state input)
    input.resultAddress (value.zeroExtend 64)) (address input.address.toInt 23)
def finished (state : State) {value : BitVec 32} (input : Inputs state value) : State :=
  X86Move.putPointer (resultStored state input) input.epilogue

theorem loaded_frame (state : State) {value : BitVec 32} (input : Inputs state value) :
    X86StateFrame.Frame {.rax, .rip} (writes input) state (loaded state input.address.toInt value) :=
  (X86StateFrame.registerOnly (X86OutcomeLoad.result_frame state value _)).mono
    (Finset.Subset.refl _) (Finset.empty_subset _)

theorem status_step_frame (state : State) {value : BitVec 32} (input : Inputs state value) :
    X86StateFrame.Frame {.rip} (X86WriteWords.written input.statusAddress (List.range 8))
      (loaded state input.address.toInt value) (statusStored state input) := X86FrameStore.result_frame _ _ _ _

theorem status_frame (state : State) {value : BitVec 32} (input : Inputs state value) :
    X86StateFrame.Frame {.rax, .rip} (writes input) state (statusStored state input) := by
  apply ((loaded_frame state input).trans (status_step_frame state input)).mono
  · simp
  · exact Finset.union_subset (Finset.Subset.refl _) Finset.subset_union_left

theorem result_step_frame (state : State) {value : BitVec 32} (input : Inputs state value) :
    X86StateFrame.Frame {.rip} (X86WriteWords.written input.resultAddress (List.range 8))
      (statusStored state input) (resultStored state input) := X86FrameStore.result_frame _ _ _ _

theorem result_frame (state : State) {value : BitVec 32} (input : Inputs state value) :
    X86StateFrame.Frame {.rax, .rip} (writes input) state (resultStored state input) := by
  apply ((status_frame state input).trans (result_step_frame state input)).mono
  · simp
  · exact Finset.union_subset (Finset.Subset.refl _) Finset.subset_union_right

theorem finished_frame (state : State) {value : BitVec 32} (input : Inputs state value) :
    X86StateFrame.Frame {.rax, .rip} (writes input) state (finished state input) := by
  simpa [finished] using (result_frame state input).trans (X86StateFrame.registerOnly (pointer_frame _ input.epilogue))

theorem load_executes (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (value : BitVec 32) (input : Inputs state value) :
    letI : OtherOpcodeHandlers := linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    Step state (loaded state input.address.toInt value) := by
  have run := X86OutcomeLoad.fetched_eax (linkedHandlers other) vector state input.toBasis
    (address input.address.toInt 5) value
    (by rw [offset_int input 5 (by decide)]; have := input.step1; omega) input.quiet
    (by simpa [address, BitVec.ofInt_toInt] using input.loaded 0 184 rfl) (by
      intro index within
      have whereByte : address input.opcodeAddress.toInt index = address input.address.toInt (1 + index) := by
        rw [show input.opcodeAddress.toInt = input.address.toInt + 1 by have := input.step1; omega]
        simp only [address, Int.natCast_add, Int.natCast_one, Int.add_assoc]
      rw [whereByte]
      have got := input.loaded (1 + index) (value.extractLsb' (8 * index) 8).toNat
        (by interval_cases index <;> rfl)
      simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using got)
  simpa only [stores_installed, Step, loaded] using run

theorem store_status_executes (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (value : BitVec 32) (input : Inputs state value) :
    letI : OtherOpcodeHandlers := linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    Step (loaded state input.address.toInt value) (statusStored state input) := by
  let current := loaded state input.address.toInt value
  have frame := loaded_frame state input
  let site := X86StateFrame.rebase state current input.toBasis frame (by decide)
    (extent := 28) input.upper 5 (by decide) (X86FuelPrefix.pointer_rip _ _)
  have run := X86FrameStore.fetched_immediate (linkedHandlers other) vector current site
    (address input.address.toInt 12) (address input.address.toInt 16) input.statusAddress input.visible input.controls
    input.frame input.flags (0x90#32) value
    (by dsimp only [site, X86StateFrame.rebase]; rw [offset_int input 8 (by decide), offset_int input 12 (by decide)]; omega)
    (by rw [offset_int input 12 (by decide), offset_int input 16 (by decide)]; omega)
    input.statusUpper ((frame.lookup 7 (by decide)).trans input.frameKnown)
    ((frame.registers .ctrs (by decide)).trans input.controlsKnown)
    ((frame.registers .rflags (by decide)).trans input.flagsKnown)
    ((frame.registers .seg_visibles (by decide)).trans input.visibleKnown)
    ((frame.registers .log_register_writes (by decide)).trans input.quiet)
    input.statusEffective input.statusAligned
    (code_at input frame 5 72 rfl) (code_at input frame 6 199 rfl) (code_at input frame 7 135 rfl)
    (by
      intro index within
      dsimp only [site, X86StateFrame.rebase]
      rw [nested_address input 8 index (by decide)]
      interval_cases index <;> exact code_at input frame _ _ rfl)
    (by
      intro index within
      rw [nested_address input 12 index (by decide)]
      have got := code_at input frame (12 + index) (value.extractLsb' (8 * index) 8).toNat
        (by interval_cases index <;> rfl)
      simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using got)
  simpa only [stores_installed, Step, current, statusStored] using run

theorem store_result_executes (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (value : BitVec 32) (input : Inputs state value) :
    letI : OtherOpcodeHandlers := linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    Step (statusStored state input) (resultStored state input) := by
  let current := statusStored state input
  have frame := status_frame state input
  let site := X86StateFrame.rebase state current input.toBasis frame (by decide)
    (extent := 28) input.upper 16 (by decide) (X86FuelPrefix.pointer_rip _ _)
  have preservedRax := (status_step_frame state input).lookup 0 (by decide)
  have rax : lookup current 0 = some (value.zeroExtend 64) := by
    rw [preservedRax]
    exact (X86Move.lookup_putPointer (put state 0 (value.zeroExtend 64))
      (address input.address.toInt 5) 0).trans (lookup_put_same state 0 (value.zeroExtend 64))
  have run := X86FrameStore.fetched_register (linkedHandlers other) vector current 0 site
    (address input.address.toInt 23) input.resultAddress input.visible input.controls input.frame
    (value.zeroExtend 64) input.flags (0x98#32)
    (by dsimp only [site, X86StateFrame.rebase]; rw [offset_int input 19 (by decide), offset_int input 23 (by decide)]; omega)
    input.resultUpper ((frame.lookup 7 (by decide)).trans input.frameKnown) rax
    ((frame.registers .ctrs (by decide)).trans input.controlsKnown)
    ((frame.registers .rflags (by decide)).trans input.flagsKnown)
    ((frame.registers .seg_visibles (by decide)).trans input.visibleKnown)
    ((frame.registers .log_register_writes (by decide)).trans input.quiet)
    input.resultEffective input.resultAligned
    (code_at input frame 16 72 rfl) (code_at input frame 17 137 rfl) (code_at input frame 18 135 rfl)
    (by
      intro index within
      dsimp only [site, X86StateFrame.rebase]
      rw [nested_address input 19 index (by decide)]
      interval_cases index <;> exact code_at input frame _ _ rfl)
  simpa only [Step, current, resultStored] using run

theorem jump_executes (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (value : BitVec 32) (input : Inputs state value) :
    letI : OtherOpcodeHandlers := linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    Step (resultStored state input) (finished state input) := by
  let current := resultStored state input
  have frame := result_frame state input
  have run := X86UnconditionalJump.fetched_jump (linkedHandlers other) vector current
    (address input.address.toInt 23) (address input.address.toInt 24) (address input.address.toInt 28)
    input.epilogue input.control input.attributes input.displacement
    (by rw [offset_int input 23 (by decide), offset_int input 24 (by decide)]; omega)
    (by rw [offset_int input 24 (by decide), offset_int input 28 (by decide)]; omega)
    (by rw [offset_int input 28 (by decide)]; exact input.jump)
    ((frame.registers .ms_reg (by decide)).trans input.status)
    ((frame.registers .fault_reg (by decide)).trans input.fault)
    ((frame.registers .msrs (by decide)).trans input.msrs)
    ((frame.registers .seg_hidden_attrs (by decide)).trans input.segments)
    input.longMode input.codeMode ((frame.registers .app_view (by decide)).trans input.application)
    (X86FuelPrefix.pointer_rip _ _) ((frame.registers .log_register_writes (by decide)).trans input.quiet)
    (code_at input frame 23 233 rfl) (by
      intro index within
      rw [nested_address input 24 index (by decide)]
      have got := code_at input frame (24 + index) (input.displacement.extractLsb' (8 * index) 8).toNat
        (by interval_cases index <;> rfl)
      simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using got)
  simpa only [jump_installed, Step, current, finished] using run

theorem executes (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (value : BitVec 32) (input : Inputs state value) :
    letI : OtherOpcodeHandlers := linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    (X86FuelPrefix.fetches 4).run state = .ok () (finished state input) := by
  let : OtherOpcodeHandlers := linkedHandlers other
  let : VectorOpcodeHandlers := vector
  have first := X86FuelPrefix.fetches_one state _ (load_executes other vector state value input)
  have second := X86FuelPrefix.fetches_one _ _ (store_status_executes other vector state value input)
  have third := X86FuelPrefix.fetches_one _ _ (store_result_executes other vector state value input)
  have fourth := X86FuelPrefix.fetches_one _ _ (jump_executes other vector state value input)
  exact X86FuelPrefix.fetches_then 1 3 state _ _ first
    (X86FuelPrefix.fetches_then 1 2 _ _ _ second (X86FuelPrefix.fetches_then 1 1 _ _ _ third fourth))

structure Result (state : State) {value : BitVec 32} (input : Inputs state value) (after : State) : Prop where
  pointer : after.regs.get? .rip = some (input.epilogue.signExtend 64)
  rax : lookup after 0 = some (value.zeroExtend 64)
  status : ∀ index < 8, after.mem.get? (X86WriteWords.physicalAddress input.statusAddress index) =
    some ((value.signExtend 64).extractLsb' (8 * index) 8)
  result : ∀ index < 8, after.mem.get? (X86WriteWords.physicalAddress input.resultAddress index) =
    some ((value.zeroExtend 64).extractLsb' (8 * index) 8)
  frame : X86StateFrame.Frame {.rax, .rip} (writes input) state after
  flags : after.regs.get? .rflags = some input.flags

theorem finished_rax (state : State) (value : BitVec 32) (input : Inputs state value) :
    lookup (finished state input) 0 = some (value.zeroExtend 64) := by
    rw [finished, X86Move.lookup_putPointer, (result_step_frame state input).lookup 0 (by decide),
      (status_step_frame state input).lookup 0 (by decide)]
    exact (X86Move.lookup_putPointer (put state 0 (value.zeroExtend 64))
      (address input.address.toInt 5) 0).trans (lookup_put_same state 0 (value.zeroExtend 64))

theorem finished_memory (state : State) {value : BitVec 32} (input : Inputs state value) :
    (finished state input).mem = (resultStored state input).mem :=
  (pointer_frame (resultStored state input) input.epilogue).memory

theorem status_memory (state : State) {value : BitVec 32} (input : Inputs state value) :
    (statusStored state input).mem =
      (X86WriteWords.storeBytes 8 (loaded state input.address.toInt value) input.statusAddress (value.signExtend 64)).mem :=
  (pointer_frame (X86WriteWords.storeBytes 8 (loaded state input.address.toInt value) input.statusAddress
    (value.signExtend 64)) (address input.address.toInt 16)).memory

theorem result_memory (state : State) {value : BitVec 32} (input : Inputs state value) :
    (resultStored state input).mem =
      (X86WriteWords.storeBytes 8 (statusStored state input) input.resultAddress (value.zeroExtend 64)).mem :=
  (pointer_frame (X86WriteWords.storeBytes 8 (statusStored state input) input.resultAddress
    (value.zeroExtend 64)) (address input.address.toInt 23)).memory
theorem finished_status (state : State) (value : BitVec 32) (input : Inputs state value)
    (index : Nat) (within : index < 8) :
    (finished state input).mem.get? (X86WriteWords.physicalAddress input.statusAddress index) =
      some ((value.signExtend 64).extractLsb' (8 * index) 8) := by
    rw [finished_memory, result_memory]
    rw [(X86WriteWords.storeBytes_frame 8 (statusStored state input) input.resultAddress (value.zeroExtend 64)).memory
      _ (input.statusOutside index within)]
    rw [status_memory]
    exact X86WriteWords.store_word_byte (loaded state input.address.toInt value) input.statusAddress
      (value.signExtend 64) input.statusUpper index within
theorem finished_return (state : State) (value : BitVec 32) (input : Inputs state value)
    (index : Nat) (within : index < 8) :
    (finished state input).mem.get? (X86WriteWords.physicalAddress input.resultAddress index) =
      some ((value.zeroExtend 64).extractLsb' (8 * index) 8) := by
    rw [finished_memory, result_memory]
    exact X86WriteWords.store_word_byte (statusStored state input) input.resultAddress
      (value.zeroExtend 64) input.resultUpper index within
theorem finished_result (state : State) (value : BitVec 32) (input : Inputs state value) :
    Result state input (finished state input) :=
  ⟨X86FuelPrefix.pointer_rip _ _, finished_rax state value input, finished_status state value input,
    finished_return state value input, finished_frame state input,
    ((finished_frame state input).registers .rflags (by decide)).trans input.flagsKnown⟩

theorem any_run_refines (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (value : BitVec 32) (input : Inputs state value) (after : State) :
    letI : OtherOpcodeHandlers := linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    (X86FuelPrefix.fetches 4).run state = .ok () after → Result state input after := by
  intro observed
  have same := (EStateM.Result.ok.inj ((executes other vector state value input).symm.trans observed)).2
  simpa only [← same] using finished_result state value input

theorem Result.image_preserved {state after : State} {value : BitVec 32} {input : Inputs state value}
    (correct : Result state input after) (base : Int) (view : NativeImage.View)
    (placed : X86CodePlacement.Placed state base view)
    (outside : ∀ index byte, view.read index = some byte →
      ((address base index).signExtend 52).toNat ∉ writes input) :
    X86CodePlacement.Placed after base view := placed.preserved base view correct.frame outside

theorem outcome_encoding (outcome : ExitStatus) :
    ((outcome.word.extractLsb' 0 32).zeroExtend 64 = outcome.word) ∧
      ((outcome.word.extractLsb' 0 32).signExtend 64 = outcome.word) := by
  cases outcome <;> decide

theorem outcome_words (state after : State) (outcome : ExitStatus)
    (input : Inputs state (outcome.word.extractLsb' 0 32)) (correct : Result state input after) :
    lookup after 0 = some outcome.word ∧
      (∀ index < 8, after.mem.get? (X86WriteWords.physicalAddress input.statusAddress index) =
        some (outcome.word.extractLsb' (8 * index) 8)) ∧
      (∀ index < 8, after.mem.get? (X86WriteWords.physicalAddress input.resultAddress index) =
        some (outcome.word.extractLsb' (8 * index) 8)) := by
  obtain ⟨unsigned, signed⟩ := outcome_encoding outcome
  exact ⟨by simpa only [unsigned] using correct.rax,
    by simpa only [signed] using correct.status, by simpa only [unsigned] using correct.result⟩

namespace Controls
private def modeControl : Vector (BitVec 64) 7 :=
  Vector.ofFn (fun index => if index.val = 0 then (0x400#64) else (0#64))
private def attributes : Vector (BitVec 16) 6 :=
  Vector.ofFn (fun index => if index.val = 1 then (0x200#16) else (0#16))
private def visible : Vector (BitVec 16) 6 := Vector.replicate 6 (0#16)
private def controls : Vector (BitVec 64) 17 := Vector.replicate 17 (0#64)
private def cells : List (Nat × BitVec 8) :=
  (List.range 28).map (fun index => (4096 + index, BitVec.ofNat 8 (((expected (4#32) (0#32))[index]?).getD 0))) ++
    [(8336, 99#8), (8344, 77#8), (8352, 42#8)]
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
  let registers := registers.insert .rdi (0x2000#64)
  let registers := registers.insert .rax (999#64)
  let registers := registers.insert .ctrs controls
  let registers := registers.insert .rflags (0#32)
  let registers := registers.insert .seg_visibles visible
  let registers := registers.insert .log_register_writes false
  ⟨registers, (), Std.ExtHashMap.ofList cells, (), 0, #[]⟩
private theorem cell (key : Nat) (byte : BitVec 8) (present : (key, byte) ∈ cells) :
    before.mem.get? key = some byte := Std.ExtHashMap.getElem?_ofList_of_mem (by simp) distinct present
private def input : Inputs before (4#32) where
  address := 0x1000#48
  opcodeAddress := 0x1001#48
  modrmAddress := 0x1002#48
  next := 0x1003#48
  control := modeControl
  attributes := attributes
  step1 := by decide
  step2 := by decide
  step3 := by decide
  status := by simp [before, Std.ExtDHashMap.get?_insert]
  fault := by simp [before, Std.ExtDHashMap.get?_insert]
  msrs := by simp [before, Std.ExtDHashMap.get?_insert]
  segments := by simp [before, Std.ExtDHashMap.get?_insert]
  longMode := by decide
  codeMode := by decide
  application := by simp [before, Std.ExtDHashMap.get?_insert]
  rip := by simp [before, Std.ExtDHashMap.get?_insert]
  frame := 0x2000#64
  statusAddress := 0x2090#48
  resultAddress := 0x2098#48
  statusUpper := by decide
  resultUpper := by decide
  statusEffective := by decide
  resultEffective := by decide
  statusAligned := by decide
  resultAligned := by decide
  visible := visible
  controls := controls
  flags := 0#32
  frameKnown := by simp [before, lookup, key, cast_eq, Std.ExtDHashMap.get?_insert]; rfl
  controlsKnown := by simp [before, Std.ExtDHashMap.get?_insert]
  visibleKnown := by simp [before, Std.ExtDHashMap.get?_insert]
  flagsKnown := by simp [before, Std.ExtDHashMap.get?_insert]
  quiet := by simp [before]
  displacement := 0#32
  epilogue := 0x101c#48
  upper := by decide
  jump := by decide
  loaded := by
    intro index byte present
    have within : index < 28 := (List.getElem?_eq_some_iff.mp present).choose
    have member : (4096 + index, BitVec.ofNat 8 byte) ∈ cells := by
      apply List.mem_append_left
      apply List.mem_map.mpr
      refine ⟨index, List.mem_range.mpr within, ?_⟩
      simp only [present, Option.getD_some]
    have got := cell (4096 + index) (BitVec.ofNat 8 byte) member
    interval_cases index <;> exact got
  codeOutside := by
    intro index byte present
    have within : index < 28 := (List.getElem?_eq_some_iff.mp present).choose
    interval_cases index <;> decide
  statusOutside := by
    intro index within
    interval_cases index <;> decide

theorem exhausted_publishes (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 4).run before = .ok () after ∧
      lookup after 0 = some (4#64) ∧ after.mem.get? 8336 = some (4#8) ∧
      after.mem.get? 8344 = some (4#8) ∧ after.mem.get? 8352 = some (42#8) := by
  let after := finished before input
  have correct := finished_result before (4#32) input
  refine ⟨after, executes other vector before (4#32) input, correct.rax, correct.status 0 (by decide),
    correct.result 0 (by decide), ?_⟩
  rw [correct.frame.memory 8352 (by decide)]
  exact cell 8352 (42#8) (by decide)

theorem unchanged_return_refused (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers) (after : State)
    (wrong : after.mem.get? 8344 = some (77#8)) :
    letI : OtherOpcodeHandlers := linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    (X86FuelPrefix.fetches 4).run before ≠ .ok () after := by
  intro observed
  obtain ⟨proved, run, _, _, value, _⟩ := exhausted_publishes other vector
  have same := (EStateM.Result.ok.inj (run.symm.trans observed)).2
  rw [same, wrong] at value
  contradiction

end Controls
end Mettapedia.Machines.TIsa.X86FailureHandler

#print axioms Mettapedia.Machines.TIsa.X86FailureHandler.executes
#print axioms Mettapedia.Machines.TIsa.X86FailureHandler.finished_result
#print axioms Mettapedia.Machines.TIsa.X86FailureHandler.any_run_refines
#print axioms Mettapedia.Machines.TIsa.X86FailureHandler.Result.image_preserved
#print axioms Mettapedia.Machines.TIsa.X86FailureHandler.outcome_words
#print axioms Mettapedia.Machines.TIsa.X86FailureHandler.Controls.exhausted_publishes
#print axioms Mettapedia.Machines.TIsa.X86FailureHandler.Controls.unchanged_return_refused

namespace Mettapedia.Machines.TIsa.X86FailureHandler.RegisterPath
open _root_.X86Registers X86RegisterRefinement X86Execution
local instance : MemoryPrimitives := X86Memory.ordinary

abbrev linkedHandlers (other : OtherOpcodeHandlers) : OtherOpcodeHandlers :=
  X86FrameStore.linkedHandlers other

theorem stores_installed (other : OtherOpcodeHandlers) :
    X86FrameStore.linkedHandlers (linkedHandlers other) = linkedHandlers other := rfl

def expected (value : BitVec 32) : List Nat :=
  [0xb8, (value.extractLsb' 0 8).toNat, (value.extractLsb' 8 8).toNat,
    (value.extractLsb' 16 8).toNat, (value.extractLsb' 24 8).toNat,
    0x48,0x89,0x87,0x90,0,0,0, 0x48,0x89,0x87,0x98,0,0,0]

structure Inputs (state : State) (value : BitVec 32) extends
    X86LegacyFetch.Basis state, X86FailureHandler.FrameFacts state where
  upper : address.toInt + 19 < (2 ^ 47 : Int)
  loaded : codeLoaded state address.toInt (expected value)
  codeOutside : ∀ index byte, (expected value)[index]? = some byte →
    ((X86Execution.address address.toInt index).signExtend 52).toNat ∉
      X86WriteWords.written statusAddress (List.range 8) ∪ X86WriteWords.written resultAddress (List.range 8)

def writes {state : State} {value : BitVec 32} (input : Inputs state value) : Finset Nat :=
  X86WriteWords.written input.statusAddress (List.range 8) ∪
    X86WriteWords.written input.resultAddress (List.range 8)

theorem offset_int {state : State} {value : BitVec 32} (input : Inputs state value)
    (offset : Nat) (within : offset ≤ 19) :
    (address input.address.toInt offset).toInt = input.address.toInt + offset :=
  address_toInt _ (by simpa using BitVec.le_toInt input.address) input.upper offset within

theorem nested_address {state : State} {value : BitVec 32} (input : Inputs state value)
    (offset index : Nat) (within : offset ≤ 19) :
    address (address input.address.toInt offset).toInt index = address input.address.toInt (offset + index) := by
  rw [offset_int input offset within]
  simp only [address, Int.natCast_add, Int.add_assoc]

theorem code_at {before current : State} {value : BitVec 32} (input : Inputs before value)
    (frame : X86StateFrame.Frame {.rax, .rip} (writes input) before current)
    (index byte : Nat) (present : (expected value)[index]? = some byte) :
    current.mem.get? ((address input.address.toInt index).signExtend 52).toNat = some (BitVec.ofNat 8 byte) :=
  frame.codeLoaded _ _ input.loaded input.codeOutside index byte present

def loaded (state : State) (base : Int) (value : BitVec 32) : State :=
  X86FailureHandler.loaded state base value

def statusStored (state : State) {value : BitVec 32} (input : Inputs state value) : State :=
  X86Move.putPointer (X86WriteWords.storeBytes 8 (loaded state input.address.toInt value)
    input.statusAddress (value.zeroExtend 64)) (address input.address.toInt 12)

def finished (state : State) {value : BitVec 32} (input : Inputs state value) : State :=
  X86Move.putPointer (X86WriteWords.storeBytes 8 (statusStored state input)
    input.resultAddress (value.zeroExtend 64)) (address input.address.toInt 19)

theorem loaded_frame (state : State) {value : BitVec 32} (input : Inputs state value) :
    X86StateFrame.Frame {.rax, .rip} (writes input) state (loaded state input.address.toInt value) :=
  (X86StateFrame.registerOnly (X86OutcomeLoad.result_frame state value _)).mono
    (Finset.Subset.refl _) (Finset.empty_subset _)

theorem status_step_frame (state : State) {value : BitVec 32} (input : Inputs state value) :
    X86StateFrame.Frame {.rip} (X86WriteWords.written input.statusAddress (List.range 8))
      (loaded state input.address.toInt value) (statusStored state input) :=
  X86FrameStore.result_frame _ _ _ _

theorem status_frame (state : State) {value : BitVec 32} (input : Inputs state value) :
    X86StateFrame.Frame {.rax, .rip} (writes input) state (statusStored state input) := by
  apply ((loaded_frame state input).trans (status_step_frame state input)).mono
  · simp
  · exact Finset.union_subset (Finset.Subset.refl _) Finset.subset_union_left

theorem result_step_frame (state : State) {value : BitVec 32} (input : Inputs state value) :
    X86StateFrame.Frame {.rip} (X86WriteWords.written input.resultAddress (List.range 8))
      (statusStored state input) (finished state input) :=
  X86FrameStore.result_frame _ _ _ _

theorem finished_frame (state : State) {value : BitVec 32} (input : Inputs state value) :
    X86StateFrame.Frame {.rax, .rip} (writes input) state (finished state input) := by
  apply ((status_frame state input).trans (result_step_frame state input)).mono
  · simp
  · exact Finset.union_subset (Finset.Subset.refl _) Finset.subset_union_right

theorem load_executes (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (value : BitVec 32) (input : Inputs state value) :
    letI : OtherOpcodeHandlers := linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    Step state (loaded state input.address.toInt value) := by
  have run := X86OutcomeLoad.fetched_eax (linkedHandlers other) vector state input.toBasis
    (address input.address.toInt 5) value
    (by rw [offset_int input 5 (by decide)]; have := input.step1; omega) input.quiet
    (by simpa [address, BitVec.ofInt_toInt] using input.loaded 0 184 rfl) (by
      intro index within
      have whereByte : address input.opcodeAddress.toInt index = address input.address.toInt (1 + index) := by
        rw [show input.opcodeAddress.toInt = input.address.toInt + 1 by have := input.step1; omega]
        simp only [address, Int.natCast_add, Int.natCast_one, Int.add_assoc]
      rw [whereByte]
      have got := input.loaded (1 + index) (value.extractLsb' (8 * index) 8).toNat
        (by interval_cases index <;> rfl)
      simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using got)
  simpa only [stores_installed, Step, loaded, X86FailureHandler.loaded] using run

theorem store_status_executes (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (value : BitVec 32) (input : Inputs state value) :
    letI : OtherOpcodeHandlers := linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    Step (loaded state input.address.toInt value) (statusStored state input) := by
  let current := loaded state input.address.toInt value
  have frame := loaded_frame state input
  let site := X86StateFrame.rebase state current input.toBasis frame (by decide)
    (extent := 19) input.upper 5 (by decide) (X86FuelPrefix.pointer_rip _ _)
  have rax : lookup current 0 = some (value.zeroExtend 64) :=
    (X86Move.lookup_putPointer (put state 0 (value.zeroExtend 64))
      (address input.address.toInt 5) 0).trans (lookup_put_same state 0 (value.zeroExtend 64))
  have run := X86FrameStore.fetched_register (linkedHandlers other) vector current 0 site
    (address input.address.toInt 12) input.statusAddress input.visible input.controls input.frame
    (value.zeroExtend 64) input.flags (0x90#32)
    (by dsimp only [site, X86StateFrame.rebase]; rw [offset_int input 8 (by decide), offset_int input 12 (by decide)]; omega)
    input.statusUpper ((frame.lookup 7 (by decide)).trans input.frameKnown) rax
    ((frame.registers .ctrs (by decide)).trans input.controlsKnown)
    ((frame.registers .rflags (by decide)).trans input.flagsKnown)
    ((frame.registers .seg_visibles (by decide)).trans input.visibleKnown)
    ((frame.registers .log_register_writes (by decide)).trans input.quiet)
    input.statusEffective input.statusAligned
    (code_at input frame 5 72 rfl) (code_at input frame 6 137 rfl) (code_at input frame 7 135 rfl)
    (by
      intro index within
      dsimp only [site, X86StateFrame.rebase]
      rw [nested_address input 8 index (by decide)]
      interval_cases index <;> exact code_at input frame _ _ rfl)
  simpa only [Step, current, statusStored] using run

theorem store_result_executes (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (value : BitVec 32) (input : Inputs state value) :
    letI : OtherOpcodeHandlers := linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    Step (statusStored state input) (finished state input) := by
  let current := statusStored state input
  have frame := status_frame state input
  let site := X86StateFrame.rebase state current input.toBasis frame (by decide)
    (extent := 19) input.upper 12 (by decide) (X86FuelPrefix.pointer_rip _ _)
  have rax : lookup current 0 = some (value.zeroExtend 64) := by
    rw [(status_step_frame state input).lookup 0 (by decide)]
    exact (X86Move.lookup_putPointer (put state 0 (value.zeroExtend 64))
      (address input.address.toInt 5) 0).trans (lookup_put_same state 0 (value.zeroExtend 64))
  have run := X86FrameStore.fetched_register (linkedHandlers other) vector current 0 site
    (address input.address.toInt 19) input.resultAddress input.visible input.controls input.frame
    (value.zeroExtend 64) input.flags (0x98#32)
    (by dsimp only [site, X86StateFrame.rebase]; rw [offset_int input 15 (by decide), offset_int input 19 (by decide)]; omega)
    input.resultUpper ((frame.lookup 7 (by decide)).trans input.frameKnown) rax
    ((frame.registers .ctrs (by decide)).trans input.controlsKnown)
    ((frame.registers .rflags (by decide)).trans input.flagsKnown)
    ((frame.registers .seg_visibles (by decide)).trans input.visibleKnown)
    ((frame.registers .log_register_writes (by decide)).trans input.quiet)
    input.resultEffective input.resultAligned
    (code_at input frame 12 72 rfl) (code_at input frame 13 137 rfl) (code_at input frame 14 135 rfl)
    (by
      intro index within
      dsimp only [site, X86StateFrame.rebase]
      rw [nested_address input 15 index (by decide)]
      interval_cases index <;> exact code_at input frame _ _ rfl)
  simpa only [Step, current, finished] using run

theorem executes (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (value : BitVec 32) (input : Inputs state value) :
    letI : OtherOpcodeHandlers := linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    (X86FuelPrefix.fetches 3).run state = .ok () (finished state input) := by
  let : OtherOpcodeHandlers := linkedHandlers other
  let : VectorOpcodeHandlers := vector
  exact X86FuelPrefix.fetches_cons 2 state _ _ (load_executes other vector state value input)
    (X86FuelPrefix.fetches_cons 1 _ _ _ (store_status_executes other vector state value input)
      (X86FuelPrefix.fetches_one _ _ (store_result_executes other vector state value input)))

theorem status_memory_map (state : State) {value : BitVec 32} (input : Inputs state value) :
    (statusStored state input).mem =
      (X86WriteWords.storeBytes 8 (loaded state input.address.toInt value)
        input.statusAddress (value.zeroExtend 64)).mem :=
  (pointer_frame (X86WriteWords.storeBytes 8 (loaded state input.address.toInt value)
    input.statusAddress (value.zeroExtend 64)) (address input.address.toInt 12)).memory

theorem result_memory_map (state : State) {value : BitVec 32} (input : Inputs state value) :
    (finished state input).mem =
      (X86WriteWords.storeBytes 8 (statusStored state input) input.resultAddress (value.zeroExtend 64)).mem :=
  (pointer_frame (X86WriteWords.storeBytes 8 (statusStored state input)
    input.resultAddress (value.zeroExtend 64)) (address input.address.toInt 19)).memory

theorem finished_status (state : State) (value : BitVec 32) (input : Inputs state value) (index : Nat)
    (within : index < 8) :
    (finished state input).mem.get? (X86WriteWords.physicalAddress input.statusAddress index) =
      some ((value.zeroExtend 64).extractLsb' (8 * index) 8) := by
  rw [(result_step_frame state input).memory _ (input.statusOutside index within)]
  rw [status_memory_map]
  exact X86WriteWords.store_word_byte _ _ _ input.statusUpper index within

theorem finished_return (state : State) (value : BitVec 32) (input : Inputs state value) (index : Nat)
    (within : index < 8) :
    (finished state input).mem.get? (X86WriteWords.physicalAddress input.resultAddress index) =
      some ((value.zeroExtend 64).extractLsb' (8 * index) 8) := by
  rw [result_memory_map]
  exact X86WriteWords.store_word_byte _ _ _ input.resultUpper index within

theorem finished_rax (state : State) (value : BitVec 32) (input : Inputs state value) :
    lookup (finished state input) 0 = some (value.zeroExtend 64) := by
  rw [(result_step_frame state input).lookup 0 (by decide), (status_step_frame state input).lookup 0 (by decide)]
  exact (X86Move.lookup_putPointer (put state 0 (value.zeroExtend 64))
    (address input.address.toInt 5) 0).trans (lookup_put_same state 0 (value.zeroExtend 64))

theorem code_preserved (state : State) (value : BitVec 32) (input : Inputs state value) :
    codeLoaded (finished state input) input.address.toInt (expected value) :=
  (finished_frame state input).codeLoaded _ _ input.loaded input.codeOutside

structure Result (state : State) {value : BitVec 32} (input : Inputs state value) (after : State) : Prop where
  pointer : after.regs.get? .rip = some ((address input.address.toInt 19).signExtend 64)
  rax : lookup after 0 = some (value.zeroExtend 64)
  status : ∀ index < 8, after.mem.get? (X86WriteWords.physicalAddress input.statusAddress index) =
    some ((value.zeroExtend 64).extractLsb' (8 * index) 8)
  result : ∀ index < 8, after.mem.get? (X86WriteWords.physicalAddress input.resultAddress index) =
    some ((value.zeroExtend 64).extractLsb' (8 * index) 8)
  frame : X86StateFrame.Frame {.rax, .rip} (writes input) state after
  flags : after.regs.get? .rflags = some input.flags

theorem finished_result (state : State) (value : BitVec 32) (input : Inputs state value) :
    Result state input (finished state input) :=
  ⟨X86FuelPrefix.pointer_rip _ _, finished_rax state value input, finished_status state value input,
    finished_return state value input, finished_frame state input,
    ((finished_frame state input).registers .rflags (by decide)).trans input.flagsKnown⟩

theorem any_run_refines (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (value : BitVec 32) (input : Inputs state value) (after : State) :
    letI : OtherOpcodeHandlers := linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    (X86FuelPrefix.fetches 3).run state = .ok () after → Result state input after := by
  let : OtherOpcodeHandlers := linkedHandlers other
  let : VectorOpcodeHandlers := vector
  intro observed
  have same := (EStateM.Result.ok.inj ((executes other vector state value input).symm.trans observed)).2
  subst after
  exact finished_result state value input

end Mettapedia.Machines.TIsa.X86FailureHandler.RegisterPath

#print axioms Mettapedia.Machines.TIsa.X86FailureHandler.RegisterPath.executes
#print axioms Mettapedia.Machines.TIsa.X86FailureHandler.RegisterPath.finished_status
#print axioms Mettapedia.Machines.TIsa.X86FailureHandler.RegisterPath.finished_return
#print axioms Mettapedia.Machines.TIsa.X86FailureHandler.RegisterPath.finished_rax
#print axioms Mettapedia.Machines.TIsa.X86FailureHandler.RegisterPath.code_preserved
#print axioms Mettapedia.Machines.TIsa.X86FailureHandler.RegisterPath.finished_result
#print axioms Mettapedia.Machines.TIsa.X86FailureHandler.RegisterPath.any_run_refines
