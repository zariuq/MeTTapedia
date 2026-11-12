import Mettapedia.Machines.TIsa.X86FailureHandler

/-!
# Successful p1 return through the epilogue boundary

The emitted block moves a full-width source register to RAX, stores success
and the full result in the frame, and takes a signed relative jump to the
epilogue. Four fetched steps of the original instruction semantics establish
its value, byte footprint, unchanged flags and preservation of loaded code.
The source register, canonical placement and patched destination are parameters.
The public stack-restoring epilogue and complete call remain separate.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Mettapedia.Machines.TIsa.X86ReturnPath
open _root_.X86Registers X86RegisterRefinement X86Execution
local instance : MemoryPrimitives := X86Memory.ordinary

noncomputable abbrev linkedHandlers (other : OtherOpcodeHandlers) : OtherOpcodeHandlers :=
  X86FailureHandler.linkedHandlers other

def expected (source : Fin 16) (displacement : BitVec 32) : List Nat :=
  [ (X86RegisterEncoding.rex true source 0).toNat, 0x89,
    (X86RegisterEncoding.modRM source 0).toNat,
    0x48,0xc7,0x87,0x90,0,0,0, 1,0,0,0,
    0x48,0x89,0x87,0x98,0,0,0, 0xe9] ++
    (List.range 4).map (fun index => (displacement.extractLsb' (8 * index) 8).toNat)

structure Inputs (state : State) (source : Fin 16) (value : Word) extends
    X86LegacyFetch.Basis state, X86FailureHandler.FrameFacts state where
  sourceKnown : lookup state source = some value
  displacement : BitVec 32
  epilogue : BitVec 48
  upper : address.toInt + 26 < (2 ^ 47 : Int)
  jump : epilogue.toInt = address.toInt + 26 + displacement.toInt
  loaded : codeLoaded state address.toInt (expected source displacement)
  codeOutside : ∀ index byte, (expected source displacement)[index]? = some byte →
    ((X86Execution.address address.toInt index).signExtend 52).toNat ∉
      X86WriteWords.written statusAddress (List.range 8) ∪ X86WriteWords.written resultAddress (List.range 8)

def writes {state : State} {source : Fin 16} {value : Word} (input : Inputs state source value) : Finset Nat :=
  X86WriteWords.written input.statusAddress (List.range 8) ∪ X86WriteWords.written input.resultAddress (List.range 8)

theorem offset_int {state : State} {source : Fin 16} {value : Word} (input : Inputs state source value)
    (offset : Nat) (within : offset ≤ 26) :
    (address input.address.toInt offset).toInt = input.address.toInt + offset :=
  address_toInt _ (by simpa using BitVec.le_toInt input.address) input.upper offset within

theorem nested_address {state : State} {source : Fin 16} {value : Word} (input : Inputs state source value)
    (offset index : Nat) (within : offset ≤ 26) :
    address (address input.address.toInt offset).toInt index = address input.address.toInt (offset + index) := by
  rw [offset_int input offset within]
  simp only [address, Int.natCast_add, Int.add_assoc]

theorem code_at {before current : State} {source : Fin 16} {value : Word} (input : Inputs before source value)
    (frame : X86StateFrame.Frame {.rax, .rip} (writes input) before current)
    (index byte : Nat) (present : (expected source input.displacement)[index]? = some byte) :
    current.mem.get? ((address input.address.toInt index).signExtend 52).toNat = some (BitVec.ofNat 8 byte) :=
  frame.codeLoaded _ _ input.loaded input.codeOutside index byte present

def moved (state : State) (base : Int) (value : Word) : State :=
  X86Move.putPointer (put state 0 value) (address base 3)
def statusStored (state : State) {source : Fin 16} {value : Word} (input : Inputs state source value) : State :=
  X86Move.putPointer (X86WriteWords.storeBytes 8 (moved state input.address.toInt value)
    input.statusAddress (1#64)) (address input.address.toInt 14)
def resultStored (state : State) {source : Fin 16} {value : Word} (input : Inputs state source value) : State :=
  X86Move.putPointer (X86WriteWords.storeBytes 8 (statusStored state input)
    input.resultAddress value) (address input.address.toInt 21)
def finished (state : State) {source : Fin 16} {value : Word} (input : Inputs state source value) : State :=
  X86Move.putPointer (resultStored state input) input.epilogue

theorem moved_frame (state : State) {source : Fin 16} {value : Word} (input : Inputs state source value) :
    X86StateFrame.Frame {.rax, .rip} (writes input) state (moved state input.address.toInt value) := by
  have frame : RegisterFrame {.rax, .rip} state (moved state input.address.toInt value) := by
    simpa [moved, key] using (put_frame state 0 value).trans (pointer_frame _ (address input.address.toInt 3))
  exact (X86StateFrame.registerOnly frame).mono (Finset.Subset.refl _) (Finset.empty_subset _)

theorem status_step_frame (state : State) {source : Fin 16} {value : Word} (input : Inputs state source value) :
    X86StateFrame.Frame {.rip} (X86WriteWords.written input.statusAddress (List.range 8))
      (moved state input.address.toInt value) (statusStored state input) := X86FrameStore.result_frame _ _ _ _

theorem status_frame (state : State) {source : Fin 16} {value : Word} (input : Inputs state source value) :
    X86StateFrame.Frame {.rax, .rip} (writes input) state (statusStored state input) := by
  apply ((moved_frame state input).trans (status_step_frame state input)).mono
  · simp
  · exact Finset.union_subset (Finset.Subset.refl _) Finset.subset_union_left

theorem result_step_frame (state : State) {source : Fin 16} {value : Word} (input : Inputs state source value) :
    X86StateFrame.Frame {.rip} (X86WriteWords.written input.resultAddress (List.range 8))
      (statusStored state input) (resultStored state input) := X86FrameStore.result_frame _ _ _ _

theorem result_frame (state : State) {source : Fin 16} {value : Word} (input : Inputs state source value) :
    X86StateFrame.Frame {.rax, .rip} (writes input) state (resultStored state input) := by
  apply ((status_frame state input).trans (result_step_frame state input)).mono
  · simp
  · exact Finset.union_subset (Finset.Subset.refl _) Finset.subset_union_right

theorem finished_frame (state : State) {source : Fin 16} {value : Word} (input : Inputs state source value) :
    X86StateFrame.Frame {.rax, .rip} (writes input) state (finished state input) := by
  simpa [finished] using (result_frame state input).trans
    (X86StateFrame.registerOnly (pointer_frame _ input.epilogue))

theorem move_executes (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (source : Fin 16) (value : Word) (input : Inputs state source value) :
    letI : OtherOpcodeHandlers := linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    Step state (moved state input.address.toInt value) := by
  let : OtherOpcodeHandlers := linkedHandlers other
  let : VectorOpcodeHandlers := vector
  let site := windowAt state state input.toBasis (RegisterFrame.refl dataRegisters state)
    input.upper 0 (by decide) (by simpa [address, BitVec.ofInt_toInt] using input.rip)
    (expected source input.displacement) input.loaded source 0 (0x89#8) (by rfl) (by rfl) (by rfl)
  have run := X86InstructionFetch.fetch_register64 state site.address site.opcodeAddress site.modrmAddress site.next
    site.control site.attributes source 0 site.step1 site.step2 site.step3 site.status site.fault
    site.msrs site.segments site.longMode site.codeMode site.application site.rip
    site.prefixByte site.opcodeByte site.modrmByte value input.sourceKnown input.quiet
  simpa [Step, moved, site, windowAt, rebase] using run

theorem store_status_executes (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (source : Fin 16) (value : Word) (input : Inputs state source value) :
    letI : OtherOpcodeHandlers := linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    Step (moved state input.address.toInt value) (statusStored state input) := by
  let current := moved state input.address.toInt value
  have frame := moved_frame state input
  let site := X86StateFrame.rebase state current input.toBasis frame (by decide)
    (extent := 26) input.upper 3 (by decide) (X86FuelPrefix.pointer_rip _ _)
  have run := X86FrameStore.fetched_immediate (linkedHandlers other) vector current site
    (address input.address.toInt 10) (address input.address.toInt 14) input.statusAddress input.visible input.controls
    input.frame input.flags (0x90#32) (1#32)
    (by dsimp only [site, X86StateFrame.rebase]; rw [offset_int input 6 (by decide), offset_int input 10 (by decide)]; omega)
    (by rw [offset_int input 10 (by decide), offset_int input 14 (by decide)]; omega)
    input.statusUpper ((frame.lookup 7 (by decide)).trans input.frameKnown)
    ((frame.registers .ctrs (by decide)).trans input.controlsKnown)
    ((frame.registers .rflags (by decide)).trans input.flagsKnown)
    ((frame.registers .seg_visibles (by decide)).trans input.visibleKnown)
    ((frame.registers .log_register_writes (by decide)).trans input.quiet)
    input.statusEffective input.statusAligned
    (code_at input frame 3 72 rfl) (code_at input frame 4 199 rfl) (code_at input frame 5 135 rfl)
    (by intro index within; dsimp only [site, X86StateFrame.rebase]; rw [nested_address input 6 index (by decide)]
        interval_cases index <;> exact code_at input frame _ _ rfl)
    (by intro index within; rw [nested_address input 10 index (by decide)]
        interval_cases index <;> exact code_at input frame _ _ rfl)
  rw [show (1#32).signExtend 64 = (1#64) from by decide] at run
  simpa only [X86FailureHandler.stores_installed, Step, current, statusStored] using run

theorem store_result_executes (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (source : Fin 16) (value : Word) (input : Inputs state source value) :
    letI : OtherOpcodeHandlers := linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    Step (statusStored state input) (resultStored state input) := by
  let current := statusStored state input
  have frame := status_frame state input
  let site := X86StateFrame.rebase state current input.toBasis frame (by decide)
    (extent := 26) input.upper 14 (by decide) (X86FuelPrefix.pointer_rip _ _)
  have rax : lookup current 0 = some value := by
    rw [(status_step_frame state input).lookup 0 (by decide)]
    exact (X86Move.lookup_putPointer (put state 0 value) (address input.address.toInt 3) 0).trans
      (lookup_put_same state 0 value)
  have run := X86FrameStore.fetched_register (linkedHandlers other) vector current 0 site
    (address input.address.toInt 21) input.resultAddress input.visible input.controls input.frame
    value input.flags (0x98#32)
    (by dsimp only [site, X86StateFrame.rebase]; rw [offset_int input 17 (by decide), offset_int input 21 (by decide)]; omega)
    input.resultUpper ((frame.lookup 7 (by decide)).trans input.frameKnown) rax
    ((frame.registers .ctrs (by decide)).trans input.controlsKnown)
    ((frame.registers .rflags (by decide)).trans input.flagsKnown)
    ((frame.registers .seg_visibles (by decide)).trans input.visibleKnown)
    ((frame.registers .log_register_writes (by decide)).trans input.quiet)
    input.resultEffective input.resultAligned
    (code_at input frame 14 72 rfl) (code_at input frame 15 137 rfl) (code_at input frame 16 135 rfl)
    (by intro index within; dsimp only [site, X86StateFrame.rebase]; rw [nested_address input 17 index (by decide)]
        interval_cases index <;> exact code_at input frame _ _ rfl)
  simpa only [Step, current, resultStored] using run

theorem jump_executes (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (source : Fin 16) (value : Word) (input : Inputs state source value) :
    letI : OtherOpcodeHandlers := linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    Step (resultStored state input) (finished state input) := by
  let current := resultStored state input
  have frame := result_frame state input
  have run := X86UnconditionalJump.fetched_jump (linkedHandlers other) vector current
    (address input.address.toInt 21) (address input.address.toInt 22) (address input.address.toInt 26)
    input.epilogue input.control input.attributes input.displacement
    (by rw [offset_int input 21 (by decide), offset_int input 22 (by decide)]; omega)
    (by rw [offset_int input 22 (by decide), offset_int input 26 (by decide)]; omega)
    (by rw [offset_int input 26 (by decide)]; exact input.jump)
    ((frame.registers .ms_reg (by decide)).trans input.status)
    ((frame.registers .fault_reg (by decide)).trans input.fault)
    ((frame.registers .msrs (by decide)).trans input.msrs)
    ((frame.registers .seg_hidden_attrs (by decide)).trans input.segments)
    input.longMode input.codeMode ((frame.registers .app_view (by decide)).trans input.application)
    (X86FuelPrefix.pointer_rip _ _) ((frame.registers .log_register_writes (by decide)).trans input.quiet)
    (code_at input frame 21 233 rfl) (by
      intro index within
      rw [nested_address input 22 index (by decide)]
      have got := code_at input frame (22 + index) (input.displacement.extractLsb' (8 * index) 8).toNat
        (by interval_cases index <;> rfl)
      simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using got)
  simpa only [X86FailureHandler.jump_installed, Step, current, finished] using run

theorem executes (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (source : Fin 16) (value : Word) (input : Inputs state source value) :
    letI : OtherOpcodeHandlers := linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    (X86FuelPrefix.fetches 4).run state = .ok () (finished state input) := by
  let : OtherOpcodeHandlers := linkedHandlers other
  let : VectorOpcodeHandlers := vector
  exact X86FuelPrefix.fetches_cons 3 state _ _ (move_executes other vector state source value input)
    (X86FuelPrefix.fetches_cons 2 _ _ _ (store_status_executes other vector state source value input)
      (X86FuelPrefix.fetches_cons 1 _ _ _ (store_result_executes other vector state source value input)
        (X86FuelPrefix.fetches_one _ _ (jump_executes other vector state source value input))))

theorem finished_rax (state : State) (source : Fin 16) (value : Word) (input : Inputs state source value) :
    lookup (finished state input) 0 = some value := by
  rw [finished, X86Move.lookup_putPointer, (result_step_frame state input).lookup 0 (by decide),
    (status_step_frame state input).lookup 0 (by decide)]
  exact (X86Move.lookup_putPointer (put state 0 value) (address input.address.toInt 3) 0).trans
    (lookup_put_same state 0 value)

theorem status_memory (state : State) {source : Fin 16} {value : Word} (input : Inputs state source value) :
    (statusStored state input).mem =
      (X86WriteWords.storeBytes 8 (moved state input.address.toInt value) input.statusAddress (1#64)).mem :=
  (pointer_frame (X86WriteWords.storeBytes 8 (moved state input.address.toInt value)
    input.statusAddress (1#64)) (address input.address.toInt 14)).memory

theorem result_memory (state : State) {source : Fin 16} {value : Word} (input : Inputs state source value) :
    (resultStored state input).mem =
      (X86WriteWords.storeBytes 8 (statusStored state input) input.resultAddress value).mem :=
  (pointer_frame (X86WriteWords.storeBytes 8 (statusStored state input)
    input.resultAddress value) (address input.address.toInt 21)).memory

theorem finished_memory (state : State) {source : Fin 16} {value : Word} (input : Inputs state source value) :
    (finished state input).mem = (resultStored state input).mem :=
  (pointer_frame (resultStored state input) input.epilogue).memory

theorem finished_status (state : State) (source : Fin 16) (value : Word) (input : Inputs state source value)
    (index : Nat) (within : index < 8) :
    (finished state input).mem.get? (X86WriteWords.physicalAddress input.statusAddress index) =
      some ((1#64).extractLsb' (8 * index) 8) := by
  rw [finished_memory, (result_step_frame state input).memory _ (input.statusOutside index within), status_memory]
  exact X86WriteWords.store_word_byte _ _ _ input.statusUpper index within

theorem finished_return (state : State) (source : Fin 16) (value : Word) (input : Inputs state source value)
    (index : Nat) (within : index < 8) :
    (finished state input).mem.get? (X86WriteWords.physicalAddress input.resultAddress index) =
      some (value.extractLsb' (8 * index) 8) := by
  rw [finished_memory, result_memory]
  exact X86WriteWords.store_word_byte _ _ _ input.resultUpper index within

structure Result (state : State) {source : Fin 16} {value : Word} (input : Inputs state source value)
    (after : State) : Prop where
  pointer : after.regs.get? .rip = some (input.epilogue.signExtend 64)
  rax : lookup after 0 = some value
  status : ∀ index < 8, after.mem.get? (X86WriteWords.physicalAddress input.statusAddress index) =
    some ((1#64).extractLsb' (8 * index) 8)
  result : ∀ index < 8, after.mem.get? (X86WriteWords.physicalAddress input.resultAddress index) =
    some (value.extractLsb' (8 * index) 8)
  frame : X86StateFrame.Frame {.rax, .rip} (writes input) state after
  flags : after.regs.get? .rflags = some input.flags

theorem finished_result (state : State) (source : Fin 16) (value : Word) (input : Inputs state source value) :
    Result state input (finished state input) :=
  ⟨X86FuelPrefix.pointer_rip _ _, finished_rax state source value input,
    finished_status state source value input, finished_return state source value input,
    finished_frame state input,
    ((finished_frame state input).registers .rflags (by decide)).trans input.flagsKnown⟩

theorem any_run_refines (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (source : Fin 16) (value : Word) (input : Inputs state source value) (after : State) :
    letI : OtherOpcodeHandlers := linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    (X86FuelPrefix.fetches 4).run state = .ok () after → Result state input after := by
  let : OtherOpcodeHandlers := linkedHandlers other
  let : VectorOpcodeHandlers := vector
  intro observed
  have same := (EStateM.Result.ok.inj ((executes other vector state source value input).symm.trans observed)).2
  subst after
  exact finished_result state source value input

end Mettapedia.Machines.TIsa.X86ReturnPath

#print axioms Mettapedia.Machines.TIsa.X86ReturnPath.move_executes
#print axioms Mettapedia.Machines.TIsa.X86ReturnPath.executes
#print axioms Mettapedia.Machines.TIsa.X86ReturnPath.finished_frame
#print axioms Mettapedia.Machines.TIsa.X86ReturnPath.finished_result
#print axioms Mettapedia.Machines.TIsa.X86ReturnPath.any_run_refines
