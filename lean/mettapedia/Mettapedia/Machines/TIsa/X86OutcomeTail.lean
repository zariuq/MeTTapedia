import Mettapedia.Machines.TIsa.X86FailureHandler

/-!
# Shared native outcome stores

Two fetched stores copy RAX to the status and result words while preserving
all registers except RIP and all bytes outside those two words. This is the
fourteen-byte tail shared by the actual unsupported, invalid-input and
exhaustion handlers. Its entry facts mention only the bytes still to execute;
an earlier immediate load or branch has its own contract.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.X86OutcomeTail
open _root_.X86Registers X86RegisterRefinement X86Execution
local instance : MemoryPrimitives := X86Memory.ordinary

def code : List Nat := [0x48,0x89,0x87,0x90,0,0,0,0x48,0x89,0x87,0x98,0,0,0]

structure Inputs (state : State) (value : Word) extends
    X86LegacyFetch.Basis state, X86FailureHandler.FrameFacts state where
  upper : address.toInt + 17 < (2 ^ 47 : Int)
  valueKnown : lookup state 0 = some value
  loaded : codeLoaded state address.toInt code
  codeOutside : ∀ index byte, code[index]? = some byte →
    ((X86Execution.address address.toInt index).signExtend 52).toNat ∉
      X86WriteWords.written statusAddress (List.range 8) ∪ X86WriteWords.written resultAddress (List.range 8)

def writes {state : State} {value : Word} (input : Inputs state value) : Finset Nat :=
  X86WriteWords.written input.statusAddress (List.range 8) ∪
    X86WriteWords.written input.resultAddress (List.range 8)

theorem offset_int {state : State} {value : Word} (input : Inputs state value)
    (offset : Nat) (within : offset ≤ 17) :
    (address input.address.toInt offset).toInt = input.address.toInt + offset :=
  address_toInt input.address.toInt (by simpa using BitVec.le_toInt input.address) input.upper offset within

theorem nested_address {state : State} {value : Word} (input : Inputs state value)
    (offset index : Nat) (within : offset ≤ 17) :
    address (address input.address.toInt offset).toInt index = address input.address.toInt (offset + index) := by
  rw [offset_int input offset within]
  simp only [address,Nat.cast_add,Int.add_assoc]

def statusStored (state : State) {value : Word} (input : Inputs state value) : State :=
  X86Move.putPointer (X86WriteWords.storeBytes 8 state input.statusAddress value)
    (address input.address.toInt 7)

def finished (state : State) {value : Word} (input : Inputs state value) : State :=
  X86Move.putPointer (X86WriteWords.storeBytes 8 (statusStored state input) input.resultAddress value)
    (address input.address.toInt 14)

theorem status_frame (state : State) {value : Word} (input : Inputs state value) :
    X86StateFrame.Frame {.rip} (writes input) state (statusStored state input) :=
  (X86FrameStore.result_frame _ _ _ _).mono (Finset.Subset.refl _) Finset.subset_union_left

theorem finished_frame (state : State) {value : Word} (input : Inputs state value) :
    X86StateFrame.Frame {.rip} (writes input) state (finished state input) := by
  apply ((status_frame state input).trans (X86FrameStore.result_frame _ _ _ _)).mono
  · simp
  · exact Finset.union_subset (Finset.Subset.refl _) Finset.subset_union_right

theorem code_at {before current : State} {value : Word} (input : Inputs before value)
    (frame : X86StateFrame.Frame {.rip} (writes input) before current)
    (index byte : Nat) (present : code[index]? = some byte) :
    current.mem.get? ((address input.address.toInt index).signExtend 52).toNat = some (BitVec.ofNat 8 byte) :=
  frame.codeLoaded _ _ input.loaded input.codeOutside index byte present

theorem store_status_executes (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (value : Word) (input : Inputs state value) :
    letI : OtherOpcodeHandlers := other
    letI : VectorOpcodeHandlers := vector
    Step state (statusStored state input) := by
  let : OtherOpcodeHandlers := other
  let : VectorOpcodeHandlers := vector
  have run := X86FrameStore.fetched_register other vector state 0 input.toBasis
    (address input.address.toInt 7) input.statusAddress input.visible input.controls input.frame value
    input.flags (0x90#32)
    (by rw [offset_int input 7 (by decide)]; have := input.step2; have := input.step3; omega)
    input.statusUpper input.frameKnown input.valueKnown input.controlsKnown input.flagsKnown
    input.visibleKnown input.quiet input.statusEffective input.statusAligned
    (by
      rw [show X86FrameLoad.frameRex (0 : Fin 16) = (0x48#8) from by decide]
      simpa [address,BitVec.ofInt_toInt] using input.loaded 0 0x48 rfl)
    (by
      have place : address input.address.toInt 1 = input.opcodeAddress := by
        change BitVec.ofInt 48 (input.address.toInt + 1) = _
        rw [input.step1,BitVec.ofInt_toInt]
      simpa only [place] using input.loaded 1 0x89 rfl)
    (by
      rw [show X86FrameLoad.frameModRM (0 : Fin 16) = (0x87#8) from by decide]
      have place : address input.address.toInt 2 = input.modrmAddress := by
        change BitVec.ofInt 48 (input.address.toInt + 2) = _
        rw [input.step2,BitVec.ofInt_toInt]
      simpa only [place] using input.loaded 2 0x87 rfl)
    (by
      intro index within
      have atNext : input.next.toInt = input.address.toInt + 3 := by
        have := input.step1; have := input.step2; have := input.step3; omega
      rw [atNext]
      have shifted : address (input.address.toInt + 3) index = address input.address.toInt (3 + index) := by
        simp [address,Nat.cast_add,Int.add_assoc]
      rw [shifted]
      interval_cases index <;> exact input.loaded _ _ rfl)
  exact run

theorem store_result_executes (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (value : Word) (input : Inputs state value) :
    letI : OtherOpcodeHandlers := other
    letI : VectorOpcodeHandlers := vector
    Step (statusStored state input) (finished state input) := by
  let : OtherOpcodeHandlers := other
  let : VectorOpcodeHandlers := vector
  let current := statusStored state input
  have frame := status_frame state input
  let site := X86StateFrame.rebase state current input.toBasis frame (by decide)
    (extent := 17) input.upper 7 (by decide) (X86FuelPrefix.pointer_rip _ _)
  have run := X86FrameStore.fetched_register other vector current 0 site
    (address input.address.toInt 14) input.resultAddress input.visible input.controls input.frame value
    input.flags (0x98#32)
    (by dsimp only [site,X86StateFrame.rebase]; rw [offset_int input 10 (by decide),offset_int input 14 (by decide)]; omega)
    input.resultUpper ((frame.lookup 7 (by decide)).trans input.frameKnown)
    ((frame.lookup 0 (by decide)).trans input.valueKnown)
    ((frame.registers .ctrs (by decide)).trans input.controlsKnown)
    ((frame.registers .rflags (by decide)).trans input.flagsKnown)
    ((frame.registers .seg_visibles (by decide)).trans input.visibleKnown)
    ((frame.registers .log_register_writes (by decide)).trans input.quiet)
    input.resultEffective input.resultAligned
    (code_at input frame 7 0x48 rfl) (code_at input frame 8 0x89 rfl) (code_at input frame 9 0x87 rfl)
    (by
      intro index within
      dsimp only [site,X86StateFrame.rebase]
      rw [nested_address input 10 index (by decide)]
      interval_cases index <;> exact code_at input frame _ _ rfl)
  exact run

theorem executes (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (value : Word) (input : Inputs state value) :
    letI : OtherOpcodeHandlers := other
    letI : VectorOpcodeHandlers := vector
    (X86FuelPrefix.fetches 2).run state = .ok () (finished state input) := by
  let : OtherOpcodeHandlers := other
  let : VectorOpcodeHandlers := vector
  exact X86FuelPrefix.fetches_then 1 1 _ _ _
    (X86FuelPrefix.fetches_one _ _ (store_status_executes other vector state value input))
    (X86FuelPrefix.fetches_one _ _ (store_result_executes other vector state value input))

theorem finished_pointer (state : State) (value : Word) (input : Inputs state value) :
    (finished state input).regs.get? .rip = some ((address input.address.toInt 14).signExtend 64) := by
  simp [finished,X86Move.putPointer]

theorem finished_value (state : State) (value : Word) (input : Inputs state value) :
    lookup (finished state input) 0 = some value :=
  ((finished_frame state input).lookup 0 (by decide)).trans input.valueKnown

theorem status_memory (state : State) (value : Word) (input : Inputs state value) :
    (statusStored state input).mem = (X86WriteWords.storeBytes 8 state input.statusAddress value).mem :=
  (pointer_frame _ _).memory

theorem finished_memory (state : State) (value : Word) (input : Inputs state value) :
    (finished state input).mem =
      (X86WriteWords.storeBytes 8 (statusStored state input) input.resultAddress value).mem :=
  (pointer_frame _ _).memory

theorem finished_status (state : State) (value : Word) (input : Inputs state value)
    (byte : Nat) (within : byte < 8) :
    (finished state input).mem.get? (X86WriteWords.physicalAddress input.statusAddress byte) =
      some (value.extractLsb' (8 * byte) 8) := by
  rw [finished_memory]
  rw [(X86WriteWords.storeBytes_frame 8 (statusStored state input) input.resultAddress value).memory _
    (input.statusOutside byte within),status_memory]
  exact X86WriteWords.store_word_byte state input.statusAddress value input.statusUpper byte within

theorem finished_output (state : State) (value : Word) (input : Inputs state value)
    (byte : Nat) (within : byte < 8) :
    (finished state input).mem.get? (X86WriteWords.physicalAddress input.resultAddress byte) =
      some (value.extractLsb' (8 * byte) 8) := by
  rw [finished_memory]
  exact X86WriteWords.store_word_byte (statusStored state input) input.resultAddress value input.resultUpper byte within

theorem finished_result (state : State) (value : Word) (input : Inputs state value) :
    (finished state input).regs.get? .rip = some ((address input.address.toInt 14).signExtend 64) ∧
    lookup (finished state input) 0 = some value ∧
    (∀ byte < 8, (finished state input).mem.get? (X86WriteWords.physicalAddress input.statusAddress byte) =
      some (value.extractLsb' (8 * byte) 8)) ∧
    (∀ byte < 8, (finished state input).mem.get? (X86WriteWords.physicalAddress input.resultAddress byte) =
      some (value.extractLsb' (8 * byte) 8)) ∧
    X86StateFrame.Frame {.rip} (writes input) state (finished state input) :=
  ⟨finished_pointer state value input,finished_value state value input,
    finished_status state value input,finished_output state value input,finished_frame state input⟩

#print axioms executes
#print axioms finished_result
end Mettapedia.Machines.TIsa.X86OutcomeTail
