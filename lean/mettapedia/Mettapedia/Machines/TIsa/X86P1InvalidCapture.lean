import Mettapedia.Machines.TIsa.X86OutcomeTail
import Mettapedia.Machines.TIsa.X86P1RefusedCapture
import Mettapedia.Machines.TIsa.X86P1SuccessCapture

/-!
# The proposition image's bounds rejection through the caller return

The first U32 load reaches the actual invalid-input handler when its region is
short or its offset is outside the permitted range. The handler loads outcome
three, jumps over the exhaustion load and uses the shared outcome stores.
The complete image supplies all instruction bytes, including the displacement.

The two bounds paths take twenty-seven or twenty-nine original-model fetches
through the public allowance call: eight for the saves and allowance setup, nine
or eleven in the body and ten for the receipt block and restores. They preserve
the complete image, restore all six saved registers, write both invalid-input
outcome words, republish the unchanged receipt and need no bytes at the
rejected data address. A concrete end-pointer witness has that address unmapped; controls
exclude other outcomes and a changed handler displacement.

This closes the first-load bounds-rejection class. Other memory failures,
whole-source admission/hosting and the generic emitter theorem remain separate.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.X86P1InvalidCapture
open _root_.X86Registers X86RegisterRefinement X86Execution
local instance : MemoryPrimitives := X86Memory.ordinary

noncomputable abbrev handlers := X86FailureHandler.linkedHandlers
def code : List Nat := [0xb8,3,0,0,0,0xe9,5,0,0,0,0xb8,4,0,0,0] ++ X86OutcomeTail.code
noncomputable abbrev image := X86P1LoadCapture.propImage

theorem captured_bytes (index : Fin 29) :
    image.view.read (590 + index.val) = (code[index.val]?).map (BitVec.ofNat 8) := by
  fin_cases index <;> kernel_reflexivity

theorem tail_byte (index byte : Nat) (present : X86OutcomeTail.code[index]? = some byte) :
    code[15 + index]? = some byte := by
  have bound : index < 14 := by
    have := (List.getElem?_eq_some_iff.mp present).1
    change index < 14 at this
    exact this
  interval_cases index <;> simpa [code,X86OutcomeTail.code] using present

structure Inputs (state : State) extends X86LegacyFetch.Basis state, X86FailureHandler.FrameFacts state where
  upper : address.toInt + 32 < (2 ^ 47 : Int)
  loaded : codeLoaded state address.toInt code
  codeOutside : ∀ index byte, code[index]? = some byte →
    ((X86Execution.address address.toInt index).signExtend 52).toNat ∉
      X86WriteWords.written statusAddress (List.range 8) ∪ X86WriteWords.written resultAddress (List.range 8)

def writes {state : State} (input : Inputs state) : Finset Nat :=
  X86WriteWords.written input.statusAddress (List.range 8) ∪
    X86WriteWords.written input.resultAddress (List.range 8)

theorem offset_int {state : State} (input : Inputs state) (offset : Nat) (within : offset ≤ 32) :
    (address input.address.toInt offset).toInt = input.address.toInt + offset :=
  address_toInt input.address.toInt (by simpa using BitVec.le_toInt input.address) input.upper offset within

theorem nested_address {state : State} (input : Inputs state) (offset index : Nat) (within : offset ≤ 32) :
    address (address input.address.toInt offset).toInt index = address input.address.toInt (offset + index) := by
  rw [offset_int input offset within]
  simp only [address,Nat.cast_add,Int.add_assoc]

def loaded (state : State) (input : Inputs state) : State :=
  X86Move.putPointer (put state 0 (3#64)) (address input.address.toInt 5)

def jumped (state : State) (input : Inputs state) : State :=
  X86Move.putPointer (loaded state input) (address input.address.toInt 15)

theorem loaded_memory (state : State) (input : Inputs state) : (loaded state input).mem = state.mem :=
  (pointer_frame (put state 0 (3#64)) _).memory.trans (put_frame state 0 (3#64)).memory

theorem prefix_memory (state : State) (input : Inputs state) : (jumped state input).mem = state.mem :=
  (pointer_frame (loaded state input) _).memory.trans (loaded_memory state input)

theorem loaded_frame (state : State) (input : Inputs state) :
    X86StateFrame.Frame {.rax,.rip} ∅ state (loaded state input) :=
  X86StateFrame.registerOnly (X86OutcomeLoad.result_frame state (3#32) _)

theorem prefix_frame (state : State) (input : Inputs state) :
    X86StateFrame.Frame {.rax,.rip} ∅ state (jumped state input) :=
  ((loaded_frame state input).trans (X86StateFrame.registerOnly (pointer_frame _ _))).mono
    (by simp) (by simp)

theorem load_executes (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (input : Inputs state) :
    letI : OtherOpcodeHandlers := handlers other
    letI : VectorOpcodeHandlers := vector
    Step state (loaded state input) := by
  let : OtherOpcodeHandlers := handlers other
  let : VectorOpcodeHandlers := vector
  have run := X86OutcomeLoad.fetched_eax (handlers other) vector state input.toBasis
    (address input.address.toInt 5) (3#32)
    (by rw [offset_int input 5 (by decide)]; have := input.step1; omega) input.quiet
    (by simpa [address,BitVec.ofInt_toInt] using input.loaded 0 0xb8 rfl)
    (by
      intro index within
      have shifted : address input.opcodeAddress.toInt index = address input.address.toInt (1 + index) := by
        rw [← input.step1]
        simp [address,Nat.cast_add,Int.add_assoc]
      rw [shifted]
      interval_cases index <;> exact input.loaded _ _ rfl)
  rw [show (3#32).zeroExtend 64 = (3#64) from by decide] at run
  simpa only [handlers,X86FailureHandler.stores_installed,Step,loaded] using run

theorem jump_executes (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (input : Inputs state) :
    letI : OtherOpcodeHandlers := handlers other
    letI : VectorOpcodeHandlers := vector
    Step (loaded state input) (jumped state input) := by
  let : OtherOpcodeHandlers := handlers other
  let : VectorOpcodeHandlers := vector
  let current := loaded state input
  have frame := loaded_frame state input
  have memory : current.mem = state.mem := loaded_memory state input
  have run := X86UnconditionalJump.fetched_jump (handlers other) vector current
    (address input.address.toInt 5) (address input.address.toInt 6) (address input.address.toInt 10)
    (address input.address.toInt 15) input.control input.attributes (5#32)
    (by rw [offset_int input 5 (by decide),offset_int input 6 (by decide)]; omega)
    (by rw [offset_int input 6 (by decide),offset_int input 10 (by decide)]; omega)
    (by rw [offset_int input 10 (by decide),offset_int input 15 (by decide)];
        have : (5#32).toInt = 5 := by decide
        omega)
    ((frame.registers .ms_reg (by decide)).trans input.status)
    ((frame.registers .fault_reg (by decide)).trans input.fault)
    ((frame.registers .msrs (by decide)).trans input.msrs)
    ((frame.registers .seg_hidden_attrs (by decide)).trans input.segments)
    input.longMode input.codeMode ((frame.registers .app_view (by decide)).trans input.application)
    (X86FuelPrefix.pointer_rip _ _) ((frame.registers .log_register_writes (by decide)).trans input.quiet)
    (by rw [memory]; exact input.loaded 5 0xe9 rfl)
    (by
      intro index within
      rw [memory,nested_address input 6 index (by decide)]
      interval_cases index <;> exact input.loaded _ _ rfl)
  simpa only [handlers,X86FailureHandler.jump_installed,Step,current,jumped] using run

def tailInput (state : State) (input : Inputs state) : X86OutcomeTail.Inputs (jumped state input) (3#64) := by
  have frame := prefix_frame state input
  let origin := X86StateFrame.rebase state (jumped state input) input.toBasis frame (by decide)
    (extent := 32) input.upper 15 (by decide) (X86FuelPrefix.pointer_rip _ _)
  refine {
    toBasis := origin
    toFrameFacts := {
      input.toFrameFacts with
      frameKnown := (frame.lookup 7 (by decide)).trans input.frameKnown
      controlsKnown := (frame.registers .ctrs (by decide)).trans input.controlsKnown
      visibleKnown := (frame.registers .seg_visibles (by decide)).trans input.visibleKnown
      flagsKnown := (frame.registers .rflags (by decide)).trans input.flagsKnown
      quiet := (frame.registers .log_register_writes (by decide)).trans input.quiet }
    upper := ?_
    valueKnown := ?_
    loaded := ?_
    codeOutside := ?_ }
  · dsimp only [origin,X86StateFrame.rebase]
    rw [offset_int input 15 (by decide)]
    have := input.upper
    omega
  · simp only [jumped,loaded,X86Move.lookup_putPointer,lookup_put_same]
  · intro index byte present
    change (jumped state input).mem.get?
      ((address (address input.address.toInt 15).toInt index).signExtend 52).toNat = _
    rw [prefix_memory,nested_address input 15 index (by decide)]
    exact input.loaded (15 + index) byte (tail_byte index byte present)
  · intro index byte present
    change ((address (address input.address.toInt 15).toInt index).signExtend 52).toNat ∉ _
    rw [nested_address input 15 index (by decide)]
    exact input.codeOutside (15 + index) byte (tail_byte index byte present)

def finished (state : State) (input : Inputs state) : State :=
  X86OutcomeTail.finished (jumped state input) (tailInput state input)

theorem executes (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (input : Inputs state) :
    letI : OtherOpcodeHandlers := handlers other
    letI : VectorOpcodeHandlers := vector
    (X86FuelPrefix.fetches 4).run state = .ok () (finished state input) := by
  let : OtherOpcodeHandlers := handlers other
  let : VectorOpcodeHandlers := vector
  exact X86FuelPrefix.fetches_then 2 2 _ _ _
    (X86FuelPrefix.fetches_then 1 1 _ _ _
      (X86FuelPrefix.fetches_one _ _ (load_executes other vector state input))
      (X86FuelPrefix.fetches_one _ _ (jump_executes other vector state input)))
    (X86OutcomeTail.executes (handlers other) vector _ _ (tailInput state input))

theorem result_frame (state : State) (input : Inputs state) :
    X86StateFrame.Frame {.rax,.rip} (writes input) state (finished state input) := by
  apply ((prefix_frame state input).trans
    (X86OutcomeTail.finished_frame (jumped state input) (tailInput state input))).mono
  · simp
  · simp only [Finset.empty_union]
    exact Finset.Subset.refl _

theorem finished_pointer (state : State) (input : Inputs state) :
    (finished state input).regs.get? .rip = some ((address input.address.toInt 29).signExtend 64) := by
  have result := X86OutcomeTail.finished_pointer (jumped state input) (3#64) (tailInput state input)
  change (finished state input).regs.get? .rip = some
    ((address (address input.address.toInt 15).toInt 14).signExtend 64) at result
  simpa only [nested_address input 15 14 (by decide)] using result

theorem finished_value (state : State) (input : Inputs state) : lookup (finished state input) 0 = some (3#64) :=
  X86OutcomeTail.finished_value _ _ (tailInput state input)

theorem finished_status (state : State) (input : Inputs state) (byte : Nat) (within : byte < 8) :
    (finished state input).mem.get? (X86WriteWords.physicalAddress input.statusAddress byte) =
      some ((3#64).extractLsb' (8 * byte) 8) :=
  X86OutcomeTail.finished_status _ _ (tailInput state input) byte within

theorem finished_output (state : State) (input : Inputs state) (byte : Nat) (within : byte < 8) :
    (finished state input).mem.get? (X86WriteWords.physicalAddress input.resultAddress byte) =
      some ((3#64).extractLsb' (8 * byte) 8) :=
  X86OutcomeTail.finished_output _ _ (tailInput state input) byte within

def capturedInput (state : State) (base : Int) (origin : X86LegacyFetch.Basis state)
    (facts : X86FailureHandler.FrameFacts state) (placed : origin.address.toInt = base + 590)
    (upper : base + 647 < (2 ^ 47 : Int)) (present : X86P1LoadCapture.Loaded image state base)
    (apart : X86P1RefusedCapture.ImageApart facts base) : Inputs state := by
  have loadedHere : codeLoaded state origin.address.toInt code := by
    intro index byte bytePresent
    have within : index < 29 := by
      have := (List.getElem?_eq_some_iff.mp bytePresent).1
      change index < 29 at this
      exact this
    have got := captured_bytes ⟨index,within⟩
    rw [bytePresent,Option.map_some] at got
    have shifted : address base (590 + index) = address origin.address.toInt index := by
      unfold address
      rw [placed]
      congr 1
      omega
    simpa only [shifted] using (present (590 + index) (by rw [X86P1LoadCapture.byte_extent]; omega)).trans got
  refine {
    toBasis := origin
    toFrameFacts := facts
    upper := by omega
    loaded := loadedHere
    codeOutside := ?_ }
  intro index byte bytePresent
  have within : index < 29 := by
    have := (List.getElem?_eq_some_iff.mp bytePresent).1
    change index < 29 at this
    exact this
  have shifted : address origin.address.toInt index = address base (590 + index) := by
    unfold address
    rw [placed]
    congr 1
    omega
  rw [shifted]
  exact apart (590 + index) (by rw [X86P1LoadCapture.byte_extent]; omega)

theorem captured_executes (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (base : Int) (origin : X86LegacyFetch.Basis state)
    (facts : X86FailureHandler.FrameFacts state) (placed : origin.address.toInt = base + 590)
    (upper : base + 647 < (2 ^ 47 : Int)) (present : X86P1LoadCapture.Loaded image state base)
    (apart : X86P1RefusedCapture.ImageApart facts base) :
    letI : OtherOpcodeHandlers := handlers other
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 4).run state = .ok () after ∧
      after.regs.get? .rip = some ((address base 619).signExtend 64) ∧
      lookup after 0 = some (3#64) ∧
      (∀ byte < 8, after.mem.get? (X86WriteWords.physicalAddress facts.statusAddress byte) =
        some ((3#64).extractLsb' (8 * byte) 8)) ∧
      (∀ byte < 8, after.mem.get? (X86WriteWords.physicalAddress facts.resultAddress byte) =
        some ((3#64).extractLsb' (8 * byte) 8)) ∧
      X86StateFrame.Frame {.rax,.rip} (X86P1RefusedCapture.writes facts) state after ∧
      after.regs.get? .rflags = some facts.flags ∧ X86P1LoadCapture.Loaded image after base := by
  let : OtherOpcodeHandlers := handlers other
  let : VectorOpcodeHandlers := vector
  let input := capturedInput state base origin facts placed upper present apart
  let after := finished state input
  have frame := result_frame state input
  have pointer := finished_pointer state input
  have site : address input.address.toInt 29 = address base 619 := by
    change address origin.address.toInt 29 = _
    unfold address
    rw [placed]
    congr 1
    omega
  refine ⟨after,executes other vector state input,?_,finished_value state input,
    finished_status state input,finished_output state input,frame,?_,?_⟩
  · simpa only [site] using pointer
  · exact (frame.registers .rflags (by decide)).trans facts.flagsKnown
  · intro index within
    rw [frame.memory _ (apart index within)]
    exact present index within

theorem execution_prefix_frame (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (input : Inputs state) (count : Nat) (within : count ≤ 4)
    (observed : State) :
    letI : OtherOpcodeHandlers := handlers other
    letI : VectorOpcodeHandlers := vector
    (X86FuelPrefix.fetches count).run state = .ok () observed →
      X86StateFrame.Frame {.rax,.rip} (writes input) state observed := by
  let : OtherOpcodeHandlers := handlers other
  let : VectorOpcodeHandlers := vector
  intro candidate
  have first := X86FuelPrefix.fetches_one state (loaded state input) (load_executes other vector state input)
  have second := X86FuelPrefix.fetches_then 1 1 state (loaded state input) (jumped state input) first
    (X86FuelPrefix.fetches_one _ _ (jump_executes other vector state input))
  interval_cases count
  · have same := X86FuelPrefix.fetches_deterministic 0 state state observed (X86FuelPrefix.fetches_zero state) candidate
    subst observed
    exact X86StateFrame.Frame.refl _ _ _
  · have same := X86FuelPrefix.fetches_deterministic 1 state (loaded state input) observed first candidate
    subst observed
    exact (loaded_frame state input).mono (Finset.Subset.refl _) (by simp)
  · have same := X86FuelPrefix.fetches_deterministic 2 state (jumped state input) observed second candidate
    subst observed
    exact (prefix_frame state input).mono (Finset.Subset.refl _) (by simp)
  · let tail := tailInput state input
    let after := X86OutcomeTail.statusStored (jumped state input) tail
    have third := X86FuelPrefix.fetches_then 2 1 state (jumped state input) after second
      (X86FuelPrefix.fetches_one _ _ (X86OutcomeTail.store_status_executes (handlers other) vector _ _ tail))
    have same := X86FuelPrefix.fetches_deterministic 3 state after observed third candidate
    subst observed
    apply ((prefix_frame state input).trans (X86OutcomeTail.status_frame (jumped state input) tail)).mono
    · simp
    · simp only [Finset.empty_union]
      exact Finset.Subset.refl _
  · have same := X86FuelPrefix.fetches_deterministic 4 state (finished state input) observed
      (executes other vector state input) candidate
    subst observed
    exact result_frame state input

def imageInput (program : P1Capture.Program) (offset : Nat)
    (bytes : ∀ index : Fin 29,
      program.view.read (offset + index.val) = (code[index.val]?).map (BitVec.ofNat 8))
    (extent : offset + 32 < program.size)
    (state : State) (base : Int) (origin : X86LegacyFetch.Basis state)
    (facts : X86FailureHandler.FrameFacts state) (placed : origin.address.toInt = base + offset)
    (upper : base + program.size < (2 ^ 47 : Int))
    (present : X86P1LoadCapture.Loaded program state base)
    (apart : ∀ index < program.size,
      ((address base index).signExtend 52).toNat ∉ X86P1RefusedCapture.writes facts) : Inputs state := by
  refine {
    toBasis := origin
    toFrameFacts := facts
    upper := by omega
    loaded := ?_
    codeOutside := ?_ }
  · intro index byte encoded
    have within : index < 29 := (List.getElem?_eq_some_iff.mp encoded).1
    have captured := bytes ⟨index,within⟩
    rw [encoded,Option.map_some] at captured
    have shifted : address base (offset + index) = address origin.address.toInt index := by
      unfold address
      rw [placed]
      congr 1
      omega
    simpa only [shifted] using (present (offset + index) (by omega)).trans captured
  · intro index byte encoded
    have within : index < 29 := (List.getElem?_eq_some_iff.mp encoded).1
    have shifted : address origin.address.toInt index = address base (offset + index) := by
      unfold address
      rw [placed]
      congr 1
      omega
    rw [shifted]
    exact apart (offset + index) (by omega)

theorem image_executes (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (program : P1Capture.Program) (offset : Nat)
    (bytes : ∀ index : Fin 29,
      program.view.read (offset + index.val) = (code[index.val]?).map (BitVec.ofNat 8))
    (extent : offset + 32 < program.size)
    (state : State) (base : Int) (origin : X86LegacyFetch.Basis state)
    (facts : X86FailureHandler.FrameFacts state) (placed : origin.address.toInt = base + offset)
    (upper : base + program.size < (2 ^ 47 : Int))
    (present : X86P1LoadCapture.Loaded program state base)
    (apart : ∀ index < program.size,
      ((address base index).signExtend 52).toNat ∉ X86P1RefusedCapture.writes facts) :
    letI : OtherOpcodeHandlers := handlers other
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 4).run state = .ok () after ∧
      after.regs.get? .rip = some ((address base (offset + 29)).signExtend 64) ∧
      lookup after 0 = some (3#64) ∧
      (∀ byte < 8, after.mem.get? (X86WriteWords.physicalAddress facts.statusAddress byte) =
        some ((3#64).extractLsb' (8 * byte) 8)) ∧
      (∀ byte < 8, after.mem.get? (X86WriteWords.physicalAddress facts.resultAddress byte) =
        some ((3#64).extractLsb' (8 * byte) 8)) ∧
      X86StateFrame.Frame {.rax,.rip} (X86P1RefusedCapture.writes facts) state after ∧
      after.regs.get? .rflags = some facts.flags ∧ X86P1LoadCapture.Loaded program after base := by
  let : OtherOpcodeHandlers := handlers other
  let : VectorOpcodeHandlers := vector
  let input := imageInput program offset bytes extent state base origin facts placed upper present apart
  let after := finished state input
  have frame := result_frame state input
  have shifted : address input.address.toInt 29 = address base (offset + 29) := by
    change address origin.address.toInt 29 = _
    unfold address
    rw [placed]
    congr 1
    omega
  refine ⟨after,executes other vector state input,?_,finished_value state input,
    finished_status state input,finished_output state input,frame,?_,?_⟩
  · simpa only [shifted] using finished_pointer state input
  · exact (frame.registers .rflags (by decide)).trans facts.flagsKnown
  · intro index within
    rw [frame.memory _ (apart index within)]
    exact present index within

theorem flags_of_preserved {before after : State} (control : X86ControlFlags.Preserved before after)
    {flags : BitVec 32} (known : before.regs.get? .rflags = some flags) :
    ∃ next, after.regs.get? .rflags = some next := by
  unfold X86ControlFlags.Preserved at control
  rw [known] at control
  cases observed : after.regs.get? .rflags with
  | none =>
      rw [observed] at control
      cases control
  | some next => exact ⟨next, rfl⟩

theorem rejected_prefix (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (state : State) (base : Int) (origin : X86LegacyFetch.Basis state)
    (facts : X86P1LoadBounds.Facts state origin 623) (placed : origin.address.toInt = base + 24)
    (present : X86P1LoadCapture.Loaded image state base)
    (outside : ¬ (facts.pointer - facts.base).toNat + 4 ≤ facts.length.toNat) :
    letI : OtherOpcodeHandlers := X86P1RefusedCapture.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after flags, (X86FuelPrefix.fetches (if facts.length.toNat < 4 then 5 else 7)).run state = .ok () after ∧
      RegisterFrame X86P1LoadBounds.writes state after ∧ after.regs.get? .rflags = some flags ∧
      after.regs.get? .rip = some ((address base 590).signExtend 64) ∧
      X86P1LoadCapture.Loaded image after base := by
  let : OtherOpcodeHandlers := X86P1RefusedCapture.handlers other extra
  let : VectorOpcodeHandlers := vector
  let input := X86P1LoadCapture.inputs state base origin facts placed present
  have portion := X86Bounds.classifies_control (X86UnconditionalJump.linked other)
    (X86ConditionByte.byteHandlers extra) vector _ state origin input.bounds
  rw [X86P1QwordGuardCapture.common_handlers] at portion
  obtain ⟨after,run,frame,rip,control⟩ := portion
  obtain ⟨flags,known⟩ := flags_of_preserved control facts.flagsKnown
  have notFits : ¬ (facts.pointer - facts.base).toNat + 0 + 4 ≤ facts.length.toNat := by omega
  change after.regs.get? .rip = some ((if (facts.pointer - facts.base).toNat + 0 + 4 ≤ facts.length.toNat
    then X86Bounds.position origin.address 36 else X86Bounds.position origin.address 566).signExtend 64) at rip
  have point : X86Bounds.position origin.address 566 = address base 590 := by
    unfold X86Bounds.position address
    rw [placed]
    congr 1
    omega
  rw [if_neg notFits, point] at rip
  have steps : X86Bounds.boundsSteps (X86BoundedLoad.layout X86P1LoadCapture.site) facts.base facts.pointer facts.length =
      if facts.length.toNat < 4 then 5 else 7 := by
    have noWrap := (facts.pointer - facts.base).isLt
    simp only [X86Bounds.boundsSteps]
    rw [if_neg (by change ¬ 2 ^ 64 ≤ (facts.pointer - facts.base).toNat + 0; omega)]
    rfl
  refine ⟨after,flags,steps ▸ run,frame,known,rip,?_⟩
  intro index within
  rw [frame.memory]
  exact present index within

def guardSteps (length : Word) : Nat := if length.toNat < 4 then 5 else 7

theorem load_bounds_invalid (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (state : State) (base : Int) (origin : X86LegacyFetch.Basis state)
    (facts : X86P1LoadBounds.Facts state origin 623) (resultFacts : X86FailureHandler.FrameFacts state)
    (placed : origin.address.toInt = base + 24) (present : X86P1LoadCapture.Loaded image state base)
    (apart : X86P1RefusedCapture.ImageApart resultFacts base)
    (outside : ¬ (facts.pointer - facts.base).toNat + 4 ≤ facts.length.toNat) :
    letI : OtherOpcodeHandlers := X86P1RefusedCapture.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after flags, (X86FuelPrefix.fetches (guardSteps facts.length + 4)).run state = .ok () after ∧
      after.regs.get? .rip = some ((address base 619).signExtend 64) ∧ lookup after 0 = some (3#64) ∧
      (∀ byte < 8, after.mem.get? (X86WriteWords.physicalAddress resultFacts.statusAddress byte) =
        some ((3#64).extractLsb' (8 * byte) 8)) ∧
      (∀ byte < 8, after.mem.get? (X86WriteWords.physicalAddress resultFacts.resultAddress byte) =
        some ((3#64).extractLsb' (8 * byte) 8)) ∧
      X86StateFrame.Frame {.rax,.rip,.rflags,.r14,.r15} (X86P1RefusedCapture.writes resultFacts) state after ∧
      after.regs.get? .rflags = some flags ∧ X86P1LoadCapture.Loaded image after base := by
  let : OtherOpcodeHandlers := X86P1RefusedCapture.handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨middle,flags,first,firstFrame,known,pointer,middleImage⟩ :=
    rejected_prefix other extra vector state base origin facts placed present outside
  have shifted : address base 590 = address origin.address.toInt 566 := by
    unfold address
    rw [placed]
    congr 1
    omega
  rw [shifted] at pointer
  let nextOrigin := rebase state middle origin (firstFrame.mono (by decide)) facts.upper 566 (by decide) pointer
  have nextPlaced : nextOrigin.address.toInt = base + 590 := by
    change (address origin.address.toInt 566).toInt = _
    rw [address_toInt origin.address.toInt (by simpa using BitVec.le_toInt origin.address)
      facts.upper 566 (by decide)]
    omega
  let nextFacts : X86FailureHandler.FrameFacts middle := {
    resultFacts with
    frameKnown := (firstFrame.lookup 7 (by decide)).trans resultFacts.frameKnown
    controlsKnown := (firstFrame.registers .ctrs (by decide)).trans resultFacts.controlsKnown
    visibleKnown := (firstFrame.registers .seg_visibles (by decide)).trans resultFacts.visibleKnown
    flags := flags
    flagsKnown := known
    quiet := (firstFrame.registers .log_register_writes (by decide)).trans resultFacts.quiet }
  have last := captured_executes (X86P1RefusedCapture.handlers other extra) vector middle base nextOrigin
    nextFacts nextPlaced (by have := facts.upper; omega) middleImage apart
  obtain ⟨after,run,rip,value,status,output,frame,finalFlags,imageAfter⟩ := last
  refine ⟨after,flags,X86FuelPrefix.fetches_then _ 4 state middle after first run,
    rip,value,status,output,?_,finalFlags,imageAfter⟩
  apply ((X86StateFrame.registerOnly firstFrame).trans frame).mono
  · decide
  · simp only [Finset.empty_union]
    exact Finset.Subset.refl _

theorem public_invalid (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (call : X86AllowanceCall.Inputs state) (base : Int)
    (entryAt : call.prologue.code.toInt = base) (exitAt : call.exit = address base 619)
    (upper : base + 647 < (2 ^ 47 : Int))
    (present : X86P1LoadCapture.Loaded image state base)
    {layout : X86Bounds.Layout} (pointerIs : layout.pointer = 6) (regionIs : layout.region = 0)
    (facts : X86Bounds.Facts layout state) (resultFacts : X86FailureHandler.FrameFacts state)
    (imageSpillApart : ∀ index < image.size,
      ((address base index).signExtend 52).toNat ∉ X86AllowanceCall.spillBytes call.prologue.bottom call.bottom)
    (imageBodyApart : X86P1RefusedCapture.ImageApart resultFacts base)
    (imageReceiptApart : ∀ index < image.size,
      ((address base index).signExtend 52).toNat ∉ X86AllowanceCall.receiptBytes call.fuel.receiptAddress)
    (baseSpillApart : ∀ byte < 8, ((address facts.baseAddress.toInt byte).signExtend 52).toNat ∉
      X86AllowanceCall.spillBytes call.prologue.bottom call.bottom)
    (lengthSpillApart : ∀ byte < 8, ((address facts.lengthAddress.toInt byte).signExtend 52).toNat ∉
      X86AllowanceCall.spillBytes call.prologue.bottom call.bottom)
    (statusReceiptApart : ∀ byte < 8, X86WriteWords.physicalAddress resultFacts.statusAddress byte ∉
      X86AllowanceCall.receiptBytes call.fuel.receiptAddress)
    (resultReceiptApart : ∀ byte < 8, X86WriteWords.physicalAddress resultFacts.resultAddress byte ∉
      X86AllowanceCall.receiptBytes call.fuel.receiptAddress)
    (budgetBodyApart : ∀ byte < 8, X86WriteWords.physicalAddress call.fuel.budgetAddress byte ∉
      X86P1RefusedCapture.writes resultFacts)
    (bottomApart : ∀ byte < 8, X86WriteWords.physicalAddress call.bottom byte ∉
      X86P1RefusedCapture.writes resultFacts ∪ X86AllowanceCall.receiptBytes call.fuel.receiptAddress)
    (savedApart : ∀ slot : Fin 6, ∀ byte < 8,
      X86WriteWords.physicalAddress (address call.prologue.bottom.toInt (8 * slot.val)) byte ∉
        X86P1RefusedCapture.writes resultFacts ∪ X86AllowanceCall.receiptBytes call.fuel.receiptAddress)
    (outside : ¬ (facts.pointer - facts.base).toNat + 4 ≤ facts.length.toNat) :
    letI : OtherOpcodeHandlers := X86P1RefusedCapture.callHandlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ body after, (X86FuelPrefix.fetches (8 + (guardSteps facts.length + 4) + 10)).run state = .ok () after ∧
      X86AllowanceCall.Result call (X86P1RefusedCapture.writes resultFacts) (call.fuel.budget - call.fuel.receipt)
        body after ∧
      lookup after 0 = some (3#64) ∧
      (∀ byte < 8, after.mem.get? (X86WriteWords.physicalAddress resultFacts.statusAddress byte) =
        some ((3#64).extractLsb' (8 * byte) 8)) ∧
      (∀ byte < 8, after.mem.get? (X86WriteWords.physicalAddress resultFacts.resultAddress byte) =
        some ((3#64).extractLsb' (8 * byte) 8)) ∧
      (∀ byte < 8, after.mem.get? (X86WriteWords.physicalAddress call.fuel.receiptAddress byte) =
        some (call.fuel.receipt.extractLsb' (8 * byte) 8)) ∧
      X86P1LoadCapture.Loaded image after base := by
  let : OtherOpcodeHandlers := X86P1RefusedCapture.callHandlers other extra
  let : VectorOpcodeHandlers := vector
  have lower : -(2 ^ 47 : Int) ≤ base := by rw [← entryAt]; simpa using BitVec.le_toInt call.prologue.code
  have codeUpper : call.prologue.code.toInt + 647 < (2 ^ 47 : Int) := by rw [entryAt]; exact upper
  have entry := call.enters (X86P1RefusedCapture.callHandlers other extra) vector
  rw [X86P1RefusedCapture.enter_dispatch] at entry
  obtain ⟨output, entered⟩ := entry
  let middle := call.entered output
  have frame := call.entered_frame output
  let origin := X86AllowanceCall.basisAt call.prologue.code 24 codeUpper (by decide) (call.enteredMode output)
    (call.entered_rip output)
  have placed : origin.address.toInt = base + 24 := by
    change (address call.prologue.code.toInt 24).toInt = _
    rw [X86AllowanceCall.offset_int call.prologue.code codeUpper 24 (by decide), entryAt]
    rfl
  let moved := X86Bounds.Facts.transport facts frame (by decide) (by decide) (by rw [pointerIs]; decide)
    (X86Flags.mergeFlags call.fuel.flags output) (call.entered_flags output) baseSpillApart lengthSpillApart
  let located := X86P1LoadCapture.located pointerIs regionIs moved origin (by rw [placed]; omega)
  let resultAt : X86FailureHandler.FrameFacts middle := {
    resultFacts with
    frameKnown := (frame.lookup 7 (by decide)).trans resultFacts.frameKnown
    controlsKnown := (frame.registers .ctrs (by decide)).trans resultFacts.controlsKnown
    visibleKnown := (frame.registers .seg_visibles (by decide)).trans resultFacts.visibleKnown
    flags := X86Flags.mergeFlags call.fuel.flags output
    flagsKnown := call.entered_flags output
    quiet := (frame.registers .log_register_writes (by decide)).trans resultFacts.quiet }
  have imageAt : X86P1LoadCapture.Loaded image middle base :=
    fun index within => (frame.memory _ (imageSpillApart index within)).trans (present index within)
  obtain ⟨body,flags,bodyRun,bodyRip,value,status,result,bodyFrame,known,bodyImage⟩ :=
    load_bounds_invalid (X86AllowanceCall.Inputs.exitDispatch (X86P1Sub1Fuel.handlers other)) extra vector
      middle base origin located resultAt placed imageAt imageBodyApart outside
  let exit : X86AllowanceCall.Exit call output (X86P1RefusedCapture.writes resultFacts) body := {
    frame := bodyFrame.mono (by decide) (Finset.Subset.refl _)
    remaining := call.fuel.budget - call.fuel.receipt
    remainingKnown := (bodyFrame.lookup 5 (by decide)).trans (call.entered_allowance output)
    flags := flags
    flagsKnown := known
    budgetSafe := budgetBodyApart
    bottomSafe := bottomApart
    savedSafe := savedApart
    exitSafe := by
      intro index byte bytePresent
      have bounded : index < 28 := (List.getElem?_eq_some_iff.mp bytePresent).1
      rw [X86P1RefusedCapture.exit_address base call.exit exitAt upper lower index]
      intro member
      rcases Finset.mem_union.mp member with written | receiptWord
      · exact imageBodyApart (619 + index) (by rw [X86P1LoadCapture.byte_extent]; omega) written
      · exact imageReceiptApart (619 + index) (by rw [X86P1LoadCapture.byte_extent]; omega) receiptWord
    pointer := by rw [exitAt]; exact bodyRip }
  obtain ⟨after, run, correct⟩ :=
    call.executes (X86P1RefusedCapture.callHandlers other extra) vector output
      (X86P1RefusedCapture.writes resultFacts) body (guardSteps located.length + 4) entered bodyRun exit
      (X86P1RefusedCapture.exit_dispatch other extra)
  refine ⟨body, after, run, correct, correct.value.trans value, ?_, ?_, ?_, ?_⟩
  · intro byte within
    rw [correct.tail.memory _ (statusReceiptApart byte within)]
    exact status byte within
  · intro byte within
    rw [correct.tail.memory _ (resultReceiptApart byte within)]
    exact result byte within
  · intro byte within
    have published := correct.receipt byte within
    change after.mem.get? _ = some (BitVec.extractLsb' (8 * byte) 8
      (call.fuel.budget - (call.fuel.budget - call.fuel.receipt))) at published
    rwa [X86P1RefusedCapture.restored_receipt] at published
  · intro index within
    rw [correct.tail.memory _ (imageReceiptApart index within)]
    exact bodyImage index within

namespace Controls
private noncomputable def seed := X86P1SuccessCapture.Controls.entryFixture (0#64)
private noncomputable def observed := X86P1SuccessCapture.Controls.entryObservations (0#64)
private noncomputable def before (pointer : Word) : State := put seed.state 6 pointer
private theorem changed (pointer : Word) : RegisterFrame {.rsi} seed.state (before pointer) := by
  simpa only [before,show key (6 : Fin 16) = .rsi from by decide] using put_frame seed.state 6 pointer

private noncomputable def caller (pointer : Word) : X86AllowanceCall.Inputs (before pointer) :=
  let frame := changed pointer
  { seed.caller with
    prologue := {
      seed.caller.prologue with
      stackKnown := (frame.lookup 4 (by decide)).trans seed.caller.prologue.stackKnown
      savedKnown := fun index => (frame.lookup _ (by fin_cases index <;> decide)).trans
        (seed.caller.prologue.savedKnown index)
      returnBytes := fun byte within => by rw [frame.memory]; exact seed.caller.prologue.returnBytes byte within
      visibleKnown := (frame.registers .seg_visibles (by decide)).trans seed.caller.prologue.visibleKnown
      controlsKnown := (frame.registers .ctrs (by decide)).trans seed.caller.prologue.controlsKnown
      flagsKnown := (frame.registers .rflags (by decide)).trans seed.caller.prologue.flagsKnown
      quiet := (frame.registers .log_register_writes (by decide)).trans seed.caller.prologue.quiet
      context := {
        seed.caller.prologue.context with
        status := (frame.registers .ms_reg (by decide)).trans seed.caller.prologue.context.status
        fault := (frame.registers .fault_reg (by decide)).trans seed.caller.prologue.context.fault
        msrs := (frame.registers .msrs (by decide)).trans seed.caller.prologue.context.msrs
        segments := (frame.registers .seg_hidden_attrs (by decide)).trans seed.caller.prologue.context.segments
        application := (frame.registers .app_view (by decide)).trans seed.caller.prologue.context.application }
      loaded := fun index byte present => by rw [frame.memory]; exact seed.caller.prologue.loaded index byte present
      rip := (frame.registers .rip (by decide)).trans seed.caller.prologue.rip }
    rbpKnown := (frame.lookup 5 (by decide)).trans seed.caller.rbpKnown
    entryLoaded := fun index byte present => by
      have loaded := seed.caller.entryLoaded index byte present
      rw [← frame.memory] at loaded
      exact loaded
    fuel := {
      seed.caller.fuel with
      frameKnown := (frame.lookup 7 (by decide)).trans seed.caller.fuel.frameKnown
      budgetPresent := fun index within => by rw [frame.memory]; exact seed.caller.fuel.budgetPresent index within
      receiptPresent := fun index within => by rw [frame.memory]; exact seed.caller.fuel.receiptPresent index within
      visibleKnown := (frame.registers .seg_visibles (by decide)).trans seed.caller.fuel.visibleKnown
      controlsKnown := (frame.registers .ctrs (by decide)).trans seed.caller.fuel.controlsKnown
      flagsKnown := (frame.registers .rflags (by decide)).trans seed.caller.fuel.flagsKnown
      quiet := (frame.registers .log_register_writes (by decide)).trans seed.caller.fuel.quiet }
    exitLoaded := fun index byte present => by
      have loaded := seed.caller.exitLoaded index byte present
      rw [← frame.memory] at loaded
      exact loaded }

private noncomputable def facts (pointer : Word) : X86Bounds.Facts X86P1FieldLoadCapture.layout (before pointer) :=
  let old := seed.data.premiseFacts
  let frame := changed pointer
  { old with
    pointer := pointer
    pointerKnown := lookup_put_same seed.state 6 pointer
    frameKnown := (frame.lookup 7 (by decide)).trans old.frameKnown
    controlKnown := (frame.registers .ctrs (by decide)).trans old.controlKnown
    visibleKnown := (frame.registers .seg_visibles (by decide)).trans old.visibleKnown
    flagsKnown := (frame.registers .rflags (by decide)).trans old.flagsKnown
    quiet := (frame.registers .log_register_writes (by decide)).trans old.quiet
    baseBytes := fun byte within => by rw [frame.memory]; exact old.baseBytes byte within
    lengthBytes := fun byte within => by rw [frame.memory]; exact old.lengthBytes byte within }

private noncomputable def receipt (pointer : Word) : X86FailureHandler.FrameFacts (before pointer) :=
  let frame := changed pointer
  { seed.receipt with
    frameKnown := (frame.lookup 7 (by decide)).trans seed.receipt.frameKnown
    controlsKnown := (frame.registers .ctrs (by decide)).trans seed.receipt.controlsKnown
    visibleKnown := (frame.registers .seg_visibles (by decide)).trans seed.receipt.visibleKnown
    flagsKnown := (frame.registers .rflags (by decide)).trans seed.receipt.flagsKnown
    quiet := (frame.registers .log_register_writes (by decide)).trans seed.receipt.quiet }

private theorem image (pointer : Word) : X86P1LoadCapture.Loaded image (before pointer) 4096 := by
  intro index within
  rw [(changed pointer).memory]
  have got := seed.data.loaded index within
  have base : seed.data.base = 4096 := observed.baseValue
  rw [base] at got
  exact got

private theorem fewer_writes (pointer : Word) :
    X86P1RefusedCapture.writes (receipt pointer) ⊆ X86P1SuccessCapture.writes seed.data seed.receipt :=
  Finset.subset_union_right

theorem end_pointer_unmapped : (before (12320#64)).mem.get? 12320 = none := by
  rw [(changed (12320#64)).memory]
  exact seed.endUnmapped

theorem end_pointer_returns_invalid (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := X86P1RefusedCapture.callHandlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ state after, state.mem.get? 12320 = none ∧ (X86FuelPrefix.fetches 29).run state = .ok () after ∧
      lookup after 0 = some (3#64) ∧ after.regs.get? .rip = some (0x9000#64) ∧
      lookup after 4 = some (32776#64) ∧ lookup after 5 = lookup state 5 ∧
      (∀ index : Fin 5, lookup after (X86Prologue.source index) = lookup state (X86Prologue.source index)) ∧
      after.mem.get? 8336 = some (3#8) ∧ after.mem.get? 8344 = some (3#8) ∧
      (∀ byte < 8, after.mem.get? (X86WriteWords.physicalAddress (8360#48) byte) =
        some ((0x10#64).extractLsb' (8 * byte) 8)) := by
  let : OtherOpcodeHandlers := X86P1RefusedCapture.callHandlers other extra
  let : VectorOpcodeHandlers := vector
  let pointer := 12320#64
  have entry : (caller pointer).prologue.code.toInt = 4096 := by
    have := observed.entryAt
    rwa [observed.baseValue] at this
  have exitAt : (caller pointer).exit = address 4096 619 := by
    have := observed.exitAt
    rwa [observed.baseValue] at this
  obtain ⟨body,after,run,correct,value,status,output,published,_⟩ := public_invalid other extra vector
    (before pointer) (caller pointer) 4096 entry exitAt (by decide) (image pointer) rfl rfl (facts pointer)
    (receipt pointer)
    (fun index within => by
      have apart := observed.preserved.code index within
      rw [observed.baseValue] at apart
      exact apart)
    (fun index within => by
      have apart := observed.codeApart index within
      rw [observed.baseValue] at apart
      exact apart)
    (fun index within => by
      have apart := observed.fuel.code index within
      rw [observed.baseValue] at apart
      exact apart)
    observed.preserved.premiseBase observed.preserved.premiseLength
    observed.statusReceiptApart observed.resultReceiptApart
    (fun byte within member => observed.fuel.budget byte within (fewer_writes pointer member))
    (fun byte within member => observed.fuel.bottom byte within
      (Finset.union_subset_union (fewer_writes pointer) (Finset.Subset.refl _) member))
    (fun slot byte within member => observed.fuel.saved slot byte within
      (Finset.union_subset_union (fewer_writes pointer) (Finset.Subset.refl _) member))
    (by
      change ¬ (12320#64 - (12288#64)).toNat + 4 ≤ (32#64).toNat
      decide)
  have stepCount : 8 + (guardSteps (facts pointer).length + 4) + 10 = 29 := by
    change 8 + ((if (32#64).toNat < 4 then 5 else 7) + 4) + 10 = 29
    decide
  rw [stepCount] at run
  refine ⟨before pointer,after,end_pointer_unmapped,run,value,correct.pointer,?_,
    correct.frame.lookup 5 (by decide),?_,?_,?_,published⟩
  · have point : (address (32720#48).toInt 56).signExtend 64 = (32776#64) := by decide
    exact correct.stackPointer.trans (congrArg some point)
  · intro index
    exact correct.frame.lookup (X86Prologue.source index) (by fin_cases index <;> decide)
  · have got := status 0 (by decide)
    have site : X86WriteWords.physicalAddress (receipt pointer).statusAddress 0 = 8336 := by
      change X86WriteWords.physicalAddress seed.receipt.statusAddress 0 = 8336
      rw [show seed.receipt.statusAddress = (8336#48) from
        (X86P1OutputCapture.Controls.fixture (0#64)).statusAddressValue]
      decide
    rw [site] at got
    exact got
  · have got := output 0 (by decide)
    have site : X86WriteWords.physicalAddress (receipt pointer).resultAddress 0 = 8344 := by
      change X86WriteWords.physicalAddress seed.receipt.resultAddress 0 = 8344
      rw [show seed.receipt.resultAddress = (8344#48) from
        (X86P1OutputCapture.Controls.fixture (0#64)).resultAddressValue]
      decide
    rw [site] at got
    exact got

theorem end_pointer_wrong_outcome (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (outcome : ExitStatus) (different : outcome ≠ .invalidInput) :
    letI : OtherOpcodeHandlers := X86P1RefusedCapture.callHandlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ state, ∀ after, (X86FuelPrefix.fetches 29).run state = .ok () after →
      lookup after 0 ≠ some outcome.word := by
  let : OtherOpcodeHandlers := X86P1RefusedCapture.callHandlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨state,actual,_,run,value,_⟩ := end_pointer_returns_invalid other extra vector
  refine ⟨state,?_⟩
  intro after executed wrong
  have same := X86FuelPrefix.fetches_deterministic 29 state actual after run executed
  rw [same,wrong] at value
  apply different
  apply ExitStatus.word_injective
  exact Option.some.inj value

private noncomputable def corrupted := X86WriteWords.putByte (before (12320#64)) 4692 (0#8)

theorem changed_handler_displacement : ¬ X86P1LoadCapture.Loaded X86P1InvalidCapture.image corrupted 4096 := by
  intro claimed
  have got := claimed 596 (by rw [X86P1LoadCapture.byte_extent]; omega)
  have byte := captured_bytes (6 : Fin 29)
  change X86P1InvalidCapture.image.view.read 596 = some (5#8) at byte
  have point : ((address 4096 596).signExtend 52).toNat = 4692 := by decide
  rw [byte,point] at got
  have observed : corrupted.mem.get? 4692 = some (0#8) := by simp [corrupted,X86WriteWords.putByte]
  rw [observed] at got
  contradiction

end Controls

#print axioms executes
#print axioms result_frame
#print axioms finished_pointer
#print axioms finished_status
#print axioms public_invalid
#print axioms Controls.end_pointer_returns_invalid
#print axioms Controls.end_pointer_wrong_outcome
#print axioms Controls.changed_handler_displacement
#print axioms Controls.end_pointer_unmapped
end Mettapedia.Machines.TIsa.X86P1InvalidCapture
