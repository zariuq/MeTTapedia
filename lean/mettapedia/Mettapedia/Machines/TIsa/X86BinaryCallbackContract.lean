import Mettapedia.Machines.TIsa.X86CanonicalSpan
import Mettapedia.Machines.TIsa.X86BinaryCallbackBody

/-!
# Shared word-address contracts for native binary producer bodies

Actual entry observations use 64-bit input, output, stack and target words.
The shared canonical/no-wrap data contract constructs the existing Sail
body inputs, including alignment and the strict post-stack bound. Loaded
bytes, mode observations and image separation remain explicit facts.

The six fetched instructions return RAX=1, write the exact word graph,
preserve input bytes and retain the original register/memory frame. Concrete
witnesses cover every operation and arbitrary input values.

Execution starts at the 30-byte body. This theorem does not execute ENDBR64
or prove a C call site, permission model or complete cross-model simulation.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.X86BinaryCallbackContract
open _root_.X86Registers X86RegisterRefinement X86Execution X86CanonicalSpan
local instance : MemoryPrimitives := X86Memory.ordinary

abbrev Operation := X86BinaryCallbackBody.Operation
abbrev Word := BitVec 64

structure BodyFacts (state : State) (operation : Operation) (entry : SharedDataEntry)
    extends X86LegacyFetch.Basis state where
  visible : Vector (BitVec 16) 6
  controls : Vector Word 17
  flags : BitVec 32
  left : Word
  right : Word
  inputKnown : lookup state 7 = some entry.input
  outputKnown : lookup state 6 = some entry.output
  stackKnown : lookup state 4 = some entry.stack
  controlKnown : state.regs.get? .ctrs = some controls
  flagsKnown : state.regs.get? .rflags = some flags
  visibleKnown : state.regs.get? .seg_visibles = some visible
  quiet : state.regs.get? .log_register_writes = some false
  upper : address.toInt + 30 < (2 ^ 47 : Int)
  loaded : codeLoaded state address.toInt (X86BinaryCallbackBody.code operation)
  inputPresent : ∀ slot : Fin 2, ∀ byte < 8,
    state.mem.get? (physicalKey (entry.input + BitVec.ofNat 64 (8 * slot.val + byte))) =
      some ((if slot.val = 0 then left else right).extractLsb' (8 * byte) 8)
  returnPresent : ∀ byte < 8,
    state.mem.get? (physicalKey (entry.stack + BitVec.ofNat 64 byte)) =
      some (entry.target.extractLsb' (8 * byte) 8)
  codeApart : ∀ offset byte, (X86BinaryCallbackBody.code operation)[offset]? = some byte →
    ((X86Execution.address address.toInt offset).signExtend 52).toNat ∉
      X86BinaryCallbackBody.outputWrites (narrow entry.output)
  outputStackApart : ∀ write < 8, ∀ read < 8,
    entry.output + BitVec.ofNat 64 write ≠ entry.stack + BitVec.ofNat 64 read
  outputInputApart : ∀ write < 8, ∀ read < 16,
    entry.output + BitVec.ofNat 64 write ≠ entry.input + BitVec.ofNat 64 read

def BodyFacts.toInputs {state : State} {operation : Operation} {entry : SharedDataEntry}
    (facts : BodyFacts state operation entry) : X86BinaryCallbackBody.Inputs state operation where
  toBasis := facts.toBasis
  visible := facts.visible
  controls := facts.controls
  flags := facts.flags
  buffer := narrow entry.input
  left := facts.left
  right := facts.right
  bufferKnown := by
    rw [narrow_representation _ (area_base _ _ (by decide) entry.inputArea)]
    exact facts.inputKnown
  controlKnown := facts.controlKnown
  flagsKnown := facts.flagsKnown
  visibleKnown := facts.visibleKnown
  quiet := facts.quiet
  upper := facts.upper
  bufferUpper := entry.geometry.inputUpper
  aligned := entry.geometry.inputAligned
  loaded := facts.loaded
  present slot byte within := by
    rw [physicalAddress_nested entry.input 16 (8 * slot.val) byte (by decide) entry.inputArea
      (by have := slot.isLt; omega)]
    exact facts.inputPresent slot byte within
  output := narrow entry.output
  stack := narrow entry.stack
  target := narrow entry.target
  outputKnown := by
    rw [narrow_representation _ (area_base _ _ (by decide) entry.outputArea)]
    exact facts.outputKnown
  stackKnown := by
    rw [narrow_representation _ (area_base _ _ (by decide) entry.stackArea)]
    exact facts.stackKnown
  outputUpper := entry.geometry.outputUpper
  stackUpper := entry.geometry.stackUpper
  outputAligned := entry.geometry.outputAligned
  stackAligned := entry.geometry.stackAligned
  returnPresent byte within := by
    rw [← physicalKey_offset entry.stack 8 byte (by decide) entry.stackArea within,
      narrow_representation entry.target entry.targetCanonical]
    exact facts.returnPresent byte within
  codeApart := facts.codeApart
  stackApart byte within := by
    have outside := outside_output entry.output (entry.stack + BitVec.ofNat 64 byte)
      entry.outputArea (entry.stackArea.2 byte within)
      (fun write bounded => facts.outputStackApart write bounded byte within)
    rw [physicalKey_offset entry.stack 8 byte (by decide) entry.stackArea within] at outside
    exact outside

theorem executes (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (operation : Operation) (state : State) (entry : SharedDataEntry)
    (facts : BodyFacts state operation entry) :
    letI : OtherOpcodeHandlers := X86BinaryCallbackBody.handlers other
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 6).run state = .ok () after ∧
      X86StateFrame.Frame X86BinaryCallbackBody.clobbers
        (X86BinaryCallbackBody.outputWrites (narrow entry.output)) state after ∧
      lookup after 0 = some (1#64) ∧ lookup after 4 = some (entry.stack + (8#64)) ∧
      after.regs.get? .rip = some entry.target ∧
      (∀ byte < 8, after.mem.get? (physicalKey (entry.output + BitVec.ofNat 64 byte)) =
        some ((X86BinaryCallbackBody.evaluate operation facts.left facts.right).extractLsb' (8 * byte) 8)) ∧
      (∀ byte < 16, after.mem.get? (physicalKey (entry.input + BitVec.ofNat 64 byte)) =
        state.mem.get? (physicalKey (entry.input + BitVec.ofNat 64 byte))) ∧
      codeLoaded after facts.address.toInt (X86BinaryCallbackBody.code operation) := by
  let : OtherOpcodeHandlers := X86BinaryCallbackBody.handlers other
  let : VectorOpcodeHandlers := vector
  obtain ⟨after,run,frame,value,stack,target,output,code⟩ :=
    X86BinaryCallbackBody.executes other vector operation state facts.toInputs
  refine ⟨after,run,frame,value,?_,?_,?_,?_,code⟩
  · simpa only [BodyFacts.toInputs, successor_representation entry.stack 8 (by decide)
      entry.stackArea entry.nextStackCanonical] using stack
  · simpa only [BodyFacts.toInputs, narrow_representation entry.target entry.targetCanonical] using target
  · intro byte within
    rw [physicalKey_offset entry.output 8 byte (by decide) entry.outputArea within]
    exact output byte within
  · intro byte within
    apply frame.memory
    exact outside_output entry.output _ entry.outputArea (entry.inputArea.2 byte within)
      (fun write bounded => facts.outputInputApart write bounded byte within)

def BodyFacts.ofInputs {state : State} {operation : Operation} {entry : SharedDataEntry}
    (input : X86BinaryCallbackBody.Inputs state operation)
    (bufferMatch : input.buffer = narrow entry.input)
    (outputMatch : input.output = narrow entry.output)
    (stackMatch : input.stack = narrow entry.stack)
    (targetMatch : input.target = narrow entry.target)
    (stackApart : ∀ write < 8, ∀ read < 8,
      entry.output + BitVec.ofNat 64 write ≠ entry.stack + BitVec.ofNat 64 read)
    (inputApart : ∀ write < 8, ∀ read < 16,
      entry.output + BitVec.ofNat 64 write ≠ entry.input + BitVec.ofNat 64 read) :
    BodyFacts state operation entry where
  toBasis := input.toBasis
  visible := input.visible
  controls := input.controls
  flags := input.flags
  left := input.left
  right := input.right
  inputKnown := by
    rw [← narrow_representation _ (area_base _ _ (by decide) entry.inputArea), ← bufferMatch]
    exact input.bufferKnown
  outputKnown := by
    rw [← narrow_representation _ (area_base _ _ (by decide) entry.outputArea), ← outputMatch]
    exact input.outputKnown
  stackKnown := by
    rw [← narrow_representation _ (area_base _ _ (by decide) entry.stackArea), ← stackMatch]
    exact input.stackKnown
  controlKnown := input.controlKnown
  flagsKnown := input.flagsKnown
  visibleKnown := input.visibleKnown
  quiet := input.quiet
  upper := input.upper
  loaded := input.loaded
  inputPresent slot byte within := by
    rw [← physicalAddress_nested entry.input 16 (8 * slot.val) byte (by decide) entry.inputArea
      (by have := slot.isLt; omega), ← bufferMatch]
    exact input.present slot byte within
  returnPresent byte within := by
    rw [physicalKey_offset entry.stack 8 byte (by decide) entry.stackArea within, ← stackMatch]
    simpa only [targetMatch, narrow_representation entry.target entry.targetCanonical] using input.returnPresent byte within
  codeApart offset byte present := by
    rw [← outputMatch]
    exact input.codeApart offset byte present
  outputStackApart := stackApart
  outputInputApart := inputApart

namespace Controls

def entry : SharedDataEntry where
  input := 12288#64
  output := 16384#64
  stack := 32768#64
  target := 0x9000#64
  inputArea := area_low _ _ (by decide)
  outputArea := area_low _ _ (by decide)
  stackArea := area_low _ _ (by decide)
  inputAligned := by decide
  outputAligned := by decide
  stackAligned := by decide
  targetCanonical := by decide
  nextStackCanonical := by decide

theorem input_apart : ∀ write < 8, ∀ read < 16,
    entry.output + BitVec.ofNat 64 write ≠ entry.input + BitVec.ofNat 64 read := by
  intro write hw read hr
  exact Ne.symm (separated_of_order entry.input entry.output 16 8
    entry.inputArea entry.outputArea (by decide) read hr write hw)

theorem stack_apart : ∀ write < 8, ∀ read < 8,
    entry.output + BitVec.ofNat 64 write ≠ entry.stack + BitVec.ofNat 64 read :=
  separated_of_order entry.output entry.stack 8 8 entry.outputArea entry.stackArea (by decide)

theorem inhabited (operation : Operation) (left right : Word) :
    ∃ (state : State) (facts : BodyFacts state operation entry), facts.left = left ∧ facts.right = right := by
  obtain ⟨state,input,buffer,output,stack,target,leftKnown,rightKnown⟩ :=
    X86BinaryCallbackBody.Controls.input_witness operation left right
  let facts := BodyFacts.ofInputs (entry := entry) input buffer output stack target stack_apart input_apart
  exact ⟨state,facts,leftKnown,rightKnown⟩

theorem all_operations (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (operation : Operation) (left right : Word) :
    letI : OtherOpcodeHandlers := X86BinaryCallbackBody.handlers other
    letI : VectorOpcodeHandlers := vector
    ∃ state after, (X86FuelPrefix.fetches 6).run state = .ok () after ∧
      lookup after 0 = some (1#64) ∧ lookup after 4 = some (32776#64) ∧
      after.regs.get? .rip = some (0x9000#64) ∧
      (∀ byte < 8, after.mem.get? (physicalKey (entry.output + BitVec.ofNat 64 byte)) =
        some ((X86BinaryCallbackBody.evaluate operation left right).extractLsb' (8 * byte) 8)) ∧
      (∀ byte < 16, after.mem.get? (physicalKey (entry.input + BitVec.ofNat 64 byte)) =
        state.mem.get? (physicalKey (entry.input + BitVec.ofNat 64 byte))) := by
  obtain ⟨state,facts,leftKnown,rightKnown⟩ := inhabited operation left right
  obtain ⟨after,run,_,value,stack,target,output,preserved,_⟩ := executes other vector operation state entry facts
  exact ⟨state,after,run,value,stack,target,by simpa only [leftKnown,rightKnown] using output,preserved⟩

end Controls

#print axioms BodyFacts.toInputs
#print axioms executes
#print axioms Controls.inhabited
#print axioms Controls.all_operations

end Mettapedia.Machines.TIsa.X86BinaryCallbackContract
