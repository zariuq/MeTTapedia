import Mettapedia.Machines.TIsa.X86WordLibrary
import Mettapedia.Machines.TIsa.X86BranchGraph

/-!
# Captured word operations with partial input readbacks

MOV and ADD/SUB retain the established source actions and original native
traces. Only actual input registers need initial readbacks; an overwritten
destination may be absent from the native initialized set. The precise frame
retains every other logical register, the whole image and architectural mode.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.X86WordPrimitive
open _root_.X86Registers X86RegisterRefinement X86Execution
local instance : MemoryPrimitives := X86Memory.ordinary
abbrev Instruction := X86WordLibrary.Instruction
abbrev physical := X86BinCapture.physical

def bytes : Instruction → List Nat
  | .copy instruction => X86MovCapture.expected (Registers.logicalSlot instruction.destination) (Registers.logicalSlot instruction.source)
  | .binary operation destination left right _ => X86BinCapture.expected (X86BinCapture.decodeOperation operation.val) destination left right

theorem captured_bytes (instruction : Instruction) : bytes instruction = X86WordLibrary.bytes instruction := by
  cases instruction with
  | copy instruction => exact (X86CopyBlock.emit_exact instruction).symm
  | binary operation destination left right unlocked => exact (X86WordLibrary.binaryBytes_exact operation destination left right).symm

def destination (instruction : Instruction) : Fin 12 := (X86WordLibrary.effect instruction).destination
def evaluate : Instruction → (Fin 12 → Word) → Word
  | .copy instruction, values => values instruction.source
  | .binary operation _ left right _, values => X86Arithmetic.result (X86BinCapture.decodeOperation operation.val) (values left) (values right)

theorem computes (instruction : Instruction) (values : Fin 12 → Word) :
    (X86WordLibrary.effect instruction).scalar.evaluate ((X86WordLibrary.effect instruction).inputs.map values) =
      some (evaluate instruction values) := by
  cases instruction with
  | copy instruction => rfl
  | binary operation destination left right unlocked => exact X86BinBlock.source_computes _ values left right destination

def writes (instruction : Instruction) : Finset Register := X86BinBlock.clobbers (destination instruction)
theorem writes_data (instruction : Instruction) : writes instruction ⊆ dataRegisters := X86BinBlock.clobbers_data _
theorem other_logical : ∀ instruction : Instruction, ∀ register : Fin 12,
    register ≠ destination instruction → key (physical register) ∉ writes instruction := by
  intro instruction register
  change register ≠ destination instruction → key (physical register) ∉ X86BinBlock.clobbers (destination instruction)
  generalize destination instruction = target
  revert register target
  decide

theorem physical_copy (register : Fin 12) : physical register = X86CopyBlock.physical register := by
  revert register
  decide

theorem handlers_agree (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) :
    X86Arithmetic.linkedHandlers (X86EscapeFetch.linked other extra) = X86BranchGate.handlers other extra := rfl

theorem zero_prefixes [OtherOpcodeHandlers] [VectorOpcodeHandlers]
    (native : State) (registers : Finset Register) :
    ∀ count ≤ 0, ∀ observed, (X86FuelPrefix.fetches count).run native = .ok () observed →
      RegisterFrame registers native observed := by
  intro count within observed run
  have zero : count = 0 := by omega
  subst count
  have same := X86FuelPrefix.fetches_deterministic 0 native native observed (X86FuelPrefix.fetches_zero native) run
  subst observed
  exact RegisterFrame.refl _ _

theorem one_prefixes [OtherOpcodeHandlers] [VectorOpcodeHandlers]
    (native after : State) (registers : Finset Register)
    (run : (X86FuelPrefix.fetches 1).run native = .ok () after) (frame : RegisterFrame registers native after) :
    ∀ count ≤ 1, ∀ observed, (X86FuelPrefix.fetches count).run native = .ok () observed →
      RegisterFrame registers native observed := by
  intro count within observed candidate
  interval_cases count
  · exact zero_prefixes native registers 0 (by omega) observed candidate
  · have same := X86FuelPrefix.fetches_deterministic 1 native after observed run candidate
    subst observed
    exact frame

/-- Before the last fetch of a template, the instruction pointer is within
that template's byte range. -/
def StrictPrefixesIn [OtherOpcodeHandlers] [VectorOpcodeHandlers]
    (base : Int) (width count : Nat) (native : State) : Prop :=
  ∀ prefixCount < count, ∀ observed, (X86FuelPrefix.fetches prefixCount).run native = .ok () observed →
    ∃ offset < width, observed.regs.get? .rip = some ((address base offset).signExtend 64)

theorem strictPrefixes_one [OtherOpcodeHandlers] [VectorOpcodeHandlers]
    (base : Int) (width : Nat) (native : State) (nonempty : 0 < width)
    (pointer : native.regs.get? .rip = some ((address base 0).signExtend 64)) :
    StrictPrefixesIn base width 1 native := by
  intro prefixCount shorter observed run
  have zero : prefixCount = 0 := by omega
  subst prefixCount
  have same := X86FuelPrefix.fetches_deterministic 0 native native observed
    (X86FuelPrefix.fetches_zero native) run
  subst observed
  exact ⟨0,nonempty,pointer⟩

theorem executes_with_prefix_addresses (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers)
    (instruction : Instruction) (values : Fin 12 → Word) (native : State) (origin : X86LegacyFetch.Basis native)
    (known : ∀ register ∈ (X86WordLibrary.effect instruction).inputs,
      X86RegisterRefinement.lookup native (physical register) = some (values register))
    (flags : BitVec 32) (flagsKnown : native.regs.get? .rflags = some flags)
    (quiet : native.regs.get? .log_register_writes = some false)
    (upper : origin.address.toInt + (bytes instruction).length + 3 < (2 ^ 47 : Int))
    (loaded : codeLoaded native origin.address.toInt (bytes instruction)) :
    letI : OtherOpcodeHandlers := X86BranchGate.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after nextFlags,
      (X86FuelPrefix.fetches (X86WordLibrary.count instruction)).run native = .ok () after ∧
      RegisterFrame (writes instruction) native after ∧
      X86RegisterRefinement.lookup after (physical (destination instruction)) = some (evaluate instruction values) ∧
      after.regs.get? .rip = some ((address origin.address.toInt (bytes instruction).length).signExtend 64) ∧
      after.regs.get? .rflags = some nextFlags ∧
      after.regs.get? .log_register_writes = some false ∧ X86ControlFlags.Preserved native after ∧
      (∀ count ≤ X86WordLibrary.count instruction, ∀ observed,
        (X86FuelPrefix.fetches count).run native = .ok () observed → RegisterFrame (writes instruction) native observed) ∧
      StrictPrefixesIn origin.address.toInt (bytes instruction).length (X86WordLibrary.count instruction) native := by
  let : OtherOpcodeHandlers := X86BranchGate.handlers other extra
  let : VectorOpcodeHandlers := vector
  cases instruction with
  | copy instruction =>
    have sourceKnown := known instruction.source (by simp [X86WordLibrary.effect,X86CopyBlock.Copy.effect,X86ResourceCopy.copyAction])
    by_cases same : instruction.destination = instruction.source
    · have empty : bytes (.copy instruction) = [] := (captured_bytes _).trans (X86CopyBlock.emit_self instruction same)
      have count : X86WordLibrary.count (.copy instruction) = 0 := by simp [X86WordLibrary.count,same]
      refine ⟨native,flags,?_,RegisterFrame.refl _ _,?_,?_,flagsKnown,quiet,X86ControlFlags.Preserved.refl native,?_,?_⟩
      · rw [count]; exact X86FuelPrefix.fetches_zero native
      · simpa only [destination,X86WordLibrary.effect,X86CopyBlock.Copy.effect,X86ResourceCopy.copyAction,same,evaluate] using sourceKnown
      · rw [empty]; simpa [address] using origin.rip
      · rw [count]; exact zero_prefixes native _
      · rw [count]; intro prefixCount shorter; omega
    · have body : bytes (.copy instruction) =
          [(X86RegisterEncoding.rex true (physical instruction.source) (physical instruction.destination)).toNat,
            0x89,(X86RegisterEncoding.modRM (physical instruction.source) (physical instruction.destination)).toNat] := by
        rw [captured_bytes]
        change X86CopyBlock.emit instruction = _
        simpa only [physical_copy] using X86CopyBlock.emit_distinct instruction same
      have length : (bytes (.copy instruction)).length = 3 := by rw [body]; rfl
      let window := windowAt native native origin (RegisterFrame.refl dataRegisters native)
        (extent := (bytes (.copy instruction)).length + 3)
        (by simpa only [Nat.cast_add,Nat.cast_ofNat,Int.add_assoc] using upper) 0 (by omega)
        (by simpa [address] using origin.rip) (bytes (.copy instruction)) loaded
        (physical instruction.source) (physical instruction.destination) (0x89#8)
        (by rw [body]; rfl) (by rw [body]; rfl) (by rw [body]; rfl)
      let after := X86Move.putPointer (put native (physical instruction.destination) (values instruction.source)) (address origin.address.toInt 3)
      have step : Step native after := X86ResourceCopy.Window.executes native _ _ window _ sourceKnown quiet
      have small := X86BinBlock.copied_local_frame native (physical instruction.destination) (values instruction.source) (address origin.address.toInt 3)
      have frame : RegisterFrame (writes (.copy instruction)) native after := small.mono (by
        intro register member
        simp only [Finset.mem_insert,Finset.mem_singleton] at member
        rcases member with rfl | rfl <;>
          simp [writes,destination,X86WordLibrary.effect,X86CopyBlock.Copy.effect,X86ResourceCopy.copyAction,X86BinBlock.clobbers])
      have run : (X86FuelPrefix.fetches 1).run native = .ok () after := X86FuelPrefix.fetches_one native after step
      have count : X86WordLibrary.count (.copy instruction) = 1 := by simp [X86WordLibrary.count,same]
      refine ⟨after,flags,?_,frame,?_,?_,?_,?_,?_,?_,?_⟩
      · rw [count]; exact run
      · change X86RegisterRefinement.lookup after (physical instruction.destination) = some (values instruction.source)
        dsimp only [after]
        rw [X86Move.lookup_putPointer,lookup_put_same]
      · rw [length]; exact X86BinBlock.copied_rip _ _ _ _
      · exact (small.registers .rflags (by generalize instruction.destination = target; fin_cases target <;> decide)).trans flagsKnown
      · exact (frame.registers .log_register_writes (fun member => (by decide : .log_register_writes ∉ dataRegisters) (writes_data _ member))).trans quiet
      · exact X86ControlFlags.of_register_frame small (by generalize instruction.destination = target; fin_cases target <;> decide)
      · rw [count]; exact one_prefixes native after _ run frame
      · rw [count,length]
        exact strictPrefixes_one _ _ _ (by decide) (by simpa [address] using origin.rip)
  | binary operation destination left right unlocked =>
    have leftKnown := known left (by simp [X86WordLibrary.effect,X86BinBlock.sourceAction])
    have rightKnown := known right (by simp [X86WordLibrary.effect,X86BinBlock.sourceAction])
    have length : (bytes (.binary operation destination left right unlocked)).length = 9 := rfl
    have bound : origin.address.toInt + 9 < (2 ^ 47 : Int) := by rw [length] at upper; omega
    obtain ⟨output,first,second,one,two,three,firstFrame,secondFrame,frame,firstRip,secondRip⟩ :=
      X86BinBlock.expected_trace_with_pointers (X86EscapeFetch.linked other extra) vector
        (X86BinCapture.decodeOperation operation.val)
        destination left right native origin bound loaded (values left) (values right) flags leftKnown rightKnown flagsKnown quiet
    let after := X86BinBlock.finished native origin.address.toInt (X86BinCapture.decodeOperation operation.val)
      destination (values left) (values right) flags output
    have run : (X86FuelPrefix.fetches 3).run native = .ok () after :=
      X86FuelPrefix.fetches_cons 2 native first after one
        (X86FuelPrefix.fetches_cons 1 first second after two (X86FuelPrefix.fetches_one second after three))
    have finalFlags := X86BinBlock.finished_flags native origin.address.toInt (X86BinCapture.decodeOperation operation.val)
      destination (values left) (values right) flags output
    refine ⟨after,X86Flags.mergeFlags flags output,run,frame,X86BinBlock.finished_destination _ _ _ _ _ _ _ _,
      ?_,finalFlags,?_,?_,?_,?_⟩
    · rw [length]; exact X86BinBlock.copied_rip _ _ _ _
    · exact (frame.registers .log_register_writes (fun member => (by decide : .log_register_writes ∉ dataRegisters) (X86BinBlock.clobbers_data _ member))).trans quiet
    · unfold X86ControlFlags.Preserved
      rw [finalFlags,flagsKnown]
      simp only [Option.map_some,X86ControlFlags.arithmetic_mask]
    · exact X86WordLibrary.prefix_from_three native first second after _ one two three firstFrame secondFrame frame
    · rw [length]
      intro prefixCount shorter observed candidate
      change prefixCount < 3 at shorter
      interval_cases prefixCount
      · have same := X86FuelPrefix.fetches_deterministic 0 native native observed
          (X86FuelPrefix.fetches_zero native) candidate
        subst observed
        exact ⟨0,by decide,by simpa [address] using origin.rip⟩
      · have same := X86FuelPrefix.fetches_deterministic 1 native first observed
          (X86FuelPrefix.fetches_one native first one) candidate
        subst observed
        exact ⟨3,by decide,firstRip⟩
      · have head := X86FuelPrefix.fetches_cons 1 native first second one
          (X86FuelPrefix.fetches_one first second two)
        have same := X86FuelPrefix.fetches_deterministic 2 native second observed head candidate
        subst observed
        exact ⟨6,by decide,secondRip⟩

theorem executes (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (instruction : Instruction) (values : Fin 12 → Word) (native : State) (origin : X86LegacyFetch.Basis native)
    (known : ∀ register ∈ (X86WordLibrary.effect instruction).inputs,
      X86RegisterRefinement.lookup native (physical register) = some (values register))
    (flags : BitVec 32) (flagsKnown : native.regs.get? .rflags = some flags)
    (quiet : native.regs.get? .log_register_writes = some false)
    (upper : origin.address.toInt + (bytes instruction).length + 3 < (2 ^ 47 : Int))
    (loaded : codeLoaded native origin.address.toInt (bytes instruction)) :
    letI : OtherOpcodeHandlers := X86BranchGate.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after nextFlags,
      (X86FuelPrefix.fetches (X86WordLibrary.count instruction)).run native = .ok () after ∧
      RegisterFrame (writes instruction) native after ∧
      X86RegisterRefinement.lookup after (physical (destination instruction)) = some (evaluate instruction values) ∧
      after.regs.get? .rip = some ((address origin.address.toInt (bytes instruction).length).signExtend 64) ∧
      after.regs.get? .rflags = some nextFlags ∧ after.regs.get? .log_register_writes = some false ∧
      X86ControlFlags.Preserved native after ∧
      ∀ count ≤ X86WordLibrary.count instruction, ∀ observed,
        (X86FuelPrefix.fetches count).run native = .ok () observed →
          RegisterFrame (writes instruction) native observed := by
  obtain ⟨after,nextFlags,run,frame,value,pointer,nextKnown,nextQuiet,control,prefixes,_⟩ :=
    executes_with_prefix_addresses other extra vector instruction values native origin known flags
      flagsKnown quiet upper loaded
  exact ⟨after,nextFlags,run,frame,value,pointer,nextKnown,nextQuiet,control,prefixes⟩

end Mettapedia.Machines.TIsa.X86WordPrimitive
