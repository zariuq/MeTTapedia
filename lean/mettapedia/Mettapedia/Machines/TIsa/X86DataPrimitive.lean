import Mettapedia.Machines.TIsa.X86ShiftBlock

/-!
# Word and shift components in one resource-operation library

The sum is a compilation presentation. Both components retain existing cell
actions and original native execution proofs, including partial input
readbacks and frames at every fetched prefix.
-/

set_option autoImplicit false
namespace Mettapedia.Machines.TIsa.X86DataPrimitive
open _root_.X86Registers X86RegisterRefinement X86Execution
local instance : MemoryPrimitives := X86Memory.ordinary
abbrev Instruction := Sum X86WordPrimitive.Instruction X86ShiftBlock.Instruction
abbrev physical := X86WordPrimitive.physical
noncomputable abbrev handlers := X86ShiftBlock.handlers

def effect : Instruction → Cells.Action (Fin 12)
  | .inl instruction => X86WordLibrary.effect instruction
  | .inr instruction => X86ShiftBlock.effect instruction
def bytes : Instruction → List Nat
  | .inl instruction => X86WordPrimitive.bytes instruction
  | .inr instruction => X86ShiftBlock.bytes instruction
def count : Instruction → Nat
  | .inl instruction => X86WordLibrary.count instruction
  | .inr instruction => X86ShiftBlock.count instruction
def destination (instruction : Instruction) : Fin 12 := (effect instruction).destination
def evaluate : Instruction → (Fin 12 → Word) → Word
  | .inl instruction => X86WordPrimitive.evaluate instruction
  | .inr instruction => X86ShiftBlock.evaluate instruction
def writes : Instruction → Finset Register
  | .inl instruction => X86WordPrimitive.writes instruction
  | .inr instruction => X86ShiftBlock.writes instruction

theorem computes (instruction : Instruction) (values : Fin 12 → Word) :
    (effect instruction).scalar.evaluate ((effect instruction).inputs.map values) =
      some (evaluate instruction values) := by
  cases instruction with
  | inl instruction => exact X86WordPrimitive.computes instruction values
  | inr instruction => exact X86ShiftBlock.computes instruction values

theorem writes_data (instruction : Instruction) : writes instruction ⊆ dataRegisters := by
  cases instruction with
  | inl instruction => exact X86WordPrimitive.writes_data instruction
  | inr instruction => exact X86ShiftBlock.writes_data instruction

theorem other_logical (instruction : Instruction) (register : Fin 12)
    (apart : register ≠ destination instruction) : key (physical register) ∉ writes instruction := by
  cases instruction with
  | inl instruction => exact X86WordPrimitive.other_logical instruction register apart
  | inr instruction => exact X86ShiftBlock.other_logical instruction register apart

theorem executes_with_prefix_addresses (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers)
    (instruction : Instruction) (values : Fin 12 → Word) (native : State) (origin : X86LegacyFetch.Basis native)
    (known : ∀ register ∈ (effect instruction).inputs,
      lookup native (physical register) = some (values register))
    (flags : BitVec 32) (flagsKnown : native.regs.get? .rflags = some flags)
    (quiet : native.regs.get? .log_register_writes = some false)
    (upper : origin.address.toInt + (bytes instruction).length + 3 < (2 ^ 47 : Int))
    (loaded : codeLoaded native origin.address.toInt (bytes instruction)) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after nextFlags,
      (X86FuelPrefix.fetches (count instruction)).run native = .ok () after ∧
      RegisterFrame (writes instruction) native after ∧
      lookup after (physical (destination instruction)) = some (evaluate instruction values) ∧
      after.regs.get? .rip = some ((address origin.address.toInt (bytes instruction).length).signExtend 64) ∧
      after.regs.get? .rflags = some nextFlags ∧ after.regs.get? .log_register_writes = some false ∧
      X86ControlFlags.Preserved native after ∧
      (∀ prefixCount ≤ count instruction, ∀ observed,
        (X86FuelPrefix.fetches prefixCount).run native = .ok () observed →
          RegisterFrame (writes instruction) native observed) ∧
      X86WordPrimitive.StrictPrefixesIn origin.address.toInt (bytes instruction).length (count instruction) native := by
  cases instruction with
  | inl instruction =>
    exact X86WordPrimitive.executes_with_prefix_addresses (X86Shift.linkedHandlers other) extra vector
      instruction values native origin known flags flagsKnown quiet upper loaded
  | inr instruction =>
    have sourceKnown := known instruction.source (by simp [effect,X86ShiftBlock.effect])
    exact X86ShiftBlock.executes_block_with_prefix_addresses other extra vector instruction values native origin
      sourceKnown flags flagsKnown quiet upper loaded

theorem executes (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (instruction : Instruction) (values : Fin 12 → Word) (native : State) (origin : X86LegacyFetch.Basis native)
    (known : ∀ register ∈ (effect instruction).inputs,
      lookup native (physical register) = some (values register))
    (flags : BitVec 32) (flagsKnown : native.regs.get? .rflags = some flags)
    (quiet : native.regs.get? .log_register_writes = some false)
    (upper : origin.address.toInt + (bytes instruction).length + 3 < (2 ^ 47 : Int))
    (loaded : codeLoaded native origin.address.toInt (bytes instruction)) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after nextFlags,
      (X86FuelPrefix.fetches (count instruction)).run native = .ok () after ∧
      RegisterFrame (writes instruction) native after ∧
      lookup after (physical (destination instruction)) = some (evaluate instruction values) ∧
      after.regs.get? .rip = some ((address origin.address.toInt (bytes instruction).length).signExtend 64) ∧
      after.regs.get? .rflags = some nextFlags ∧ after.regs.get? .log_register_writes = some false ∧
      X86ControlFlags.Preserved native after ∧
      ∀ prefixCount ≤ count instruction, ∀ observed,
        (X86FuelPrefix.fetches prefixCount).run native = .ok () observed →
          RegisterFrame (writes instruction) native observed := by
  obtain ⟨after,nextFlags,run,frame,value,pointer,nextKnown,nextQuiet,control,prefixes,_⟩ :=
    executes_with_prefix_addresses other extra vector instruction values native origin known flags
      flagsKnown quiet upper loaded
  exact ⟨after,nextFlags,run,frame,value,pointer,nextKnown,nextQuiet,control,prefixes⟩

#print axioms computes
#print axioms executes_with_prefix_addresses
#print axioms executes
end Mettapedia.Machines.TIsa.X86DataPrimitive
