import Mettapedia.Machines.TIsa.X86P1ArithmeticCore
import Mettapedia.Machines.TIsa.X86Normalize32
import Mettapedia.Machines.TIsa.P1Scalar

/-!
# Complete p1 ADD/SUB templates with typed carrier normalization

Aliasing selects the actual core template. U32Z and I32S append their proved
normalizers; U64 keeps the core result. The source operation remains the
existing P1Scalar recipe, with protected-frame and supported-tag checks.
-/

set_option autoImplicit false
namespace Mettapedia.Machines.TIsa.X86P1Arithmetic
open _root_.X86Registers X86RegisterRefinement X86RegisterEncoding X86Execution X86FetchEntry
local instance : MemoryPrimitives := X86Memory.ordinary
abbrev physical := X86P1ArithmeticCore.physical

def Supported (tag : P1Source.TypeTag) : Prop := tag = .u64 ∨ tag = .u32z ∨ tag = .i32s
instance (tag : P1Source.TypeTag) : Decidable (Supported tag) :=
  inferInstanceAs (Decidable (tag = .u64 ∨ tag = .u32z ∨ tag = .i32s))

structure Instruction where
  core : X86P1ArithmeticCore.Instruction
  tag : P1Source.TypeTag
  supported : Supported tag

def normalization : P1Source.TypeTag → Option Bool
  | .u32z => some false | .i32s => some true | _ => none

def normalBytes (instruction : Instruction) : List Nat :=
  match normalization instruction.tag with
  | none => []
  | some signed => X86Normalize32.bytes signed (physical instruction.core.destination)

def normalCount (instruction : Instruction) : Nat := if (normalization instruction.tag).isSome then 1 else 0

def bytes (instruction : Instruction) : List Nat := X86P1ArithmeticCore.bytes instruction.core ++ normalBytes instruction
def count (instruction : Instruction) : Nat := X86P1ArithmeticCore.count instruction.core + normalCount instruction
def writes (instruction : Instruction) : Finset Register := X86P1ArithmeticCore.writes instruction.core

def evaluate (instruction : Instruction) (values : Fin 12 → Word) : Word :=
  P1Scalar.normalize instruction.tag (X86P1ArithmeticCore.evaluate instruction.core values)

def p1 (instruction : Instruction) : P1Source.Instr :=
  .binary (X86ResourceBinary.binary instruction.core.operation) instruction.tag
    instruction.core.destination instruction.core.left instruction.core.right

def effect (instruction : Instruction) : CellEffects.Recipe (Fin 12) :=
  P1Scalar.recipe (p1 instruction) instruction.core.destination

def lower? : P1Source.Instr → Option Instruction
  | .binary .add tag destination left right =>
      if valid : Supported tag ∧ destination ≠ 0 then
        some ⟨⟨.add,destination,left,right,valid.2⟩,tag,valid.1⟩ else none
  | .binary .sub tag destination left right =>
      if valid : Supported tag ∧ destination ≠ 0 then
        some ⟨⟨.sub,destination,left,right,valid.2⟩,tag,valid.1⟩ else none
  | _ => none

theorem lower?_roundtrip (instruction : Instruction) : lower? (p1 instruction) = some instruction := by
  rcases instruction with ⟨⟨operation,destination,left,right,unlocked⟩,tag,supported⟩
  cases operation <;> simp [lower?,p1,X86ResourceBinary.binary,supported,unlocked]

theorem lower?_source {source : P1Source.Instr} {instruction : Instruction}
    (accepted : lower? source = some instruction) : p1 instruction = source := by
  cases source <;> simp only [lower?] at accepted <;> try contradiction
  split at accepted
  · split at accepted
    · cases accepted
      symm
      assumption
    · cases accepted
  · split at accepted
    · cases accepted
      symm
      assumption
    · cases accepted
  · cases accepted

theorem computes (instruction : Instruction) (values : Fin 12 → Word) :
    P1Scalar.evaluate (p1 instruction) ((p1 instruction).reads.map values) = some (evaluate instruction values) := by
  rcases instruction.supported with supported | supported | supported <;>
    cases selected : instruction.core.operation <;>
    simp [p1,P1Source.Instr.reads,P1Scalar.evaluate,P1Scalar.boolInputs,X86ResourceBinary.binary,
      evaluate,X86P1ArithmeticCore.evaluate,X86Arithmetic.result,Binary.evaluate,selected,supported]

noncomputable abbrev handlers (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) : OtherOpcodeHandlers :=
  X86Extend32.linkedHandlers (X86P1ArithmeticCore.handlers other extra)

theorem core_handlers_agree (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) :
    X86P1ArithmeticCore.handlers (X86Extend32.linkedHandlers other) extra = handlers other extra := rfl

theorem writes_data (instruction : Instruction) : writes instruction ⊆ dataRegisters :=
  X86P1ArithmeticCore.writes_data _

theorem byte_length (instruction : Instruction) : (bytes instruction).length =
    (X86P1ArithmeticCore.bytes instruction.core).length + (normalBytes instruction).length := by simp [bytes]

private theorem normalized (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (instruction : Instruction) (values : Fin 12 → Word) (native : State) (origin : X86LegacyFetch.Basis native)
    (signed : Bool)
    (normalShape : normalBytes instruction = X86Normalize32.bytes signed (physical instruction.core.destination))
    (normalCountShape : normalCount instruction = 1)
    (valueShape : ∀ value : Word, P1Scalar.normalize instruction.tag value = extend32 signed (low32 value))
    (leftKnown : lookup native (physical instruction.core.left) = some (values instruction.core.left))
    (rightKnown : lookup native (physical instruction.core.right) = some (values instruction.core.right))
    (flags : BitVec 32) (flagsKnown : native.regs.get? .rflags = some flags)
    (quiet : native.regs.get? .log_register_writes = some false)
    (upper : origin.address.toInt + (bytes instruction).length + 3 < (2 ^ 47 : Int))
    (loaded : codeLoaded native origin.address.toInt (bytes instruction)) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after nextFlags, (X86FuelPrefix.fetches (count instruction)).run native = .ok () after ∧
      RegisterFrame (writes instruction) native after ∧
      lookup after (physical instruction.core.destination) = some (evaluate instruction values) ∧
      after.regs.get? .rip = some ((address origin.address.toInt (bytes instruction).length).signExtend 64) ∧
      after.regs.get? .rflags = some nextFlags ∧ after.regs.get? .log_register_writes = some false ∧
      X86ControlFlags.Preserved native after ∧
      ∀ prefixCount ≤ count instruction, ∀ observed,
        (X86FuelPrefix.fetches prefixCount).run native = .ok () observed → RegisterFrame (writes instruction) native observed := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  have coreLoaded := codeLoaded_left native origin.address.toInt (X86P1ArithmeticCore.bytes instruction.core)
    (normalBytes instruction) loaded
  have coreUpper : origin.address.toInt + (X86P1ArithmeticCore.bytes instruction.core).length + 3 < (2 ^ 47 : Int) := by
    rw [byte_length] at upper
    omega
  have proof := X86P1ArithmeticCore.executes (X86Extend32.linkedHandlers other) extra vector instruction.core
    values native origin leftKnown rightKnown flags flagsKnown quiet coreUpper coreLoaded
  rw [core_handlers_agree] at proof
  obtain ⟨middle,middleFlags,first,firstFrame,middleValue,middleRip,middleKnown,middleQuiet,firstControl,firstPrefixes⟩ := proof
  have firstFrame' : RegisterFrame (writes instruction) native middle := firstFrame
  let entry := (Entry.ofBasis origin).transport (X86StateFrame.registerOnly firstFrame') (writes_data instruction)
    (address origin.address.toInt (X86P1ArithmeticCore.bytes instruction.core).length) middleRip
  have lower : -(2 ^ 47 : Int) ≤ origin.address.toInt := by simpa using BitVec.le_toInt origin.address
  have wholeUpper : origin.address.toInt + ((bytes instruction).length + 3 : Nat) < (2 ^ 47 : Int) := by
    simpa [Int.add_assoc] using upper
  have position : entry.address.toInt = origin.address.toInt + (X86P1ArithmeticCore.bytes instruction.core).length :=
    address_toInt _ lower wholeUpper _ (by rw [byte_length];omega)
  have complete := firstFrame'.code_preserved origin.address.toInt (bytes instruction) loaded
  have tail := codeLoaded_right middle origin.address.toInt (X86P1ArithmeticCore.bytes instruction.core)
    (normalBytes instruction) complete
  have lastLoaded : codeLoaded middle entry.address.toInt
      (X86Normalize32.bytes signed (physical instruction.core.destination)) := by
    rw [position,←normalShape]
    exact tail
  have lastUpper : entry.address.toInt + (X86Normalize32.bytes signed (physical instruction.core.destination)).length <
      (2 ^ 47 : Int) := by
    rw [position,←normalShape]
    rw [byte_length] at upper
    omega
  have last := X86Normalize32.executes (X86P1ArithmeticCore.handlers other extra) vector signed middle
    (physical instruction.core.destination) (X86P1ArithmeticCore.evaluate instruction.core values) entry
    middleValue middleQuiet lastUpper lastLoaded
  have computed : extend32 signed (low32 (X86P1ArithmeticCore.evaluate instruction.core values)) =
      evaluate instruction values := (valueShape _).symm
  have endpoint : address entry.address.toInt
      (X86Normalize32.bytes signed (physical instruction.core.destination)).length =
      address origin.address.toInt (bytes instruction).length := by
    rw [position,←normalShape,byte_length]
    simp only [address,Int.natCast_add,Int.add_assoc]
  rw [computed,endpoint] at last
  let after := X86Move.putPointer (put middle (physical instruction.core.destination) (evaluate instruction values))
    (address origin.address.toInt (bytes instruction).length)
  have lastRun : (X86FuelPrefix.fetches 1).run middle = .ok () after :=
    X86FuelPrefix.fetches_one middle after last
  have small := X86Normalize32.result_frame signed middle (physical instruction.core.destination)
    (X86P1ArithmeticCore.evaluate instruction.core values) (address origin.address.toInt (bytes instruction).length)
  rw [computed] at small
  have included : {key (physical instruction.core.destination),Register.rip} ⊆ writes instruction := by
    intro register member
    simp only [Finset.mem_insert,Finset.mem_singleton] at member
    rcases member with rfl | rfl <;> simp [writes,X86P1ArithmeticCore.writes,X86BinBlock.clobbers]
  have lastFrame : RegisterFrame (writes instruction) middle after := small.mono included
  have frame : RegisterFrame (writes instruction) native after := by
    simpa only [Finset.union_self] using firstFrame'.trans lastFrame
  have nextKnown : after.regs.get? .rflags = some middleFlags := by
    change (X86Move.putPointer (put middle (physical instruction.core.destination) (evaluate instruction values)) _).regs.get? .rflags = _
    rw [(pointer_frame _ _).registers .rflags (by decide),put_flags,middleKnown]
  have nextQuiet : after.regs.get? .log_register_writes = some false :=
    (frame.registers .log_register_writes (fun member =>
      (by decide : Register.log_register_writes ∉ dataRegisters) (writes_data instruction member))).trans quiet
  have noFlags : ∀ destination : Fin 16,
      Register.rflags ∉ ({key destination,Register.rip} : Finset Register) := by decide
  have lastControl := X86ControlFlags.of_register_frame small (noFlags _)
  have whole := X86FuelPrefix.fetches_then (X86P1ArithmeticCore.count instruction.core) 1 native middle after first lastRun
  have prefixes := X86PrefixComposition.append (writes instruction) (X86P1ArithmeticCore.count instruction.core) 1
    native middle first firstFrame' firstPrefixes (X86WordPrimitive.one_prefixes middle after _ lastRun lastFrame)
  refine ⟨after,middleFlags,?_,frame,?_,?_,nextKnown,nextQuiet,firstControl.trans lastControl,?_⟩
  · simpa only [count,normalCountShape] using whole
  · dsimp only [after]
    rw [X86Move.lookup_putPointer,lookup_put_same]
  · exact X86BinBlock.copied_rip _ _ _ _
  · simpa only [count,normalCountShape] using prefixes

theorem executes (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (instruction : Instruction) (values : Fin 12 → Word) (native : State) (origin : X86LegacyFetch.Basis native)
    (leftKnown : lookup native (physical instruction.core.left) = some (values instruction.core.left))
    (rightKnown : lookup native (physical instruction.core.right) = some (values instruction.core.right))
    (flags : BitVec 32) (flagsKnown : native.regs.get? .rflags = some flags)
    (quiet : native.regs.get? .log_register_writes = some false)
    (upper : origin.address.toInt + (bytes instruction).length + 3 < (2 ^ 47 : Int))
    (loaded : codeLoaded native origin.address.toInt (bytes instruction)) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after nextFlags, (X86FuelPrefix.fetches (count instruction)).run native = .ok () after ∧
      RegisterFrame (writes instruction) native after ∧
      lookup after (physical instruction.core.destination) = some (evaluate instruction values) ∧
      after.regs.get? .rip = some ((address origin.address.toInt (bytes instruction).length).signExtend 64) ∧
      after.regs.get? .rflags = some nextFlags ∧ after.regs.get? .log_register_writes = some false ∧
      X86ControlFlags.Preserved native after ∧
      ∀ prefixCount ≤ count instruction, ∀ observed,
        (X86FuelPrefix.fetches prefixCount).run native = .ok () observed → RegisterFrame (writes instruction) native observed := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  rcases instruction.supported with wide | unsigned | signed
  · have codeShape : bytes instruction = X86P1ArithmeticCore.bytes instruction.core := by
      simp [bytes,normalBytes,normalization,wide]
    have countShape : count instruction = X86P1ArithmeticCore.count instruction.core := by
      simp [count,normalCount,normalization,wide]
    have valueShape : evaluate instruction values = X86P1ArithmeticCore.evaluate instruction.core values := by
      simp [evaluate,P1Scalar.normalize,wide]
    have proof := X86P1ArithmeticCore.executes (X86Extend32.linkedHandlers other) extra vector instruction.core
      values native origin leftKnown rightKnown flags flagsKnown quiet
      (by rw [←codeShape];exact upper) (by rw [←codeShape];exact loaded)
    rw [core_handlers_agree] at proof
    simpa only [codeShape,countShape,valueShape,writes,physical] using proof
  · exact normalized other extra vector instruction values native origin false
      (by simp [normalBytes,normalization,unsigned]) (by simp [normalCount,normalization,unsigned])
      (by intro value;rw [unsigned];rfl) leftKnown rightKnown flags flagsKnown quiet upper loaded
  · exact normalized other extra vector instruction values native origin true
      (by simp [normalBytes,normalization,signed]) (by simp [normalCount,normalization,signed])
      (by intro value;rw [signed];rfl) leftKnown rightKnown flags flagsKnown quiet upper loaded

#print axioms executes
#print axioms lower?_roundtrip
#print axioms lower?_source
#print axioms computes
end Mettapedia.Machines.TIsa.X86P1Arithmetic
