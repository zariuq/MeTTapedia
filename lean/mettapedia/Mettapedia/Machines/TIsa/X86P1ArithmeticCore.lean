import Mettapedia.Machines.TIsa.X86ArithmeticWord
import Mettapedia.Machines.TIsa.X86PrefixComposition

/-!
# Aliasing-directed p1 ADD/SUB templates

In-place operations use one instruction. A distinct destination is initialized
before the arithmetic instruction. Right-aliased subtraction retains the
captured three-instruction scratch path. Source operands alone need readbacks.
-/

set_option autoImplicit false
namespace Mettapedia.Machines.TIsa.X86P1ArithmeticCore
open _root_.X86Registers X86RegisterRefinement X86RegisterEncoding X86Execution X86FetchEntry
local instance : MemoryPrimitives := X86Memory.ordinary
abbrev physical := X86WordPrimitive.physical

structure Instruction where
  operation : X86Arithmetic.DefinedOperation
  destination : Fin 12
  left : Fin 12
  right : Fin 12
  unlocked : destination ≠ 0

theorem physical_copy (register : Fin 12) : physical register = X86CopyBlock.physical register :=
  X86WordPrimitive.physical_copy register

def copy (instruction : Instruction) : X86CopyBlock.Copy :=
  ⟨instruction.left,instruction.destination,instruction.unlocked⟩
def copyBytes (instruction : Instruction) : List Nat :=
  [(rex true (physical instruction.left) (physical instruction.destination)).toNat,0x89,
    (modRM (physical instruction.left) (physical instruction.destination)).toNat]
def scratchBytes (instruction : Instruction) : List Nat :=
  X86WordPrimitive.bytes (.binary 1 instruction.destination instruction.left instruction.right instruction.unlocked)

def bytes (instruction : Instruction) : List Nat :=
  if instruction.destination = instruction.left then
    X86ArithmeticWord.bytes instruction.operation (physical instruction.right) (physical instruction.destination)
  else if instruction.destination = instruction.right then
    match instruction.operation with
    | .add => X86ArithmeticWord.bytes .add (physical instruction.left) (physical instruction.destination)
    | .sub => scratchBytes instruction
  else copyBytes instruction ++
    X86ArithmeticWord.bytes instruction.operation (physical instruction.right) (physical instruction.destination)

def count (instruction : Instruction) : Nat :=
  if instruction.destination = instruction.left then 1
  else if instruction.destination = instruction.right then
    match instruction.operation with | .add => 1 | .sub => 3
  else 2

def evaluate (instruction : Instruction) (values : Fin 12 → Word) : Word :=
  X86Arithmetic.result instruction.operation (values instruction.left) (values instruction.right)
def writes (instruction : Instruction) : Finset Register := X86BinBlock.clobbers instruction.destination

noncomputable abbrev handlers (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) : OtherOpcodeHandlers :=
  X86BranchGate.handlers other extra

theorem arithmetic_installed (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) :
    X86Arithmetic.linkedHandlers (handlers other extra) = handlers other extra := rfl

theorem writes_data (instruction : Instruction) : writes instruction ⊆ dataRegisters :=
  X86BinBlock.clobbers_data _

theorem byte_length (instruction : Instruction) : (bytes instruction).length = 3 * count instruction := by
  unfold bytes count
  split
  · rfl
  · split
    · cases instruction.operation <;> rfl
    · rfl

theorem count_bounds (instruction : Instruction) : 1 ≤ count instruction ∧ count instruction ≤ 3 := by
  unfold count
  split
  · decide
  · split
    · cases instruction.operation <;> decide
    · decide

private theorem inplace (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (instruction : Instruction) (values : Fin 12 → Word) (native : State) (origin : X86LegacyFetch.Basis native)
    (operand : Fin 12) (left right : Word)
    (codeShape : bytes instruction = X86ArithmeticWord.bytes instruction.operation
      (physical operand) (physical instruction.destination)) (countShape : count instruction = 1)
    (computed : X86Arithmetic.result instruction.operation left right = evaluate instruction values)
    (leftKnown : lookup native (physical instruction.destination) = some left)
    (rightKnown : lookup native (physical operand) = some right)
    (flags : BitVec 32) (flagsKnown : native.regs.get? .rflags = some flags)
    (quiet : native.regs.get? .log_register_writes = some false)
    (upper : origin.address.toInt + (bytes instruction).length + 3 < (2 ^ 47 : Int))
    (loaded : codeLoaded native origin.address.toInt (bytes instruction)) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after nextFlags, (X86FuelPrefix.fetches (count instruction)).run native = .ok () after ∧
      RegisterFrame (writes instruction) native after ∧
      lookup after (physical instruction.destination) = some (evaluate instruction values) ∧
      after.regs.get? .rip = some ((address origin.address.toInt (bytes instruction).length).signExtend 64) ∧
      after.regs.get? .rflags = some nextFlags ∧ after.regs.get? .log_register_writes = some false ∧
      X86ControlFlags.Preserved native after ∧
      ∀ prefixCount ≤ count instruction, ∀ observed,
        (X86FuelPrefix.fetches prefixCount).run native = .ok () observed → RegisterFrame (writes instruction) native observed := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  have size : (bytes instruction).length = 3 := by rw [byte_length,countShape]
  have actualLoaded : codeLoaded native origin.address.toInt
      (X86ArithmeticWord.bytes instruction.operation (physical operand) (physical instruction.destination)) := by
    rw [←codeShape]
    exact loaded
  have proof := X86ArithmeticWord.executes (handlers other extra) vector instruction.operation native
    (physical operand) (physical instruction.destination) left right flags (Entry.ofBasis origin)
    leftKnown rightKnown flagsKnown quiet (by change origin.address.toInt + 3 < _; rw [size] at upper; omega) actualLoaded
  rw [arithmetic_installed] at proof
  obtain ⟨after,nextFlags,run,frame,result,rip,nextKnown,nextQuiet,control,prefixes⟩ := proof
  have included : X86ArithmeticWord.writes (physical instruction.destination) ⊆ writes instruction := by
    intro register member
    simp only [X86ArithmeticWord.writes,Finset.mem_insert,Finset.mem_singleton] at member
    simp only [writes,X86BinBlock.clobbers,Finset.mem_insert,Finset.mem_singleton]
    exact Or.inr member
  refine ⟨after,nextFlags,?_,frame.mono included,?_,?_,nextKnown,nextQuiet,control,?_⟩
  · rw [countShape];exact run
  · rw [computed] at result;exact result
  · rw [size];exact rip
  · intro prefixCount within observed candidate
    rw [countShape] at within
    exact (prefixes prefixCount within observed candidate).mono included

private theorem scratch (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (instruction : Instruction) (values : Fin 12 → Word) (native : State) (origin : X86LegacyFetch.Basis native)
    (selected : instruction.operation = .sub)
    (codeShape : bytes instruction = scratchBytes instruction) (countShape : count instruction = 3)
    (leftKnown : lookup native (physical instruction.left) = some (values instruction.left))
    (rightKnown : lookup native (physical instruction.right) = some (values instruction.right))
    (flags : BitVec 32) (flagsKnown : native.regs.get? .rflags = some flags)
    (quiet : native.regs.get? .log_register_writes = some false)
    (upper : origin.address.toInt + (bytes instruction).length + 3 < (2 ^ 47 : Int))
    (loaded : codeLoaded native origin.address.toInt (bytes instruction)) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after nextFlags, (X86FuelPrefix.fetches (count instruction)).run native = .ok () after ∧
      RegisterFrame (writes instruction) native after ∧
      lookup after (physical instruction.destination) = some (evaluate instruction values) ∧
      after.regs.get? .rip = some ((address origin.address.toInt (bytes instruction).length).signExtend 64) ∧
      after.regs.get? .rflags = some nextFlags ∧ after.regs.get? .log_register_writes = some false ∧
      X86ControlFlags.Preserved native after ∧
      ∀ prefixCount ≤ count instruction, ∀ observed,
        (X86FuelPrefix.fetches prefixCount).run native = .ok () observed → RegisterFrame (writes instruction) native observed := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  have known : ∀ register ∈ (X86WordLibrary.effect
      (.binary 1 instruction.destination instruction.left instruction.right instruction.unlocked)).inputs,
      lookup native (physical register) = some (values register) := by
    intro register member
    simp only [X86WordLibrary.effect,X86BinBlock.sourceAction,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · exact leftKnown
    · exact rightKnown
  have bound : origin.address.toInt + (scratchBytes instruction).length + 3 < (2 ^ 47 : Int) := by
    rwa [codeShape] at upper
  have present : codeLoaded native origin.address.toInt (scratchBytes instruction) := by rwa [codeShape] at loaded
  obtain ⟨after,nextFlags,run,frame,result,rip,nextKnown,nextQuiet,control,prefixes⟩ :=
    X86WordPrimitive.executes other extra vector
      (.binary 1 instruction.destination instruction.left instruction.right instruction.unlocked)
      values native origin known flags flagsKnown quiet bound present
  have computed : X86WordPrimitive.evaluate
      (.binary 1 instruction.destination instruction.left instruction.right instruction.unlocked) values =
        evaluate instruction values := by simp [X86WordPrimitive.evaluate,evaluate,selected,X86BinCapture.decodeOperation]
  refine ⟨after,nextFlags,?_,frame,?_,?_,nextKnown,nextQuiet,control,?_⟩
  · rw [countShape];exact run
  · rw [computed] at result;exact result
  · rw [codeShape];exact rip
  · intro prefixCount within observed candidate
    rw [countShape] at within
    exact prefixes prefixCount within observed candidate

private theorem copy_then (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (instruction : Instruction) (values : Fin 12 → Word) (native : State) (origin : X86LegacyFetch.Basis native)
    (notLeft : instruction.destination ≠ instruction.left) (notRight : instruction.destination ≠ instruction.right)
    (codeShape : bytes instruction = copyBytes instruction ++ X86ArithmeticWord.bytes instruction.operation
      (physical instruction.right) (physical instruction.destination)) (countShape : count instruction = 2)
    (leftKnown : lookup native (physical instruction.left) = some (values instruction.left))
    (rightKnown : lookup native (physical instruction.right) = some (values instruction.right))
    (flags : BitVec 32) (flagsKnown : native.regs.get? .rflags = some flags)
    (quiet : native.regs.get? .log_register_writes = some false)
    (upper : origin.address.toInt + (bytes instruction).length + 3 < (2 ^ 47 : Int))
    (loaded : codeLoaded native origin.address.toInt (bytes instruction)) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after nextFlags, (X86FuelPrefix.fetches (count instruction)).run native = .ok () after ∧
      RegisterFrame (writes instruction) native after ∧
      lookup after (physical instruction.destination) = some (evaluate instruction values) ∧
      after.regs.get? .rip = some ((address origin.address.toInt (bytes instruction).length).signExtend 64) ∧
      after.regs.get? .rflags = some nextFlags ∧ after.regs.get? .log_register_writes = some false ∧
      X86ControlFlags.Preserved native after ∧
      ∀ prefixCount ≤ count instruction, ∀ observed,
        (X86FuelPrefix.fetches prefixCount).run native = .ok () observed → RegisterFrame (writes instruction) native observed := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  have size : (bytes instruction).length = 6 := by rw [byte_length,countShape]
  have csize : (copyBytes instruction).length = 3 := rfl
  have code : X86WordPrimitive.bytes (.copy (copy instruction)) = copyBytes instruction := by
    rw [X86WordPrimitive.captured_bytes]
    change X86CopyBlock.emit (copy instruction) = _
    simpa only [copyBytes,copy,physical_copy] using X86CopyBlock.emit_distinct (copy instruction) notLeft
  have copyCount : X86WordLibrary.count (.copy (copy instruction)) = 1 := by
    simp [X86WordLibrary.count,copy,notLeft]
  have known : ∀ register ∈ (X86WordLibrary.effect (.copy (copy instruction))).inputs,
      lookup native (physical register) = some (values register) := by
    intro register member
    have same : register = instruction.left := by
      simpa [X86WordLibrary.effect,X86CopyBlock.Copy.effect,X86ResourceCopy.copyAction,copy] using member
    subst register
    exact leftKnown
  have total : codeLoaded native origin.address.toInt (copyBytes instruction ++
      X86ArithmeticWord.bytes instruction.operation (physical instruction.right) (physical instruction.destination)) := by
    rwa [codeShape] at loaded
  have firstLoaded := codeLoaded_left native origin.address.toInt (copyBytes instruction) _ total
  have copyLoaded : codeLoaded native origin.address.toInt (X86WordPrimitive.bytes (.copy (copy instruction))) := by
    rw [code];exact firstLoaded
  obtain ⟨copied,copyFlags,copyRun,copyFrame,copiedValue,copiedRip,copiedFlags,copiedQuiet,copiedControl,copyPrefixes⟩ :=
    X86WordPrimitive.executes other extra vector (.copy (copy instruction)) values native origin known flags flagsKnown quiet
      (by rw [code,csize];rw [size] at upper;omega) copyLoaded
  rw [copyCount] at copyRun copyPrefixes
  rw [code,csize] at copiedRip
  have copyFrame' : RegisterFrame (writes instruction) native copied := copyFrame
  have retained : lookup copied (physical instruction.right) = some (values instruction.right) :=
    (copyFrame.lookup (physical instruction.right)
      (X86WordPrimitive.other_logical (.copy (copy instruction)) instruction.right (Ne.symm notRight))).trans rightKnown
  let entry := (Entry.ofBasis origin).transport (X86StateFrame.registerOnly copyFrame')
    (writes_data instruction) (address origin.address.toInt 3) copiedRip
  have lower : -(2 ^ 47 : Int) ≤ origin.address.toInt := by simpa using BitVec.le_toInt origin.address
  have fullUpper : origin.address.toInt + 6 < (2 ^ 47 : Int) := by rw [size] at upper;omega
  have position : entry.address.toInt = origin.address.toInt + 3 :=
    address_toInt _ lower fullUpper 3 (by decide : 3 ≤ 6)
  have copiedTotal := copyFrame'.code_preserved origin.address.toInt _ total
  have suffixRead := codeLoaded_right copied origin.address.toInt (copyBytes instruction)
    (X86ArithmeticWord.bytes instruction.operation (physical instruction.right) (physical instruction.destination)) copiedTotal
  have secondLoaded : codeLoaded copied entry.address.toInt
      (X86ArithmeticWord.bytes instruction.operation (physical instruction.right) (physical instruction.destination)) := by
    simpa [position,csize] using suffixRead
  have second := X86ArithmeticWord.executes (handlers other extra) vector instruction.operation copied
    (physical instruction.right) (physical instruction.destination) (values instruction.left) (values instruction.right)
    copyFlags entry copiedValue retained copiedFlags copiedQuiet (by rw [position];omega) secondLoaded
  rw [arithmetic_installed] at second
  obtain ⟨after,nextFlags,lastRun,lastFrame,result,rip,nextKnown,nextQuiet,control,lastPrefixes⟩ := second
  have included : X86ArithmeticWord.writes (physical instruction.destination) ⊆ writes instruction := by
    intro register member
    simp only [X86ArithmeticWord.writes,Finset.mem_insert,Finset.mem_singleton] at member
    simp only [writes,X86BinBlock.clobbers,Finset.mem_insert,Finset.mem_singleton]
    exact Or.inr member
  have frame : RegisterFrame (writes instruction) native after := by
    simpa only [Finset.union_self] using copyFrame'.trans (lastFrame.mono included)
  have endpoint : address entry.address.toInt 3 = address origin.address.toInt (bytes instruction).length := by
    rw [position,size]
    simp [address,Int.add_assoc]
  have whole := X86FuelPrefix.fetches_then 1 1 native copied after copyRun lastRun
  refine ⟨after,nextFlags,?_,frame,result,?_,nextKnown,nextQuiet,copiedControl.trans control,?_⟩
  · rw [countShape];exact whole
  · rw [endpoint] at rip;exact rip
  · intro prefixCount within observed candidate
    rw [countShape] at within
    exact X86PrefixComposition.append (writes instruction) 1 1 native copied copyRun copyFrame'
      copyPrefixes (fun c h reached run => (lastPrefixes c h reached run).mono included)
      prefixCount within observed candidate

theorem executes (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (instruction : Instruction) (values : Fin 12 → Word) (native : State) (origin : X86LegacyFetch.Basis native)
    (leftKnown : lookup native (physical instruction.left) = some (values instruction.left))
    (rightKnown : lookup native (physical instruction.right) = some (values instruction.right))
    (flags : BitVec 32) (flagsKnown : native.regs.get? .rflags = some flags)
    (quiet : native.regs.get? .log_register_writes = some false)
    (upper : origin.address.toInt + (bytes instruction).length + 3 < (2 ^ 47 : Int))
    (loaded : codeLoaded native origin.address.toInt (bytes instruction)) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after nextFlags, (X86FuelPrefix.fetches (count instruction)).run native = .ok () after ∧
      RegisterFrame (writes instruction) native after ∧
      lookup after (physical instruction.destination) = some (evaluate instruction values) ∧
      after.regs.get? .rip = some ((address origin.address.toInt (bytes instruction).length).signExtend 64) ∧
      after.regs.get? .rflags = some nextFlags ∧ after.regs.get? .log_register_writes = some false ∧
      X86ControlFlags.Preserved native after ∧
      ∀ prefixCount ≤ count instruction, ∀ observed,
        (X86FuelPrefix.fetches prefixCount).run native = .ok () observed → RegisterFrame (writes instruction) native observed := by
  by_cases sameLeft : instruction.destination = instruction.left
  · exact inplace other extra vector instruction values native origin instruction.right
      (values instruction.left) (values instruction.right)
      (by simp only [bytes,if_pos sameLeft]) (by simp only [count,if_pos sameLeft]) rfl
      (by rw [sameLeft];exact leftKnown) rightKnown flags flagsKnown quiet upper loaded
  · by_cases sameRight : instruction.destination = instruction.right
    · cases selected : instruction.operation with
      | add =>
        apply inplace other extra vector instruction values native origin instruction.left
          (values instruction.right) (values instruction.left)
          (by simp only [bytes,if_neg sameLeft,if_pos sameRight,selected])
          (by simp only [count,if_neg sameLeft,if_pos sameRight,selected])
          ?_ (by rw [sameRight];exact rightKnown) leftKnown flags flagsKnown quiet upper loaded
        simp only [evaluate,selected,X86Arithmetic.result,BitVec.add_comm]
      | sub =>
        exact scratch other extra vector instruction values native origin selected
          (by simp only [bytes,if_neg sameLeft,if_pos sameRight,selected])
          (by simp only [count,if_neg sameLeft,if_pos sameRight,selected])
          leftKnown rightKnown flags flagsKnown quiet upper loaded
    · exact copy_then other extra vector instruction values native origin sameLeft sameRight
        (by simp only [bytes,if_neg sameLeft,if_neg sameRight])
        (by simp only [count,if_neg sameLeft,if_neg sameRight])
        leftKnown rightKnown flags flagsKnown quiet upper loaded

#print axioms executes
#print axioms inplace
#print axioms scratch
end Mettapedia.Machines.TIsa.X86P1ArithmeticCore
